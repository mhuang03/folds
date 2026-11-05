import Folds.Live3

/-!
# Live pairs, part 4: rotation-stable sequences and a larger proven family

`experiments/live4/PROOFS.txt`.

* `GoodL q ν π` / `Good q ν t`: `π` is a valid sequence of the `q`-strip such that
  `σ ∘ π` is valid too (`σ = sig q ν`), and `π` starts with `t`.  By live3 1.1(e) these are
  exactly the residue chains that are complete orders of all `q` classes
  (`chainOK_of_valid`, and the converse `valid_of_chainOK`).  `coReach_good`: if
  `Good q (N mod q) s`, the class of `s` has a reachable complement and co-reachable sets of
  its class strip stay co-reachable.
* Sources of `Good`: `good_table` (all non-exceptional classes, `q ≤ 12`), `good_zero`
  (`ν = 0`, every `q`), `good_nu_one` / `good_nu_neg_one` (Theorem H of live3, every odd
  `q`), and the symmetries `good_sig` (same `ν`) and `good_mirror` (`ν ↦ -ν`).
* **Block chains** (`good_comp`, live2 3.1): from `Good j e a`, `Good m c' y` and the
  existence of rotation-stable sequences of the `m`-strip for `c` and `c + 1`, a
  rotation-stable sequence of the `m j`-strip for `ν = j c + e`, starting with
  `cls j a y = (y - 1) j + a`, uniformly in `j, m`.  E.g. `good_pow_two`: for `q = 2^a` every
  class is good for every `ν`.
* `Cov2`: the closure of the base cases under all these transfers (any `q`) and the mirror;
  `Cov.cov2` (it contains `Live2.Cov`), `Cov2.coReach`, `Cov2.extends`.
-/

namespace Folds
namespace Live4

open Live2 Live3

/-! ## Rotation-stable sequences -/

/-- `π` and `sig q ν ∘ π` are both valid sequences of the `q`-strip. -/
def GoodL (q ν : Nat) (π : List Nat) : Prop :=
  IsFoldSeq q π ∧ SemiSymmetric q π ∧ SemiSymmetric q (π.map (sig q ν))

/-- Class `t` can come first (equivalently last) in a complete residue chain mod `q` for
`N ≡ ν (mod q)`. -/
def Good (q ν t : Nat) : Prop := ∃ π, GoodL q ν π ∧ π.head? = some t

theorem isFoldSeq_map_sig {q ν : Nat} (hν : ν < q) {L : List Nat} (hf : IsFoldSeq q L) :
    IsFoldSeq q (L.map (sig q ν)) := by
  have hb : ∀ t ∈ L, 1 ≤ t ∧ t ≤ q := fun t ht => (mem_range'_of_perm hf).1 ht
  refine perm_range'_of_nodup_subset ?_ ?_ (by rw [List.length_map, hf.length_eq]; simp)
  · exact nodup_map_of_injOn (nodup_of_foldSeq hf) (sig_injOn hν hb)
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy
    exact sig_mem hν (hb u hu)

/-- The last step of a complete sequence is always valid. -/
theorem semiStep_last {N m : Nat} {S : List Nat} (h : IsFoldSeq N (S ++ [m])) :
    SemiStep N S m := by
  have hnd := nodup_of_foldSeq h
  rw [semiStep_iff_balanced_append (List.nodup_append.1 hnd).1]
  exact Balanced.perm balanced_full h.symm

theorem semiSymmetric_snoc {N m : Nat} {S : List Nat} (h : IsFoldSeq N (S ++ [m]))
    (hS : SemiSymmetric N S) : SemiSymmetric N (S ++ [m]) := by
  refine semiSymmetric_append_iff.2 ⟨hS, fun k hk => ?_⟩
  have : k = 0 := by simp at hk; omega
  subst this
  simpa using semiStep_last h

/-- **Converse of `chainOK_of_valid`** (for any list of distinct classes). -/
theorem valid_of_chainOK {q ν : Nat} (hν : ν < q) {π : List Nat} (hnd : π.Nodup)
    (hb : ∀ t ∈ π, 1 ≤ t ∧ t ≤ q) (hc : ChainOK q ν π) :
    SemiSymmetric q π ∧ SemiSymmetric q (π.map (sig q ν)) := by
  constructor
  · intro i hi
    have hs := hb _ (List.getElem_mem hi)
    have hA : ∀ t ∈ π.take i, 1 ≤ t ∧ t ≤ q := fun t ht => hb t (List.mem_of_mem_take ht)
    rw [semiStep_iff_cycBal (take_nodup hnd i) hA hs]
    have c1 := (hc i hi).1
    unfold reach
    rcases Nat.le_total (π[i] - 1) (q - π[i]) with hle | hle
    · rw [min_eq_left hle]; exact c1
    · rw [min_eq_right hle, show q - π[i] = q - 1 - (π[i] - 1) by omega,
        ← cycBal_dual hA hs (by omega)]
      exact c1
  · intro i hi
    simp only [List.length_map] at hi
    rw [List.getElem_map, ← List.map_take]
    have hs := hb _ (List.getElem_mem hi)
    have hA : ∀ t ∈ π.take i, 1 ≤ t ∧ t ≤ q := fun t ht => hb t (List.mem_of_mem_take ht)
    have hndA := take_nodup hnd i
    have hndA' : ((π.take i).map (sig q ν)).Nodup := nodup_map_of_injOn hndA (sig_injOn hν hA)
    have hA' : ∀ t ∈ (π.take i).map (sig q ν), 1 ≤ t ∧ t ≤ q := by
      intro t ht
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
      exact sig_mem hν (hA u hu)
    have hsm := sig_mem hν hs
    rw [semiStep_iff_cycBal hndA' hA' hsm]
    have c2 := (hc i hi).2
    have hsig : sig q ν π[i] - 1 = (ν + q - π[i]) % q := by unfold sig; omega
    unfold reach
    rcases Nat.le_total (sig q ν π[i] - 1) (q - sig q ν π[i]) with hle | hle
    · rw [min_eq_left hle, cycBal_sig hν hA hs (by omega), hsig]; exact c2
    · rw [min_eq_right hle, show q - sig q ν π[i] = q - 1 - (sig q ν π[i] - 1) by omega,
        ← cycBal_dual hA' hsm (by omega), cycBal_sig hν hA hs (by omega), hsig]
      exact c2

theorem goodL_of_chain {q ν : Nat} (hν : ν < q) {L : List Nat} (hf : IsFoldSeq q L)
    (hc : ChainOK q ν L) : GoodL q ν L :=
  ⟨hf, valid_of_chainOK hν (nodup_of_foldSeq hf) (fun x hx => (mem_range'_of_perm hf).1 hx) hc⟩

theorem GoodL.chainOK {q ν : Nat} (hν : ν < q) {L : List Nat} (h : GoodL q ν L) :
    ChainOK q ν L := chainOK_of_valid hν h.1 h.2.1 h.2.2

theorem GoodL.reverse {q ν : Nat} (hν : ν < q) {L : List Nat} (h : GoodL q ν L) :
    GoodL q ν L.reverse :=
  ⟨(List.reverse_perm _).trans h.1, h.2.1.reverse h.1,
    by rw [List.map_reverse]; exact h.2.2.reverse (isFoldSeq_map_sig hν h.1)⟩

theorem good_of_last {q ν t : Nat} (hν : ν < q) {L : List Nat} (h : GoodL q ν L)
    (hl : L.reverse.head? = some t) : Good q ν t := ⟨L.reverse, h.reverse hν, hl⟩

/-- **Residue transfer through a good class.** -/
theorem coReach_good {q N s : Nat} (hq : 0 < q) (hqN : q ≤ N) (hg : Good q (N % q) s)
    {D : Finset Nat} (hDs : D ⊆ Finset.Icc 1 (ccount q s N))
    (hD : CoReach (ccount q s N) D) : CoReach N (D.image (cls q s)) := by
  obtain ⟨π, hπ, hh⟩ := hg
  have hν := Nat.mod_lt N hq
  have hr := hπ.reverse hν
  exact coReach_of_chain_last hq hqN hr.1 (hr.chainOK hν) (by simpa using hh) hDs hD

theorem Good.bounds {q ν t : Nat} (h : Good q ν t) : 1 ≤ t ∧ t ≤ q := by
  obtain ⟨π, hπ, hh⟩ := h
  exact (mem_range'_of_perm hπ.1).1 (List.mem_of_mem_head? hh)

/-! ## Sources -/

theorem sig_zero {q t : Nat} (ht : 1 ≤ t ∧ t ≤ q) : sig q 0 t = q + 1 - t := by
  rw [sig_eq (by omega) ht]; split_ifs <;> omega

/-- `ν = 0`: every valid sequence is a chain (live2 2.2, `q ∣ N`). -/
theorem good_zero {q t : Nat} (ht : 1 ≤ t ∧ t ≤ q) : Good q 0 t := by
  obtain ⟨a, hf, hs, p, rfl⟩ := extends_single q t ht.1 ht.2
  have hb : ∀ x ∈ [t] ++ p, 1 ≤ x ∧ x ≤ q := fun x hx => (mem_range'_of_perm hf).1 hx
  refine ⟨[t] ++ p, ⟨hf, hs, ?_⟩, by simp⟩
  rw [List.map_congr_left (fun x hx => sig_zero (hb x hx))]
  exact hs.mirror hf

/-- The reflection `sig q ν` maps good classes to good classes (same `ν`). -/
theorem good_sig {q ν t : Nat} (hν : ν < q) (h : Good q ν t) : Good q ν (sig q ν t) := by
  obtain ⟨π, ⟨hf, h1, h2⟩, hh⟩ := h
  have hb : ∀ x ∈ π, 1 ≤ x ∧ x ≤ q := fun x hx => (mem_range'_of_perm hf).1 hx
  refine ⟨π.map (sig q ν), ⟨isFoldSeq_map_sig hν hf, h2, ?_⟩, ?_⟩
  · have e : π.map (sig q ν ∘ sig q ν) = π := by
      conv_rhs => rw [← List.map_id π]
      exact List.map_congr_left fun x hx => sig_sig hν (hb x hx)
    rw [List.map_map, e]
    exact h1
  · cases π with
    | nil => simp at hh
    | cons a π' => simp only [List.head?_cons, Option.some.injEq] at hh; subst hh; simp

theorem sig_mirror {q ν x : Nat} (hν : ν < q) (hx : 1 ≤ x ∧ x ≤ q) :
    sig q ((q - ν) % q) (q + 1 - x) = q + 1 - sig q ν x := by
  have hx' : 1 ≤ q + 1 - x ∧ q + 1 - x ≤ q := by omega
  rcases Nat.eq_zero_or_pos ν with rfl | hν0
  · rw [Nat.sub_zero, Nat.mod_self, sig_zero hx', sig_zero hx]
  · rw [Nat.mod_eq_of_lt (show q - ν < q by omega), sig_eq (by omega) hx', sig_eq hν hx]
    split_ifs <;> omega

/-- The mirror `t ↦ q + 1 - t` maps good classes for `ν` to good classes for `-ν`. -/
theorem good_mirror {q ν t : Nat} (hν : ν < q) (h : Good q ν t) :
    Good q ((q - ν) % q) (q + 1 - t) := by
  obtain ⟨π, ⟨hf, h1, h2⟩, hh⟩ := h
  have hb : ∀ x ∈ π, 1 ≤ x ∧ x ≤ q := fun x hx => (mem_range'_of_perm hf).1 hx
  refine ⟨π.map (q + 1 - ·), ⟨hf.mirror, h1.mirror hf, ?_⟩, ?_⟩
  · rw [List.map_map]
    have e : π.map (sig q ((q - ν) % q) ∘ (q + 1 - ·)) = (π.map (sig q ν)).map (q + 1 - ·) := by
      rw [List.map_map]
      exact List.map_congr_left fun x hx => sig_mirror hν (hb x hx)
    rw [e]
    exact h2.mirror (isFoldSeq_map_sig hν hf)
  · cases π with
    | nil => simp at hh
    | cons a π' => simp only [List.head?_cons, Option.some.injEq] at hh; subst hh; simp

/-- **`q ≤ 12`**: every non-exceptional class is good (from the table of live2). -/
theorem good_table {q ν s : Nat} (h2 : 2 ≤ q) (hq : q ≤ 12) (hν : ν < q) (hs1 : 1 ≤ s)
    (hsq : s ≤ q) (he : excB q ν s = false) : Good q ν s := by
  have hok := chainFor_ok h2 (by omega) hν hs1 hsq he
  unfold chainOKB at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hperm, hc⟩ := hok
  have hnd : (chainFor q ν s).Nodup := hperm.nodup_iff.2 ((List.nodup_range' ..).filter _)
  have hmem : ∀ t, t ∈ chainFor q ν s ↔ 1 ≤ t ∧ t ≤ q ∧ t ≠ s := by
    intro t
    rw [hperm.mem_iff, List.mem_filter, List.mem_range'_1]
    simp only [bne_iff_ne, ne_eq]
    omega
  have hb : ∀ t ∈ chainFor q ν s, 1 ≤ t ∧ t ≤ q := fun t ht => by
    have := (hmem t).1 ht; omega
  have hnd' : (chainFor q ν s ++ [s]).Nodup :=
    List.nodup_append.2 ⟨hnd, List.nodup_singleton s, fun a ha b hb' e => by
      simp at hb'; subst hb'; subst e; exact ((hmem a).1 ha).2.2 rfl⟩
  have hf : IsFoldSeq q (chainFor q ν s ++ [s]) := by
    refine perm_of_mem_iff hnd' (List.nodup_range' ..) fun x => ?_
    rw [List.mem_append, hmem, List.mem_range'_1, List.mem_singleton]
    omega
  obtain ⟨v1, v2⟩ := valid_of_chainOK hν hnd hb hc
  have hf' := isFoldSeq_map_sig hν hf
  rw [List.map_append, List.map_singleton] at hf'
  refine good_of_last hν ⟨hf, semiSymmetric_snoc hf v1, ?_⟩ (by simp)
  rw [List.map_append, List.map_singleton]
  exact semiSymmetric_snoc hf' v2

/-- **Theorem H** (live3): for odd `q = 2k + 1` and `ν = 1`, the classes `2 v₀ + 1` and
`q + 1 - 2 v₀` (`v₀` odd, `v₀ ≤ k`) are good. -/
theorem good_nu_one {k v₀ t : Nat} (hv : v₀ % 2 = 1) (hvk : v₀ ≤ k)
    (ht : t = 2 * v₀ + 1 ∨ t = 2 * k + 2 - 2 * v₀) : Good (2 * k + 1) 1 t := by
  obtain ⟨π, hf, hc, hcr, hh, hl⟩ := palindromic_chain (k := k) hv hvk
  have hν : 1 < 2 * k + 1 := by omega
  rcases ht with rfl | rfl
  · exact ⟨π, goodL_of_chain hν hf hc, hh⟩
  · exact good_of_last hν (goodL_of_chain hν hf hc) (by rw [hl]; congr 1; omega)

/-- A good class for `ν = 1`, rotated by one step, is good for `ν = q - 1`. -/
theorem good_rot {q t : Nat} (hq : 2 ≤ q) (h : Good q 1 t) : Good q (q - 1) (rot q t) := by
  obtain ⟨π, hπ, hh⟩ := h
  have hb : ∀ x ∈ π, 1 ≤ x ∧ x ≤ q := fun x hx => (mem_range'_of_perm hπ.1).1 hx
  refine ⟨π.map (rot q), goodL_of_chain (by omega) (isFoldSeq_map_rot hq hπ.1)
    (chainOK_rot hq hb (hπ.chainOK (by omega))), ?_⟩
  cases π with
  | nil => simp at hh
  | cons a π' => simp only [List.head?_cons, Option.some.injEq] at hh; subst hh; simp

/-! ## Block chains (live2 3.1) -/

theorem mul_add_mod_mul {j m X R : Nat} (hm : 0 < m) (hR : R < j) :
    (j * X + R) % (m * j) = j * (X % m) + R := by
  have h1 : j * X + R = (j * (X % m) + R) + (m * j) * (X / m) := by
    have := Nat.div_add_mod X m
    calc j * X + R = j * (m * (X / m) + X % m) + R := by rw [this]
      _ = _ := by ring
  rw [h1, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have h2 : X % m + 1 ≤ m := Nat.mod_lt _ hm
  have h3 := Nat.mul_le_mul_left j h2
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm j m] at h3
  omega

/-- The inner rotation used for the block of class `a` mod `j`. -/
def inner (m c e a : Nat) : Nat := if a ≤ e then (c + 1) % m else c

theorem inner_lt {m c e a : Nat} (hm : 0 < m) (hc : c < m) : inner m c e a < m := by
  unfold inner; split_ifs
  · exact Nat.mod_lt _ hm
  · exact hc

/-- The reflection `sig` of the `m j`-strip, on residue classes mod `j`. -/
theorem sig_cls {j m c e a y : Nat} (hj : 0 < j) (hm : 0 < m) (hc : c < m) (he : e < j)
    (ha : 1 ≤ a ∧ a ≤ j) (hy : 1 ≤ y ∧ y ≤ m) :
    sig (m * j) (j * c + e) (cls j a y) = cls j (sig j e a) (sig m (inner m c e a) y) := by
  obtain ⟨Y, rfl⟩ : ∃ Y, y = Y + 1 := ⟨y - 1, by omega⟩
  have hYm : Y < m := by omega
  have hYj : Y * j + j ≤ m * j := by
    have := Nat.mul_le_mul_right j (show Y + 1 ≤ m by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  unfold sig cls inner
  simp only [Nat.add_sub_cancel]
  split_ifs with hae
  · -- the block of `a` sits in the same period
    have e1 : (e + j - a) % j = e - a := by
      rw [show e + j - a = (e - a) + j * 1 by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
    have e2 : ((c + 1) % m + m - (Y + 1)) % m = (c + m - Y) % m := by
      rcases Nat.lt_or_ge (c + 1) m with h | h
      · rw [Nat.mod_eq_of_lt h]; congr 1; omega
      · have : c + 1 = m := by omega
        rw [this, Nat.mod_self, show 0 + m - (Y + 1) = m - 1 - Y by omega,
          show c + m - Y = (m - 1 - Y) + m * 1 by omega, Nat.add_mul_mod_self_left]
    have e3 : j * c + e + m * j - (Y * j + a) = j * (c + m - Y) + (e - a) := by
      have : j * (c + m - Y) + j * Y = j * c + m * j := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by omega), Nat.mul_add, Nat.mul_comm m j]
      rw [Nat.mul_comm Y j] at hYj ⊢
      omega
    rw [e1, e2, e3, mul_add_mod_mul hm (by omega), Nat.mul_comm j]
    omega
  · have e1 : (e + j - a) % j = e + j - a := Nat.mod_eq_of_lt (by omega)
    have e2 : (c + m - (Y + 1)) % m = (c + m - Y - 1) % m := by congr 1
    have e3 : j * c + e + m * j - (Y * j + a) = j * (c + m - Y - 1) + (e + j - a) := by
      have : j * (c + m - Y - 1) + j * Y + j = j * c + m * j := by
        rw [← Nat.mul_add, ← Nat.mul_succ, show (c + m - Y - 1 + Y).succ = c + m by omega,
          Nat.mul_add, Nat.mul_comm m j]
      rw [Nat.mul_comm Y j] at hYj ⊢
      omega
    rw [e1, e2, e3, mul_add_mod_mul hm (by omega), Nat.mul_comm j]
    omega

/-- **Block chains.**  Let `ν = j c + e` (`c < m`, `e < j`).  If class `a` is good mod `j`
for `e`, index `y` is good mod `m` for the inner rotation of `a` (`c + 1` if `a ≤ e`,
else `c`), and the `m`-strip has rotation-stable sequences for `c` (and for `c + 1` when
`e > 0`), then `cls j a y` is good mod `m j` for `ν`. -/
theorem good_comp {j m c e a y : Nat} (hj : 0 < j) (hm : 0 < m) (hc : c < m) (he : e < j)
    (ha : Good j e a) (hy : Good m (inner m c e a) y) (hA : ∃ z, Good m c z)
    (hB : 0 < e → ∃ z, Good m ((c + 1) % m) z) :
    Good (m * j) (j * c + e) (cls j a y) := by
  have hfam : ∀ b, ∃ l, (1 ≤ b → b ≤ j → GoodL m (inner m c e b) l) ∧
      (b = a → l.head? = some y) := by
    intro b
    by_cases hba : b = a
    · subst hba
      obtain ⟨l, hl, hh⟩ := hy
      exact ⟨l, fun _ _ => hl, fun _ => hh⟩
    · by_cases hb1 : 1 ≤ b
      · by_cases hbe : b ≤ e
        · obtain ⟨z, l, hl, -⟩ := hB (by omega)
          refine ⟨l, fun _ _ => ?_, fun h => absurd h hba⟩
          unfold inner; rw [if_pos hbe]; exact hl
        · obtain ⟨z, l, hl, -⟩ := hA
          refine ⟨l, fun _ _ => ?_, fun h => absurd h hba⟩
          unfold inner; rw [if_neg hbe]; exact hl
      · exact ⟨[], fun h => absurd h hb1, fun h => absurd h hba⟩
  choose α hα using hfam
  obtain ⟨π, ⟨hπf, hπ1, hπ2⟩, hπh⟩ := ha
  have hbπ : ∀ b ∈ π, 1 ≤ b ∧ b ≤ j := fun b hb => (mem_range'_of_perm hπf).1 hb
  have hν : j * c + e < m * j := by
    have := Nat.mul_le_mul_left j (show c + 1 ≤ m by omega)
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm j m] at this
    omega
  have hinner : ∀ b, inner m c e b < m := fun b => inner_lt hm hc
  set β : Nat → List Nat := fun b => (α (sig j e b)).map (sig m (inner m c e (sig j e b)))
    with hβ
  have hmap : (blocks j π α).map (sig (m * j) (j * c + e)) =
      blocks j (π.map (sig j e)) β := by
    unfold blocks
    rw [List.map_flatten, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun b hb => ?_
    have hb' := hbπ b hb
    simp only [Function.comp, hβ, sig_sig he hb', List.map_map]
    refine List.map_congr_left fun y hy' => ?_
    have hyb := (mem_range'_of_perm ((hα b).1 hb'.1 hb'.2).1).1 hy'
    exact sig_cls hj hm hc he hb' hyb
  refine ⟨blocks j π α, ⟨isFoldSeq_blocks hj hπf fun b h1 h2 => ((hα b).1 h1 h2).1,
    semiSymmetric_blocks hj hπf hπ1 fun b h1 h2 => ⟨((hα b).1 h1 h2).1, ((hα b).1 h1 h2).2.1⟩,
    ?_⟩, ?_⟩
  · rw [hmap]
    refine semiSymmetric_blocks hj (isFoldSeq_map_sig he hπf) hπ2 fun b h1 h2 => ?_
    have hb' := sig_mem he ⟨h1, h2⟩
    have hg := (hα (sig j e b)).1 hb'.1 hb'.2
    exact ⟨isFoldSeq_map_sig (hinner _) hg.1, hg.2.2⟩
  · cases π with
    | nil => simp at hπh
    | cons b π' =>
      simp only [List.head?_cons, Option.some.injEq] at hπh
      subst hπh
      have hh := (hα b).2 rfl
      cases hl : α b with
      | nil => rw [hl] at hh; simp at hh
      | cons z l' =>
        rw [hl] at hh
        simp only [List.head?_cons, Option.some.injEq] at hh
        subst hh
        simp [blocks, hl]

/-! ## Palindromic chains at `ν = 4r + 1` (odd `q`)

PROOFS.txt section 2.  For `q = 2k + 1` and `ν = 4r + 1` the reflection `sig` fixes
`t₀ = 2r + 1`.  The transversal `X_r` = (evens below `t₀`) + (odds above `t₀`) is the image of
`phiR r` (`i ↦ 2i` for `i ≤ r`, `2i + 1` beyond), and `sig X_r` that of `psiR r`; on indices
`sig` acts as `sig k (2r)`.  Both maps agree with the window relation of the `k`-strip except
at the pairs `exc1` resp. `exc2`, so a sequence `β` of the `k`-strip which is good for `2r`
and places these exceptional partners late (`CG k r β`) gives the palindromic chain
`phiR β, t₀, reverse (psiR (sig β))`. -/

/-- Membership-only dependence of a step. -/
theorem semiStep_congr {N m : Nat} {S T : List Nat} (h : ∀ x, x ∈ S ↔ x ∈ T) :
    SemiStep N S m ↔ SemiStep N T m := by
  unfold SemiStep leftCount rightCount
  simp only [h]

/-- In a complete sequence `S, m, T`, the step `m` is valid after `S` iff it is valid
after `T`. -/
theorem semiStep_compl {N m : Nat} {S T : List Nat} (h : IsFoldSeq N (S ++ [m] ++ T)) :
    SemiStep N S m ↔ SemiStep N T m := by
  have hnd := nodup_of_foldSeq h
  have hS : S.Nodup := (List.nodup_append.1 (List.nodup_append.1 hnd).1).1
  have hT : T.Nodup := (List.nodup_append.1 hnd).2.1
  rw [semiStep_iff_balanced_append hS, semiStep_iff_balanced_append hT]
  have hf := (balanced_full (N := N) (m := m)).perm h.symm
  unfold Balanced at *
  simp only [List.countP_append, List.countP_cons, List.countP_nil] at *
  simp only [lt_irrefl, and_false, false_and, decide_false, Bool.false_eq_true, if_false] at *
  omega

/-- A sequence `A ++ B` is valid if `A` is, and `B` read backwards is valid from scratch. -/
theorem semiSymmetric_append_rev {N : Nat} {A B : List Nat} (h : IsFoldSeq N (A ++ B))
    (hA : SemiSymmetric N A) (hB : SemiSymmetric N B.reverse) : SemiSymmetric N (A ++ B) := by
  refine semiSymmetric_append_iff.2 ⟨hA, fun i hi => ?_⟩
  have e : A ++ B = (A ++ B.take i) ++ [B[i]] ++ B.drop (i + 1) := by
    simp only [List.append_assoc, List.singleton_append]
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  rw [e] at h
  rw [semiStep_compl h]
  have hj : B.length - 1 - i < B.reverse.length := by simp; omega
  have := hB (B.length - 1 - i) hj
  rw [List.take_reverse, List.getElem_reverse] at this
  rw [show B.length - (B.length - 1 - i) = i + 1 by omega] at this
  have e2 : B.length - 1 - (B.length - 1 - i) = i := by omega
  simp only [e2] at this
  exact (semiStep_congr fun x => by simp).1 this

/-- `φ` maps the window relation of `i` in the `k`-strip to that of `φ i` in the `Q`-strip,
as far as `j` is concerned. -/
def Agree (Q k : Nat) (φ : Nat → Nat) (i j : Nat) : Prop :=
  ((φ i - reach Q (φ i) ≤ φ j ∧ φ j < φ i) ↔ (i - reach k i ≤ j ∧ j < i)) ∧
  ((φ i < φ j ∧ φ j ≤ φ i + reach Q (φ i)) ↔ (i < j ∧ j ≤ i + reach k i))

theorem near_step {Q k : Nat} {φ : Nat → Nat} {S : List Nat} {i : Nat} (hS : S.Nodup)
    (hinj : ∀ a ∈ S, ∀ b ∈ S, φ a = φ b → a = b) (hag : ∀ j ∈ S, Agree Q k φ i j) :
    SemiStep Q (S.map φ) (φ i) ↔ SemiStep k S i := by
  have hS' := nodup_map_of_injOn hS hinj
  unfold SemiStep
  rw [leftCount_eq hS', rightCount_eq hS', leftCount_eq hS, rightCount_eq hS, List.countP_map,
    List.countP_map]
  have e1 : S.countP ((fun x => decide (φ i - reach Q (φ i) ≤ x ∧ x < φ i)) ∘ φ) =
      S.countP (fun x => decide (i - reach k i ≤ x ∧ x < i)) :=
    List.countP_congr fun j hj => by
      simp only [Function.comp, decide_eq_true_eq]; exact (hag j hj).1
  have e2 : S.countP ((fun x => decide (φ i < x ∧ x ≤ φ i + reach Q (φ i))) ∘ φ) =
      S.countP (fun x => decide (i < x ∧ x ≤ i + reach k i)) :=
    List.countP_congr fun j hj => by
      simp only [Function.comp, decide_eq_true_eq]; exact (hag j hj).2
  rw [e1, e2]

/-- `β` places no exceptional partner `j` (`e β[p] j`) before `β[p]`. -/
def Prec (e : Nat → Nat → Prop) (β : List Nat) : Prop :=
  ∀ p (h : p < β.length), ∀ j ∈ β.take p, ¬ e β[p] j

theorem semiSymmetric_near {Q k : Nat} {φ : Nat → Nat} {e : Nat → Nat → Prop} {β : List Nat}
    (hb : ∀ x ∈ β, 1 ≤ x ∧ x ≤ k) (hnd : β.Nodup) (hv : SemiSymmetric k β) (hp : Prec e β)
    (hinj : ∀ a b, 1 ≤ a → a ≤ k → 1 ≤ b → b ≤ k → φ a = φ b → a = b)
    (hag : ∀ i j, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → i ≠ j → ¬ e i j → Agree Q k φ i j) :
    SemiSymmetric Q (β.map φ) := by
  intro p hp'
  simp only [List.length_map] at hp'
  rw [List.getElem_map, ← List.map_take]
  have hi := hb _ (List.getElem_mem hp')
  have hbt : ∀ x ∈ β.take p, 1 ≤ x ∧ x ≤ k := fun x hx => hb x (List.mem_of_mem_take hx)
  refine (near_step (take_nodup hnd p) (fun a ha b hb' h => ?_) (fun j hj => ?_)).2 (hv p hp')
  · exact hinj a b (hbt a ha).1 (hbt a ha).2 (hbt b hb').1 (hbt b hb').2 h
  · have hj' := hbt j hj
    refine hag _ _ hi.1 hi.2 hj'.1 hj'.2 ?_ (hp p hp' j hj)
    intro h
    obtain ⟨m, hm, e'⟩ := List.getElem_of_mem hj
    rw [List.getElem_take] at e'
    have : m = p := (hnd.getElem_inj_iff).1 (e'.trans h.symm)
    simp at hm; omega

def phiR (r i : Nat) : Nat := if i ≤ r then 2 * i else 2 * i + 1

def psiR (r i : Nat) : Nat := if i ≤ r then 2 * i - 1 else 2 * i

/-- Exceptional pairs of `phiR`: doubling `i ↦ 2i` above `r`, and `i ↦ 2i - k` below `r`. -/
def exc1 (k r i j : Nat) : Prop := (j = 2 * i ∧ r < i ∧ 2 * i ≤ k) ∨ (j + k = 2 * i ∧ 1 ≤ j ∧ j ≤ r)

/-- Exceptional pairs of `psiR`. -/
def exc2 (r i j : Nat) : Prop := j + 1 = 2 * i ∧ i ≤ r ∧ r + 1 < 2 * i

theorem agree_phi {k r i j : Nat} (hrk : 2 * r < k) (hi1 : 1 ≤ i) (hik : i ≤ k) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (hij : i ≠ j) (he : ¬ exc1 k r i j) : Agree (2 * k + 1) k (phiR r) i j := by
  unfold Agree phiR reach exc1 at *
  split_ifs <;> omega

theorem agree_psi {k r i j : Nat} (hrk : 2 * r < k) (hi1 : 1 ≤ i) (hik : i ≤ k) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (hij : i ≠ j) (he : ¬ exc2 r i j) : Agree (2 * k + 1) k (psiR r) i j := by
  unfold Agree psiR reach exc2 at *
  split_ifs <;> omega

theorem sig_phiR {k r i : Nat} (hrk : 2 * r < k) (hi : 1 ≤ i ∧ i ≤ k) :
    sig (2 * k + 1) (4 * r + 1) (phiR r i) = psiR r (sig k (2 * r) i) := by
  have h1 : 1 ≤ phiR r i ∧ phiR r i ≤ 2 * k + 1 := by unfold phiR; split_ifs <;> omega
  rw [sig_eq (by omega) h1, sig_eq (by omega) hi]
  unfold phiR psiR
  split_ifs <;> omega

theorem sig_psiR {k r i : Nat} (hrk : 2 * r < k) (hi : 1 ≤ i ∧ i ≤ k) :
    sig (2 * k + 1) (4 * r + 1) (psiR r (sig k (2 * r) i)) = phiR r i := by
  have h1 : 1 ≤ phiR r i ∧ phiR r i ≤ 2 * k + 1 := by unfold phiR; split_ifs <;> omega
  rw [← sig_phiR hrk hi, sig_sig (by omega) h1]

/-- The constrained problem for the transversal `X_r`. -/
def CG (k r : Nat) (β : List Nat) : Prop :=
  GoodL k (2 * r) β ∧ Prec (exc1 k r) β ∧ Prec (exc2 r) (β.map (sig k (2 * r)))

/-- **Palindromic chains at `ν = 4r + 1`.**  A solution of the constrained problem in the
`k`-strip starting with `b` gives a good class `phiR r b` mod `2k + 1` for `ν = 4r + 1`. -/
theorem good_palin {k r b : Nat} (hrk : 2 * r < k) {β : List Nat} (hβ : CG k r β)
    (hh : β.head? = some b) : Good (2 * k + 1) (4 * r + 1) (phiR r b) := by
  obtain ⟨⟨hf, hv1, hv2⟩, hp1, hp2⟩ := hβ
  have hb : ∀ x ∈ β, 1 ≤ x ∧ x ≤ k := fun x hx => (mem_range'_of_perm hf).1 hx
  have hnd := nodup_of_foldSeq hf
  have hν : 2 * r < k := hrk
  set σβ := β.map (sig k (2 * r)) with hσβ
  have hfσ : IsFoldSeq k σβ := isFoldSeq_map_sig (by omega) hf
  have hbσ : ∀ x ∈ σβ, 1 ≤ x ∧ x ≤ k := fun x hx => (mem_range'_of_perm hfσ).1 hx
  set x := β.map (phiR r) with hx
  set y := σβ.map (psiR r) with hy
  have hxv : SemiSymmetric (2 * k + 1) x :=
    semiSymmetric_near hb hnd hv1 hp1
      (fun a b _ _ _ _ h => by unfold phiR at h; split_ifs at h <;> omega)
      (fun i j h1 h2 h3 h4 h5 h6 => agree_phi hrk h1 h2 h3 h4 h5 h6)
  have hyv : SemiSymmetric (2 * k + 1) y :=
    semiSymmetric_near hbσ (nodup_of_foldSeq hfσ) hv2 hp2
      (fun a b _ _ _ _ h => by unfold psiR at h; split_ifs at h <;> omega)
      (fun i j h1 h2 h3 h4 h5 h6 => agree_psi hrk h1 h2 h3 h4 h5 h6)
  set π := x ++ [2 * r + 1] ++ y.reverse with hπ
  -- the complete sequence
  have hxb : ∀ z ∈ x, (∃ i, 1 ≤ i ∧ i ≤ k ∧ z = phiR r i) := by
    intro z hz; obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz; exact ⟨i, (hb i hi).1, (hb i hi).2, rfl⟩
  have hyb : ∀ z ∈ y, (∃ i, 1 ≤ i ∧ i ≤ k ∧ z = psiR r i) := by
    intro z hz; obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
    exact ⟨i, (hbσ i hi).1, (hbσ i hi).2, rfl⟩
  have hxnd : x.Nodup := nodup_map_of_injOn hnd fun a _ b _ h => by
    unfold phiR at h; split_ifs at h <;> omega
  have hynd : y.Nodup := nodup_map_of_injOn (nodup_of_foldSeq hfσ) fun a _ b _ h => by
    unfold psiR at h; split_ifs at h <;> omega
  have hπf : IsFoldSeq (2 * k + 1) π := by
    refine perm_range'_of_nodup_subset ?_ ?_ ?_
    · rw [hπ, List.nodup_append, List.nodup_append]
      refine ⟨⟨hxnd, List.nodup_singleton _, ?_⟩, List.nodup_reverse.2 hynd, ?_⟩
      · intro a ha b hb' e; simp at hb'
        obtain ⟨i, h1, h2, h⟩ := hxb a ha; unfold phiR at h; split_ifs at h <;> omega
      · intro a ha b hb' e
        rw [List.mem_reverse] at hb'
        obtain ⟨i, h1, h2, h⟩ := hyb b hb'
        rw [List.mem_append] at ha
        rcases ha with ha | ha
        · obtain ⟨i', h1', h2', h'⟩ := hxb a ha
          unfold psiR at h; unfold phiR at h'; split_ifs at h h' <;> omega
        · simp at ha; unfold psiR at h; split_ifs at h <;> omega
    · intro z hz
      rw [hπ, List.mem_append, List.mem_append, List.mem_reverse] at hz
      rcases hz with (hz | hz) | hz
      · obtain ⟨i, h1, h2, rfl⟩ := hxb z hz; unfold phiR; split_ifs <;> omega
      · simp at hz; omega
      · obtain ⟨i, h1, h2, rfl⟩ := hyb z hz; unfold psiR; split_ifs <;> omega
    · rw [hπ]; simp [hx, hy, hσβ, hf.length_eq]; omega
  -- the middle step
  have hmid : SemiStep (2 * k + 1) x (2 * r + 1) := by
    unfold SemiStep
    rw [leftCount_eq hxnd, rightCount_eq hxnd, hx, List.countP_map, List.countP_map,
      hf.countP_eq, hf.countP_eq]
    have hre : reach (2 * k + 1) (2 * r + 1) = 2 * r := by unfold reach; omega
    rw [hre]
    have e1 : (List.range' 1 k).countP ((fun z => decide (2 * r + 1 - 2 * r ≤ z ∧ z < 2 * r + 1))
        ∘ phiR r) = (List.range' 1 k).countP (fun y => decide (1 ≤ y ∧ y ≤ r)) :=
      List.countP_congr fun i hi => by
        rw [List.mem_range'_1] at hi
        simp only [Function.comp, decide_eq_true_eq]; unfold phiR; split_ifs <;> omega
    have e2 : (List.range' 1 k).countP ((fun z => decide (2 * r + 1 < z ∧ z ≤ 2 * r + 1 + 2 * r))
        ∘ phiR r) = (List.range' 1 k).countP (fun y => decide (r + 1 ≤ y ∧ y ≤ 2 * r)) :=
      List.countP_congr fun i hi => by
        rw [List.mem_range'_1] at hi
        simp only [Function.comp, decide_eq_true_eq]; unfold phiR; split_ifs <;> omega
    rw [e1, e2, countP_range'_interval, countP_range'_interval]
    omega
  have hπs : SemiSymmetric (2 * k + 1) π := by
    rw [hπ]
    refine semiSymmetric_append_rev hπf (semiSymmetric_append_iff.2 ⟨hxv, fun j hj => ?_⟩)
      (by rwa [List.reverse_reverse])
    have : j = 0 := by simp at hj; omega
    subst this
    simpa using hmid
  have hmap : π.map (sig (2 * k + 1) (4 * r + 1)) = π.reverse := by
    have ex : x.map (sig (2 * k + 1) (4 * r + 1)) = y := by
      rw [hx, hy, hσβ, List.map_map, List.map_map]
      exact List.map_congr_left fun i hi => sig_phiR hrk (hb i hi)
    have ey : y.map (sig (2 * k + 1) (4 * r + 1)) = x := by
      rw [hx, hy, hσβ, List.map_map, List.map_map]
      exact List.map_congr_left fun i hi => sig_psiR hrk (hb i hi)
    have et : sig (2 * k + 1) (4 * r + 1) (2 * r + 1) = 2 * r + 1 := by
      rw [sig_eq (by omega) (by omega)]; split_ifs <;> omega
    rw [hπ]
    simp only [List.map_append, List.map_reverse, List.map_cons, List.map_nil, ex, ey, et,
      List.reverse_append, List.reverse_reverse, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.append_assoc, List.singleton_append, List.cons_append]
  refine ⟨π, ⟨hπf, hπs, by rw [hmap]; exact hπs.reverse hπf⟩, ?_⟩
  rw [hπ, hx]
  cases β with
  | nil => simp at hh
  | cons a β' => simp only [List.head?_cons, Option.some.injEq] at hh; subst hh; simp

/-! ### Parity recursion for the constrained problem

For `k = 2m` the reflection `sig k (2r)` exchanges the parity classes, so parity blocks
`α` (odd panels) `γ` (even panels) with `α, γ` good for `(m, r)` are good for `(2m, 2r)`; the
precedence constraints only concern `γ`.  For `r = 2r'` they are exactly the constraints of
`CG m r'` (`cg_double`), for `r = 1` they are the doubling condition (`cg_four`). -/

theorem sig_scale1 {m r y : Nat} (hr : r < m) (hy : 1 ≤ y ∧ y ≤ m) :
    sig (2 * m) (2 * r) (scale 1 y) = scale 0 (sig m r y) := by
  rw [sig_eq (by omega) (by unfold scale; omega), sig_eq hr hy]
  unfold scale; split_ifs <;> omega

theorem sig_scale0 {m r y : Nat} (hr : r < m) (hy : 1 ≤ y ∧ y ≤ m) :
    sig (2 * m) (2 * r) (scale 0 y) = scale 1 (sig m r y) := by
  rw [sig_eq (by omega) (by unfold scale; omega), sig_eq hr hy]
  unfold scale; split_ifs <;> omega

theorem sig_one_scale1 {n y : Nat} (hn : 2 ≤ n) (hy : 1 ≤ y ∧ y ≤ n) :
    sig (2 * n) 1 (scale 1 y) = scale 1 (sig n 1 y) := by
  rw [sig_eq (by omega) (by unfold scale; omega), sig_eq (by omega) hy]
  unfold scale; split_ifs <;> omega

theorem sig_one_scale0 {n y : Nat} (hn : 2 ≤ n) (hy : 1 ≤ y ∧ y ≤ n) :
    sig (2 * n) 1 (scale 0 y) = scale 0 (sig n 0 y) := by
  rw [sig_eq (by omega) (by unfold scale; omega), sig_eq (by omega) hy]
  unfold scale; split_ifs <;> omega

theorem isFoldSeq_half1 {m : Nat} {α : List Nat} (h : IsFoldSeq m α) :
    IsFoldSeq ((2 * m + 1) / 2) α := by rwa [show (2 * m + 1) / 2 = m by omega]

theorem isFoldSeq_half0 {m : Nat} {α : List Nat} (h : IsFoldSeq m α) :
    IsFoldSeq ((2 * m + 0) / 2) α := by rwa [show (2 * m + 0) / 2 = m by omega]

theorem map_congr_mem {f g : Nat → Nat} {L : List Nat} {m : Nat} (hL : IsFoldSeq m L)
    (h : ∀ y, 1 ≤ y ∧ y ≤ m → f y = g y) : L.map f = L.map g :=
  List.map_congr_left fun y hy => h y ((mem_range'_of_perm hL).1 hy)

/-- Parity blocks of two good sequences of `(m, r)` form a good sequence of `(2m, 2r)`. -/
theorem goodL_blocks {m r : Nat} (hr : r < m) {α γ : List Nat} (hα : GoodL m r α)
    (hγ : GoodL m r γ) : GoodL (2 * m) (2 * r) (α.map (scale 1) ++ γ.map (scale 0)) := by
  obtain ⟨hαf, hα1, hα2⟩ := hα
  obtain ⟨hγf, hγ1, hγ2⟩ := hγ
  have hb := IsFoldSeq.blocks (N := 2 * m) (c := 1) (by norm_num) (isFoldSeq_half1 hαf)
    (by simpa using isFoldSeq_half0 hγf)
  simp only [Nat.sub_self] at hb
  refine ⟨hb, ?_, ?_⟩
  · have := (semiSymmetric_blocks_iff (N := 2 * m) (c := 1) (by norm_num)
      (isFoldSeq_half1 hαf) (by simpa using isFoldSeq_half0 hγf)).2
      ⟨by rwa [show (2 * m + 1) / 2 = m by omega], by simpa [show (2 * m + 0) / 2 = m by omega]⟩
    simpa using this
  · rw [List.map_append, List.map_map, List.map_map,
      map_congr_mem hαf (f := sig (2 * m) (2 * r) ∘ scale 1) (g := scale 0 ∘ sig m r)
        fun y hy => sig_scale1 hr hy,
      map_congr_mem hγf (f := sig (2 * m) (2 * r) ∘ scale 0) (g := scale 1 ∘ sig m r)
        fun y hy => sig_scale0 hr hy,
      ← List.map_map, ← List.map_map]
    have h1 := isFoldSeq_map_sig hr hαf
    have h2 := isFoldSeq_map_sig hr hγf
    have := (semiSymmetric_blocks_iff (N := 2 * m) (c := 0) (by norm_num)
      (isFoldSeq_half0 h1) (by simpa using isFoldSeq_half1 h2)).2
      ⟨by simpa [show (2 * m + 0) / 2 = m by omega], by
        simpa [show (2 * m + 1) / 2 = m by omega]⟩
    simpa using this

theorem goodL_blocks_one {n : Nat} (hn : 2 ≤ n) {α γ : List Nat} (hα : GoodL n 1 α)
    (hγ : GoodL n 0 γ) : GoodL (2 * n) 1 (α.map (scale 1) ++ γ.map (scale 0)) := by
  obtain ⟨hαf, hα1, hα2⟩ := hα
  obtain ⟨hγf, hγ1, hγ2⟩ := hγ
  have hb := IsFoldSeq.blocks (N := 2 * n) (c := 1) (by norm_num) (isFoldSeq_half1 hαf)
    (by simpa using isFoldSeq_half0 hγf)
  simp only [Nat.sub_self] at hb
  refine ⟨hb, ?_, ?_⟩
  · have := (semiSymmetric_blocks_iff (N := 2 * n) (c := 1) (by norm_num)
      (isFoldSeq_half1 hαf) (by simpa using isFoldSeq_half0 hγf)).2
      ⟨by rwa [show (2 * n + 1) / 2 = n by omega], by simpa [show (2 * n + 0) / 2 = n by omega]⟩
    simpa using this
  · rw [List.map_append, List.map_map, List.map_map,
      map_congr_mem hαf (f := sig (2 * n) 1 ∘ scale 1) (g := scale 1 ∘ sig n 1)
        fun y hy => sig_one_scale1 hn hy,
      map_congr_mem hγf (f := sig (2 * n) 1 ∘ scale 0) (g := scale 0 ∘ sig n 0)
        fun y hy => sig_one_scale0 hn hy,
      ← List.map_map, ← List.map_map]
    have h1 := isFoldSeq_map_sig (ν := 1) (by omega) hαf
    have h2 := isFoldSeq_map_sig (ν := 0) (by omega) hγf
    have := (semiSymmetric_blocks_iff (N := 2 * n) (c := 1) (by norm_num)
      (isFoldSeq_half1 h1) (by simpa using isFoldSeq_half0 h2)).2
      ⟨by simpa [show (2 * n + 1) / 2 = n by omega], by
        simpa [show (2 * n + 0) / 2 = n by omega]⟩
    simpa using this

theorem prec_append {e : Nat → Nat → Prop} {A B : List Nat} (hA : Prec e A)
    (hB : ∀ p (h : p < B.length), ∀ j ∈ A ++ B.take p, ¬ e B[p] j) : Prec e (A ++ B) := by
  intro p hp j hj
  by_cases hpA : p < A.length
  · rw [List.getElem_append_left hpA]
    rw [List.take_append_of_le_length (by omega)] at hj
    exact hA p hpA j hj
  · obtain ⟨i, rfl⟩ : ∃ i, p = A.length + i := ⟨p - A.length, by omega⟩
    rw [List.getElem_append_right (by omega)]
    rw [List.take_length_add_append] at hj
    simp only [List.length_append] at hp
    simpa using hB i (by omega) j hj

theorem prec_map {e : Nat → Nat → Prop} {f : Nat → Nat} {L : List Nat}
    (h : Prec (fun a b => e (f a) (f b)) L) : Prec e (L.map f) := by
  intro p hp j hj
  simp only [List.length_map] at hp
  rw [List.getElem_map]
  rw [← List.map_take] at hj
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hj
  exact h p hp b hb

theorem prec_mono {e e' : Nat → Nat → Prop} {L : List Nat} (h : Prec e L)
    (hee : ∀ a ∈ L, ∀ b ∈ L, e' a b → e a b) : Prec e' L := by
  intro p hp j hj h'
  exact h p hp j hj (hee _ (List.getElem_mem hp) _ (List.mem_of_mem_take hj) h')

/-- Constraints on the even block. -/
def E1 (m r a b : Nat) : Prop := (b = 2 * a ∧ r < 2 * a ∧ 2 * a ≤ m) ∨
  (b + m = 2 * a ∧ 1 ≤ b ∧ 2 * b ≤ r)

def E2 (r a b : Nat) : Prop := b + 1 = 2 * a ∧ 2 * a ≤ r + 1 ∧ r + 3 < 4 * a

theorem cg_blocks {m r : Nat} (hr : r < m) {α γ : List Nat} (hα : GoodL m r α)
    (hγ : GoodL m r γ) (h1 : Prec (E1 m r) γ) (h2 : Prec (E2 r) (γ.map (sig m r))) :
    CG (2 * m) r (α.map (scale 1) ++ γ.map (scale 0)) := by
  have hαb : ∀ y ∈ α, 1 ≤ y ∧ y ≤ m := fun y hy => (mem_range'_of_perm hα.1).1 hy
  have hγb : ∀ y ∈ γ, 1 ≤ y ∧ y ≤ m := fun y hy => (mem_range'_of_perm hγ.1).1 hy
  refine ⟨goodL_blocks hr hα hγ, ?_, ?_⟩
  · refine prec_append (prec_map fun p hp j hj => ?_) fun p hp j hj => ?_
    · have := hαb _ (List.getElem_mem hp); have := hαb j (List.mem_of_mem_take hj)
      intro h
      unfold exc1 scale at h; omega
    · simp only [List.length_map] at hp
      rw [List.getElem_map]
      rw [List.mem_append] at hj
      rcases hj with hj | hj
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hj
        have := hγb _ (List.getElem_mem hp); have := hαb b hb
        intro h; unfold exc1 scale at h; omega
      · rw [← List.map_take] at hj
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hj
        intro h
        have ha := hγb _ (List.getElem_mem hp)
        have hb' := hγb b (List.mem_of_mem_take hb)
        apply h1 p hp b hb
        unfold exc1 scale at h; unfold E1; omega
  · rw [List.map_append, List.map_map, List.map_map,
      map_congr_mem hα.1 (f := sig (2 * m) (2 * r) ∘ scale 1) (g := scale 0 ∘ sig m r)
        fun y hy => sig_scale1 hr hy,
      map_congr_mem hγ.1 (f := sig (2 * m) (2 * r) ∘ scale 0) (g := scale 1 ∘ sig m r)
        fun y hy => sig_scale0 hr hy,
      ← List.map_map, ← List.map_map]
    have hσb : ∀ y ∈ γ.map (sig m r), 1 ≤ y ∧ y ≤ m := fun y hy =>
      (mem_range'_of_perm (isFoldSeq_map_sig hr hγ.1)).1 hy
    have hασ : ∀ y ∈ α.map (sig m r), 1 ≤ y ∧ y ≤ m := fun y hy =>
      (mem_range'_of_perm (isFoldSeq_map_sig hr hα.1)).1 hy
    refine prec_append (prec_map fun p hp j hj => ?_) fun p hp j hj => ?_
    · have := hασ _ (List.getElem_mem hp); have := hασ j (List.mem_of_mem_take hj)
      intro h; unfold exc2 scale at h; omega
    · simp only [List.length_map] at hp
      rw [List.getElem_map]
      rw [List.mem_append] at hj
      rcases hj with hj | hj
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hj
        have := hσb _ (List.getElem_mem (by simpa using hp : p < (γ.map (sig m r)).length))
        have := hασ b hb
        intro h; unfold exc2 scale at h; omega
      · rw [← List.map_take] at hj
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hj
        intro h
        have ha := hσb _ (List.getElem_mem (by simpa using hp : p < (γ.map (sig m r)).length))
        have hb' := hσb b (List.mem_of_mem_take hb)
        apply h2 p (by simpa using hp) b hb
        unfold exc2 scale at h; unfold E2; omega

/-- **Doubling step**: `CG (2m) (2r')` from a good sequence of `(m, 2r')` (which gives the
start) and a solution of `CG m r'`. -/
theorem cg_double {m r' : Nat} (hr : 2 * r' < m) {α γ : List Nat} (hα : GoodL m (2 * r') α)
    (hγ : CG m r' γ) : CG (2 * m) (2 * r') (α.map (scale 1) ++ γ.map (scale 0)) := by
  obtain ⟨hγg, hp1, hp2⟩ := hγ
  refine cg_blocks hr hα hγg (prec_mono hp1 fun a _ b _ h => ?_) (prec_mono hp2 fun a _ b _ h => ?_)
  · unfold E1 at h; unfold exc1; omega
  · unfold E2 at h; unfold exc2; omega

/-- **`r = 1`, `k = 4n`**: from a good sequence of `(2n, 1)` (the start), one of `(n, 1)`,
and Lemma W. -/
theorem cg_four {n : Nat} (hn : 2 ≤ n) {α γ₁ γ₂ : List Nat} (hα : GoodL (2 * n) 1 α)
    (h1 : GoodL n 1 γ₁) (h2 : GoodL n 0 γ₂) (hd : Doubling γ₂) :
    CG (2 * (2 * n)) 1 (α.map (scale 1) ++ (γ₁.map (scale 1) ++ γ₂.map (scale 0)).map (scale 0)) := by
  have hγ := goodL_blocks_one hn h1 h2
  have hb2 : ∀ y ∈ γ₂, 1 ≤ y ∧ y ≤ n := fun y hy => (mem_range'_of_perm h2.1).1 hy
  have hb1 : ∀ y ∈ γ₁, 1 ≤ y ∧ y ≤ n := fun y hy => (mem_range'_of_perm h1.1).1 hy
  refine cg_blocks (by omega) hα hγ ?_ ?_
  · refine prec_append (prec_map fun p hp j hj => ?_) fun p hp j hj => ?_
    · have := hb1 _ (List.getElem_mem hp); have := hb1 j (List.mem_of_mem_take hj)
      intro h; unfold E1 scale at h; omega
    · simp only [List.length_map] at hp
      rw [List.getElem_map]
      rw [List.mem_append] at hj
      rcases hj with hj | hj
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hj
        have := hb2 _ (List.getElem_mem hp); have := hb1 b hb
        intro h; unfold E1 scale at h; omega
      · rw [← List.map_take] at hj
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hj
        intro h
        have ha := hb2 _ (List.getElem_mem hp)
        have hb' := hb2 b (List.mem_of_mem_take hb)
        have hb'' : b = 2 * γ₂[p] := by unfold E1 scale at h; omega
        subst hb''
        exact double_not_before (nodup_of_foldSeq h2.1) hd hp hb
  · intro p hp j hj h
    unfold E2 at h; omega

/-- Rotation-stable sequences for `ν = 1` exist for every `n ≥ 2`. -/
theorem good_one_exists : ∀ n, 2 ≤ n → ∃ t, Good n 1 t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨k, rfl⟩
    · by_cases hm : m = 1
      · subst hm
        exact ⟨1, good_table (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
          (by unfold excB; simp)⟩
      · obtain ⟨y, hy⟩ := ih m (by omega) (by omega)
        have hm1 : 1 % m = 1 := Nat.mod_eq_of_lt (by omega)
        have := good_comp (j := 2) (m := m) (c := 0) (e := 1) (a := 1) (y := y) (by norm_num)
          (by omega) (by omega) (by norm_num)
          (good_table (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
            (by unfold excB; simp))
          (by unfold inner; simp only [le_refl, if_true, Nat.zero_add, hm1]; exact hy)
          ⟨1, good_zero ⟨le_rfl, by omega⟩⟩ fun _ => ⟨y, by simpa [hm1] using hy⟩
        exact ⟨_, by rw [show m + m = m * 2 by ring]; simpa using this⟩
    · have := good_nu_one (k := k) (v₀ := 1) (t := 3) rfl (by omega) (Or.inl rfl)
      exact ⟨3, this⟩

/-- Solvable instances of the constrained problem (`CGs k r b`: a solution of `CG k r`
starting with `b`), generated by `cg_four` and `cg_double`. -/
inductive CGs : Nat → Nat → Nat → Prop
  | four {n b : Nat} : 2 ≤ n → Good (2 * n) 1 b → CGs (4 * n) 1 (2 * b - 1)
  | dbl {m r' b b' : Nat} : 2 * r' < m → Good m (2 * r') b → CGs m r' b' →
      CGs (2 * m) (2 * r') (2 * b - 1)

theorem head_blocks {α γ : List Nat} {b : Nat} (h : α.head? = some b) :
    (α.map (scale 1) ++ γ).head? = some (2 * b - 1) := by
  cases α with
  | nil => simp at h
  | cons a α' => simp only [List.head?_cons, Option.some.injEq] at h; subst h; simp [scale]

theorem CGs.sound {k r b : Nat} (h : CGs k r b) : ∃ β, CG k r β ∧ β.head? = some b := by
  induction h with
  | @four n b hn hg =>
    obtain ⟨α, hα, hh⟩ := hg
    obtain ⟨t, γ₁, hγ₁, -⟩ := good_one_exists n hn
    obtain ⟨γ₂, hf, hs, -, hd⟩ := lemmaW n 1 rfl (by omega)
    have hγ₂ : GoodL n 0 γ₂ := ⟨hf, hs, by
      rw [map_congr_mem hf (g := (n + 1 - ·)) fun y hy => sig_zero hy]; exact hs.mirror hf⟩
    have := cg_four hn hα hγ₁ hγ₂ hd
    rw [show 2 * (2 * n) = 4 * n by ring] at this
    exact ⟨_, this, head_blocks hh⟩
  | @dbl m r' b b' hr hg _ ih =>
    obtain ⟨α, hα, hh⟩ := hg
    obtain ⟨γ, hγ, -⟩ := ih
    exact ⟨_, cg_double hr hα hγ, head_blocks hh⟩

/-- **Palindromic chains, general form.**  If `x` and `sig ∘ x` are valid from scratch, `t₀`
is fixed by `sig` and balanced by `x`, and `x, t₀, reverse (sig ∘ x)` is a complete
sequence, then it is a good sequence (`sig` maps it to its reverse). -/
theorem goodL_palin {q ν t₀ : Nat} (hν : ν < q) {x : List Nat}
    (hf : IsFoldSeq q (x ++ [t₀] ++ (x.map (sig q ν)).reverse)) (ht : sig q ν t₀ = t₀)
    (hx : SemiSymmetric q x) (hy : SemiSymmetric q (x.map (sig q ν)))
    (hmid : SemiStep q x t₀) : GoodL q ν (x ++ [t₀] ++ (x.map (sig q ν)).reverse) := by
  have hb : ∀ z ∈ x, 1 ≤ z ∧ z ≤ q := fun z hz => (mem_range'_of_perm hf).1 (by simp [hz])
  have hs : SemiSymmetric q (x ++ [t₀] ++ (x.map (sig q ν)).reverse) := by
    refine semiSymmetric_append_rev hf (semiSymmetric_append_iff.2 ⟨hx, fun j hj => ?_⟩)
      (by rwa [List.reverse_reverse])
    have : j = 0 := by simp at hj; omega
    subst this
    simpa using hmid
  refine ⟨hf, hs, ?_⟩
  have ey : (x.map (sig q ν)).map (sig q ν) = x := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id x]
    exact List.map_congr_left fun z hz => sig_sig hν (hb z hz)
  have hmap : (x ++ [t₀] ++ (x.map (sig q ν)).reverse).map (sig q ν) =
      (x ++ [t₀] ++ (x.map (sig q ν)).reverse).reverse := by
    simp only [List.map_append, List.map_reverse, List.map_cons, List.map_nil, ey, ht,
      List.reverse_append, List.reverse_reverse, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.append_assoc, List.singleton_append, List.cons_append]
  rw [hmap]
  exact hs.reverse hf

/-! ### Certificates for small `q` (checked by `decide`) -/

/-- A palindromic certificate `(q, ν, t₀, x)`. -/
def palOK (e : Nat × Nat × Nat × List Nat) : Prop :=
  e.2.1 < e.1 ∧ sig e.1 e.2.1 e.2.2.1 = e.2.2.1 ∧
    IsFoldSeq e.1 (e.2.2.2 ++ [e.2.2.1] ++ (e.2.2.2.map (sig e.1 e.2.1)).reverse) ∧
    SemiSymmetric e.1 e.2.2.2 ∧ SemiSymmetric e.1 (e.2.2.2.map (sig e.1 e.2.1)) ∧
    SemiStep e.1 e.2.2.2 e.2.2.1

instance (e : Nat × Nat × Nat × List Nat) : Decidable (palOK e) := by
  unfold palOK; infer_instance

theorem good_of_palOK {e : Nat × Nat × Nat × List Nat} (h : palOK e) {t : Nat}
    (ht : e.2.2.2.head? = some t) : Good e.1 e.2.1 t := by
  obtain ⟨hν, ht0, hf, hx, hy, hm⟩ := h
  refine ⟨_, goodL_palin hν hf ht0 hx hy hm, ?_⟩
  cases h : e.2.2.2 with
  | nil => rw [h] at ht; simp at ht
  | cons a l => rw [h] at ht; simpa using ht

/-- A full certificate `(q, ν, π)`: `π` is good for `ν`. -/
def fullOK (e : Nat × Nat × List Nat) : Prop :=
  e.2.1 < e.1 ∧ IsFoldSeq e.1 e.2.2 ∧ SemiSymmetric e.1 e.2.2 ∧
    SemiSymmetric e.1 (e.2.2.map (sig e.1 e.2.1))

instance (e : Nat × Nat × List Nat) : Decidable (fullOK e) := by
  unfold fullOK; infer_instance

theorem good_of_fullOK {q ν t : Nat} {π : List Nat} (h : fullOK (q, ν, π))
    (ht : π.head? = some t) : Good q ν t := ⟨π, h.2, ht⟩

/-! ## The closure of the good classes, and the enlarged family -/

/-- The good classes proven here (`experiments/live4/covlean4.py` computes this closure). -/
inductive Gd : Nat → Nat → Nat → Prop
  | table {q ν s : Nat} : 2 ≤ q → q ≤ 12 → ν < q → 1 ≤ s → s ≤ q → excB q ν s = false →
      Gd q ν s
  | zero {q t : Nat} : 1 ≤ t → t ≤ q → Gd q 0 t
  | nu_one {k v₀ t : Nat} : v₀ % 2 = 1 → v₀ ≤ k → (t = 2 * v₀ + 1 ∨ t = 2 * k + 2 - 2 * v₀) →
      Gd (2 * k + 1) 1 t
  | sig {q ν t : Nat} : ν < q → Gd q ν t → Gd q ν (sig q ν t)
  | mirror {q ν t : Nat} : ν < q → Gd q ν t → Gd q ((q - ν) % q) (q + 1 - t)
  | comp {j m c e a y z z' : Nat} : 0 < j → 0 < m → c < m → e < j → Gd j e a →
      Gd m (inner m c e a) y → Gd m c z → (0 < e → Gd m ((c + 1) % m) z') →
      Gd (m * j) (j * c + e) (cls j a y)
  | cert {q ν t : Nat} {π : List Nat} : fullOK (q, ν, π) → π.head? = some t → Gd q ν t
  | palin {k r b : Nat} : 2 * r < k → CGs k r b → Gd (2 * k + 1) (4 * r + 1) (phiR r b)

theorem Gd.good {q ν t : Nat} (h : Gd q ν t) : Good q ν t := by
  induction h with
  | table h2 hq hν hs1 hsq he => exact good_table h2 hq hν hs1 hsq he
  | zero h1 h2 => exact good_zero ⟨h1, h2⟩
  | nu_one hv hvk ht => exact good_nu_one hv hvk ht
  | sig hν _ ih => exact good_sig hν ih
  | mirror hν _ ih => exact good_mirror hν ih
  | comp hj hm hc he _ _ _ _ iha ihy ihz ihz' =>
    exact good_comp hj hm hc he iha ihy ⟨_, ihz⟩ fun h => ⟨_, ihz' h⟩
  | cert h ht => exact good_of_fullOK h ht
  | palin hrk hc =>
    obtain ⟨β, hβ, hh⟩ := hc.sound
    exact good_palin hrk hβ hh

/-- For `q = 2^a` every class is good for every `ν` (parity recursion, `good_comp` with
`j = 2`). -/
theorem good_pow_two : ∀ a ν t, ν < 2 ^ a → 1 ≤ t → t ≤ 2 ^ a → Good (2 ^ a) ν t := by
  intro a
  induction a with
  | zero =>
    intro ν t hν h1 h2
    simp only [pow_zero] at *
    obtain rfl : ν = 0 := by omega
    exact good_zero ⟨h1, h2⟩
  | succ a ih =>
    intro ν t hν h1 h2
    have hp : 0 < 2 ^ a := Nat.pow_pos (by norm_num)
    have e2 : 2 ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
    rw [e2] at hν h2 ⊢
    have hb : 1 ≤ (t - 1) % 2 + 1 ∧ (t - 1) % 2 + 1 ≤ 2 := by omega
    have ht : t = cls 2 ((t - 1) % 2 + 1) ((t - 1) / 2 + 1) := by unfold cls; simp; omega
    have hν' : ν = 2 * (ν / 2) + ν % 2 := by omega
    rw [ht, hν']
    refine good_comp (by norm_num) hp (by omega) (Nat.mod_lt _ (by norm_num))
      (good_table (by norm_num) (by norm_num) (Nat.mod_lt _ (by norm_num)) hb.1 hb.2
        (by unfold excB; simp)) (ih _ _ (inner_lt hp (by omega)) (by omega) (by omega))
      ⟨1, ih _ _ (by omega) le_rfl (by omega)⟩
      fun _ => ⟨1, ih _ _ (Nat.mod_lt _ hp) le_rfl (by omega)⟩

/-- **The enlarged proven family**: base cases, residue transfers through every good class
(any modulus `q`), and the mirror. -/
inductive Cov2 : Nat → Finset Nat → Prop
  | small {N : Nat} {D : Finset Nat} : (Finset.Icc 1 N \ D).card ≤ 1 → Cov2 N D
  | table {N u v : Nat} : N ≤ 12 → 1 ≤ u → u < v → v ≤ N → deadB N u v = false →
      Cov2 N {u, v}
  | res {q N s : Nat} {D : Finset Nat} : 2 ≤ q → q ≤ N → Good q (N % q) s →
      D ⊆ Finset.Icc 1 (ccount q s N) → Cov2 (ccount q s N) D → Cov2 N (D.image (cls q s))
  | mirror {N : Nat} {D : Finset Nat} : Cov2 N D → Cov2 N (D.image (N + 1 - ·))

theorem Cov2.coReach {N : Nat} {D : Finset Nat} (h : Cov2 N D) : CoReach N D := by
  induction h with
  | small h => exact coReach_small h
  | table hN hu huv hv hd => exact coReach_base hN hu huv hv hd
  | res hq2 hqN hg hDs _ ih => exact coReach_good (by omega) hqN hg hDs ih
  | mirror _ ih => exact coReach_mirror ih

/-- `Cov2` contains the family `Cov` of live2. -/
theorem Cov.cov2 {N : Nat} {D : Finset Nat} (h : Cov N D) : Cov2 N D := by
  induction h with
  | small h => exact Cov2.small h
  | table hN hu huv hv hd => exact Cov2.table hN hu huv hv hd
  | res hq2 hq12 hqN hs1 hsq hexc hDs _ ih =>
    exact Cov2.res hq2 hqN (good_table hq2 hq12 (Nat.mod_lt _ (by omega)) hs1 hsq hexc) hDs ih
  | mirror _ ih => exact Cov2.mirror ih

/-- Every valid 2-prefix whose set is in the family is live. -/
theorem Cov2.extends {N u v : Nat} (h : Cov2 N {u, v}) (hu : 1 ≤ u ∧ u ≤ N)
    (hv : 1 ≤ v ∧ v ≤ N) (huv : u ≠ v) (hval : SemiSymmetric N [u, v]) :
    Extends N [u, v] := by
  rw [extends_iff_coReach (by simp [huv]) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption) hval]
  convert h.coReach using 2
  ext x; simp

end Live4
end Folds
