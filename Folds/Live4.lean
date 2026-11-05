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

theorem Gd.good {q ν t : Nat} (h : Gd q ν t) : Good q ν t := by
  induction h with
  | table h2 hq hν hs1 hsq he => exact good_table h2 hq hν hs1 hsq he
  | zero h1 h2 => exact good_zero ⟨h1, h2⟩
  | nu_one hv hvk ht => exact good_nu_one hv hvk ht
  | sig hν _ ih => exact good_sig hν ih
  | mirror hν _ ih => exact good_mirror hν ih
  | comp hj hm hc he _ _ _ _ iha ihy ihz ihz' =>
    exact good_comp hj hm hc he iha ihy ⟨_, ihz⟩ fun h => ⟨_, ihz' h⟩

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
