import Folds.SymStructure

/-!
# Symmetric (3-AP-free) fold sequences II: extendable prefixes, live counts, the merge
count and Sharma's ends bound

See `experiments/symstruct2/NOTES.txt` and `experiments/symstruct/PROOFS.txt`.
-/

namespace Folds
namespace SymStructure2

open SymParity SymStructure
open scoped List

/-! ## Rescaling a parity class -/

/-- Rescaling of a parity class: `2r - 1 ↦ r` (odd class) and `2r ↦ r` (even class). -/
def half (v : ℕ) : ℕ := (v + 1) / 2

/-- Inverse of `half` on the class of parity `p`: `r ↦ 2r - p`. -/
def lift (p r : ℕ) : ℕ := 2 * r - p

/-- `a` lists every element of `[1, N]` exactly once. -/
def IsPermOf (N : ℕ) (a : List ℕ) : Prop := a.Nodup ∧ ∀ v, v ∈ a ↔ 1 ≤ v ∧ v ≤ N

/-- `π` is an **extendable** (live) prefix: it is a prefix of a 3-AP-free permutation of
`[1, N]`. -/
def Ext (N : ℕ) (π : List ℕ) : Prop := ∃ s, IsPermOf N (π ++ s) ∧ APF (π ++ s)

/-- The parity-`p` entries of `l`, rescaled. -/
def cls (p : ℕ) (l : List ℕ) : List ℕ := (l.filter (fun v => decide (v % 2 = p))).map half

theorem isPermOf_iff_isFoldSeq {N : ℕ} {a : List ℕ} : IsPermOf N a ↔ IsFoldSeq N a := by
  constructor
  · rintro ⟨hnd, hI⟩
    exact (List.perm_ext_iff_of_nodup hnd (List.nodup_range' ..)).2 fun v => by
      rw [hI, List.mem_range'_1]; omega
  · intro hf
    exact ⟨hf.nodup_iff.2 (List.nodup_range' ..), fun v => mem_range'_of_perm hf⟩

theorem IsPermOf.length {N : ℕ} {a : List ℕ} (h : IsPermOf N a) : a.length = N := by
  rw [(isPermOf_iff_isFoldSeq.1 h).length_eq]; simp

theorem apFree_of_apf {a : List ℕ} (h : APF a) : APFree a := by
  intro i j k hij hjk hk e
  have hj : j < a.length := by omega
  have hi : i < a.length := by omega
  have h1 : [a[k]] <+ a.drop k := by
    rw [List.drop_eq_getElem_cons hk]; exact List.singleton_sublist.2 List.mem_cons_self
  have h2 : [a[j], a[k]] <+ a.drop j := by
    rw [List.drop_eq_getElem_cons hj]
    exact (h1.trans (List.drop_sublist_drop_left _ (by omega))).cons_cons _
  have h3 : [a[i], a[j], a[k]] <+ a.drop i := by
    rw [List.drop_eq_getElem_cons hi]
    exact (h2.trans (List.drop_sublist_drop_left _ (by omega))).cons_cons _
  exact h _ _ _ (h3.trans (List.drop_sublist _ _)) e

theorem apf_iff_apFree {a : List ℕ} : APF a ↔ APFree a := ⟨apFree_of_apf, apf_of_apFree⟩

theorem mem_symSeqs_iff {N : ℕ} {a : List ℕ} : a ∈ symSeqs N ↔ IsPermOf N a ∧ APF a := by
  rw [mem_symSeqs, isPermOf_iff_isFoldSeq, apf_iff_apFree]
  constructor
  · rintro ⟨hf, hs⟩; exact ⟨hf, (symmetric_iff_apFree hf).1 hs⟩
  · rintro ⟨hf, hs⟩; exact ⟨hf, (symmetric_iff_apFree hf).2 hs⟩

/-- 3-AP-freeness is preserved by a map that reflects 3-term progressions. -/
theorem apf_map {l : List ℕ} {f : ℕ → ℕ}
    (hf : ∀ x ∈ l, ∀ y ∈ l, ∀ z ∈ l, f x + f z = 2 * f y → x + z = 2 * y) (h : APF l) :
    APF (l.map f) := by
  intro x' y' z' hs e
  obtain ⟨l', hl', he⟩ := List.sublist_map_iff.1 hs
  rcases l' with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, l'⟩⟩⟩⟩ <;> simp at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hx : x ∈ l := hl'.subset (by simp)
  have hy : y ∈ l := hl'.subset (by simp)
  have hz : z ∈ l := hl'.subset (by simp)
  exact h x y z hl' (hf x hx y hy z hz e)

theorem apf_map_half {l : List ℕ} {p : ℕ} (hp : ∀ v ∈ l, v % 2 = p) (h : APF l) :
    APF (l.map half) := by
  refine apf_map (fun x hx y hy z hz e => ?_) h
  have := hp x hx; have := hp y hy; have := hp z hz
  simp only [half] at e; omega

theorem apf_map_lift {l : List ℕ} {p : ℕ} (hp : p ≤ 1) (h1 : ∀ v ∈ l, 1 ≤ v) (h : APF l) :
    APF (l.map (lift p)) := by
  refine apf_map (fun x hx y hy z hz e => ?_) h
  have := h1 x hx; have := h1 y hy; have := h1 z hz
  simp only [lift] at e; omega

theorem half_lift {p r : ℕ} (hp : p ≤ 1) (hr : 1 ≤ r) : half (lift p r) = r := by
  simp only [half, lift]; omega

theorem lift_half {p v : ℕ} (hv : v % 2 = p) : lift p (half v) = v := by
  simp only [half, lift]; omega

theorem lift_mod {p r : ℕ} (hp : p ≤ 1) (hr : 1 ≤ r) : lift p r % 2 = p := by
  simp only [lift]; omega

theorem lift_inj {p : ℕ} (hp : p ≤ 1) : Function.Injective (lift p) := by
  intro x y e; simp only [lift] at e; omega

theorem cls_append (p : ℕ) (l₁ l₂ : List ℕ) : cls p (l₁ ++ l₂) = cls p l₁ ++ cls p l₂ := by
  simp [cls]

theorem mem_cls {p r : ℕ} {l : List ℕ} : r ∈ cls p l ↔ ∃ v ∈ l, v % 2 = p ∧ half v = r := by
  simp [cls, and_assoc]

theorem cls_nodup {p : ℕ} {l : List ℕ} (h : l.Nodup) : (cls p l).Nodup := by
  refine (h.filter _).map_on ?_
  intro x hx y hy e
  simp only [List.mem_filter, decide_eq_true_eq] at hx hy
  simp only [half] at e; omega

theorem cls_range {N p : ℕ} {l : List ℕ} (hp : p ≤ 1) (h : ∀ v ∈ l, 1 ≤ v ∧ v ≤ N) :
    ∀ r ∈ cls p l, 1 ≤ r ∧ r ≤ (N + p) / 2 := by
  intro r hr
  obtain ⟨v, hv, hvp, rfl⟩ := mem_cls.1 hr
  have := h v hv
  simp only [half]; omega

theorem cls_isPermOf {N p : ℕ} {a : List ℕ} (hp : p ≤ 1) (h : IsPermOf N a) :
    IsPermOf ((N + p) / 2) (cls p a) := by
  refine ⟨cls_nodup h.1, fun r => ⟨fun hr => cls_range hp (fun v hv => (h.2 v).1 hv) r hr,
    fun hr => mem_cls.2 ⟨lift p r, (h.2 _).2 ?_, lift_mod hp hr.1, half_lift hp hr.1⟩⟩⟩
  simp only [lift]; omega

theorem cls_apf {p : ℕ} {a : List ℕ} (h : APF a) : APF (cls p a) :=
  apf_map_half (p := p) (fun v hv => by simpa using (List.mem_filter.1 hv).2)
    (h.sublist List.filter_sublist)

/-- Lifting back the rescaled class gives the parity-`p` subsequence. -/
theorem map_lift_cls (p : ℕ) (l : List ℕ) :
    (cls p l).map (lift p) = l.filter (fun v => decide (v % 2 = p)) := by
  rw [cls, List.map_map]
  conv_rhs => rw [← List.map_id (List.filter _ l)]
  apply List.map_congr_left
  intro v hv
  simp only [List.mem_filter, decide_eq_true_eq] at hv
  exact lift_half hv.2

theorem cls_map_lift {p : ℕ} (hp : p ≤ 1) {l : List ℕ} (h1 : ∀ r ∈ l, 1 ≤ r) :
    cls p (l.map (lift p)) = l := by
  rw [cls, List.filter_eq_self.2, List.map_map]
  · conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left fun r hr => half_lift hp (h1 r hr)
  · intro v hv
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hv
    simpa using lift_mod hp (h1 r hr)

theorem cls_map_lift_other {p q : ℕ} (hp : p ≤ 1) (hq : q ≠ p) {l : List ℕ}
    (h1 : ∀ r ∈ l, 1 ≤ r) : cls q (l.map (lift p)) = [] := by
  rw [cls, List.filter_eq_nil_iff.2, List.map_nil]
  intro v hv
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hv
  have := lift_mod hp (h1 r hr)
  simp; omega

theorem filter_ne_eq (w : ℕ) (l : List ℕ) :
    l.filter (fun v => decide (v % 2 ≠ w % 2)) = l.filter (fun v => decide (v % 2 = 1 - w % 2)) :=
  List.filter_congr fun v _ => by
    rw [decide_eq_decide]; omega

/-! ## Basic facts about extendable prefixes -/

theorem Ext.nodup {N : ℕ} {π : List ℕ} (h : Ext N π) : π.Nodup := by
  obtain ⟨s, ⟨hnd, _⟩, _⟩ := h
  exact hnd.sublist (List.sublist_append_left _ _)

theorem Ext.range {N : ℕ} {π : List ℕ} (h : Ext N π) : ∀ v ∈ π, 1 ≤ v ∧ v ≤ N := by
  obtain ⟨s, ⟨_, hI⟩, _⟩ := h
  exact fun v hv => (hI v).1 (List.mem_append_left _ hv)

theorem Ext.of_append {N : ℕ} {π ρ : List ℕ} (h : Ext N (π ++ ρ)) : Ext N π := by
  obtain ⟨s, h1, h2⟩ := h
  exact ⟨ρ ++ s, by rwa [← List.append_assoc], by rwa [← List.append_assoc]⟩

theorem Ext.of_prefix {N : ℕ} {π ρ : List ℕ} (h : Ext N ρ) (hp : π <+: ρ) : Ext N π := by
  obtain ⟨t, rfl⟩ := hp
  exact h.of_append

theorem ext_iff_mem_symSeqs {N : ℕ} {π : List ℕ} : Ext N π ↔ ∃ a ∈ symSeqs N, π <+: a := by
  constructor
  · rintro ⟨s, h1, h2⟩
    exact ⟨π ++ s, mem_symSeqs_iff.2 ⟨h1, h2⟩, List.prefix_append _ _⟩
  · rintro ⟨a, ha, ⟨s, rfl⟩⟩
    exact ⟨s, mem_symSeqs_iff.1 ha⟩

theorem ext_zero : Ext 0 [] :=
  ⟨[], ⟨by simp, fun v => by simp; omega⟩, fun x y z hs _ => by
    have := hs.length_le; simp at this⟩

theorem ext_one : Ext 1 [1] :=
  ⟨[], ⟨by simp, fun v => by simp; omega⟩, fun x y z hs _ => by
    have := hs.length_le; simp at this⟩

/-- Every list of distinct elements of `[1, N]`, `N ≤ 1`, is extendable. -/
theorem ext_of_le_one {N : ℕ} {π : List ℕ} (hN : N ≤ 1) (hnd : π.Nodup)
    (hr : ∀ v ∈ π, 1 ≤ v ∧ v ≤ N) : Ext N π := by
  rcases π with _ | ⟨w, _ | ⟨w', t⟩⟩
  · rcases (show N = 0 ∨ N = 1 by omega) with rfl | rfl
    · exact ext_zero
    · exact (show Ext 1 ([] ++ [1]) from ext_one).of_append
  · have := hr w (by simp)
    obtain rfl : w = 1 := by omega
    obtain rfl : N = 1 := by omega
    exact ext_one
  · have h1 := hr w (by simp)
    have h2 := hr w' (by simp)
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
    exact absurd (by omega) hnd.1.1

/-! ## Theorem E: which prefixes extend -/

instance (N y u : ℕ) : Decidable (Linked N y u) :=
  inferInstanceAs (Decidable ((u < 2 * y ∧ 2 * y ≤ N + u) ∨ (y < 2 * u ∧ 2 * u ≤ N + y)))

/-- (a) On linked pairs inside `π`, the entry of the parity of `w` (the `D`-entry) comes
first. -/
def CondA (N w : ℕ) (π : List ℕ) : Prop :=
  ∀ y ∈ π, ∀ u ∈ π, y % 2 = w % 2 → u % 2 ≠ w % 2 → Linked N y u → Bef π y u

/-- (b) No `C`-entry of `π` is linked to a `D`-value of `[1, N]` outside `π`. -/
def CondB (N w : ℕ) (π : List ℕ) : Prop :=
  ∀ u ∈ π, ∀ y ∈ List.range' 1 N, y ∉ π → y % 2 = w % 2 → u % 2 ≠ w % 2 → ¬ Linked N y u

/-! Boolean versions (fast in the kernel). -/

def linkedB (N y u : ℕ) : Bool :=
  (Nat.blt u (2 * y) && Nat.ble (2 * y) (N + u)) || (Nat.blt y (2 * u) && Nat.ble (2 * u) (N + y))

theorem linkedB_iff {N y u : ℕ} : linkedB N y u = true ↔ Linked N y u := by
  simp [linkedB, Linked, Nat.blt_eq, Nat.ble_eq]

def befB : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => false
  | x :: t, y, u => (x == y && t.contains u) || befB t y u

theorem befB_iff : ∀ {l : List ℕ} {y u : ℕ}, befB l y u = true ↔ Bef l y u
  | [], y, u => by simp [befB, Bef]
  | x :: t, y, u => by
    rw [bef_cons_iff, ← befB_iff]
    simp only [befB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem]
    constructor
    · rintro (⟨rfl, h⟩ | h)
      · exact Or.inr ⟨rfl, h⟩
      · exact Or.inl h
    · rintro (h | ⟨rfl, h⟩)
      · exact Or.inr h
      · exact Or.inl ⟨rfl, h⟩

def condAB (N w : ℕ) (π : List ℕ) : Bool :=
  π.all fun y => y % 2 != w % 2 || π.all fun u => u % 2 == w % 2 || !linkedB N y u || befB π y u

def condBB (N w : ℕ) (π : List ℕ) : Bool :=
  π.all fun u => u % 2 == w % 2 || (List.range' 1 N).all fun y =>
    π.contains y || y % 2 != w % 2 || !linkedB N y u

theorem condAB_iff {N w : ℕ} {π : List ℕ} : condAB N w π = true ↔ CondA N w π := by
  simp only [condAB, CondA, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true', befB_iff]
  constructor
  · intro h y hy u hu hyw huw hl
    rcases h y hy with h | h
    · exact absurd hyw h
    · rcases h u hu with (h | h) | h
      · exact absurd h huw
      · rw [← Bool.not_eq_true, linkedB_iff] at h; exact absurd hl h
      · exact h
  · intro h y hy
    by_cases hyw : y % 2 = w % 2
    · refine Or.inr fun u hu => ?_
      by_cases huw : u % 2 = w % 2
      · exact Or.inl (Or.inl huw)
      by_cases hl : Linked N y u
      · exact Or.inr (h y hy u hu hyw huw hl)
      · exact Or.inl (Or.inr (by rw [← Bool.not_eq_true, linkedB_iff]; exact hl))
    · exact Or.inl hyw

theorem condBB_iff {N w : ℕ} {π : List ℕ} : condBB N w π = true ↔ CondB N w π := by
  simp only [condBB, CondB, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true', List.contains_iff_mem]
  constructor
  · intro h u hu y hy hyπ hyw huw hl
    rcases h u hu with h | h
    · exact huw h
    · rcases h y hy with (h | h) | h
      · exact hyπ h
      · exact h hyw
      · rw [← Bool.not_eq_true, linkedB_iff] at h; exact h hl
  · intro h u hu
    by_cases huw : u % 2 = w % 2
    · exact Or.inl huw
    refine Or.inr fun y hy => ?_
    by_cases hyπ : y ∈ π
    · exact Or.inl (Or.inl hyπ)
    by_cases hyw : y % 2 = w % 2
    · exact Or.inr (by rw [← Bool.not_eq_true, linkedB_iff]; exact h u hu y hy hyπ hyw huw)
    · exact Or.inl (Or.inr hyw)

instance (N w : ℕ) (π : List ℕ) : Decidable (CondA N w π) := decidable_of_iff _ condAB_iff
instance (N w : ℕ) (π : List ℕ) : Decidable (CondB N w π) := decidable_of_iff _ condBB_iff

theorem bef_left {π s : List ℕ} (hnd : (π ++ s).Nodup) {x y : ℕ} (hx : x ∈ π) (hy : y ∈ π)
    (h : Bef (π ++ s) x y) : Bef π x y := by
  rcases bef_total (hnd.sublist (List.sublist_append_left _ _)) hx hy (bef_ne hnd h) with h' | h'
  · exact h'
  · exact absurd (bef_append_left h') (bef_asymm hnd h)

/-- **Theorem E, "only if".** -/
theorem ext_imp {N w : ℕ} {π t : List ℕ} (hπ : π = w :: t) (h : Ext N π) :
    CondA N w π ∧ CondB N w π ∧ Ext ((N + w % 2) / 2) (cls (w % 2) π) ∧
      Ext ((N + (1 - w % 2)) / 2) (cls (1 - w % 2) π) := by
  obtain ⟨s, hP, hap⟩ := h
  have ha : π ++ s = w :: (t ++ s) := by rw [hπ]; rfl
  obtain ⟨_, _, hor⟩ := (merge_iff ha hP.1 hP.2).1 hap
  refine ⟨?_, ?_, ⟨cls (w % 2) s, ?_, ?_⟩, ⟨cls (1 - w % 2) s, ?_, ?_⟩⟩
  · intro y hy u hu hyw huw hl
    exact bef_left hP.1 hy hu
      (hor y u (List.mem_append_left _ hy) (List.mem_append_left _ hu) hyw huw hl)
  · intro u hu y hy hyπ hyw huw hl
    rw [List.mem_range'_1] at hy
    have hya : y ∈ π ++ s := (hP.2 y).2 (by omega)
    have hys : y ∈ s := by simpa [hyπ] using hya
    have h1 := hor y u hya (List.mem_append_left _ hu) hyw huw hl
    exact bef_asymm hP.1 h1 (bef_append_mid hu hys)
  · rw [← cls_append]; exact cls_isPermOf (by omega) hP
  · rw [← cls_append]; exact cls_apf hap
  · rw [← cls_append]; exact cls_isPermOf (by omega) hP
  · rw [← cls_append]; exact cls_apf hap

section classPart
variable {N p : ℕ} {π s₁ : List ℕ} (hp : p ≤ 1) (hP : IsPermOf ((N + p) / 2) (cls p π ++ s₁))
include hp hP

theorem part_range : ∀ v ∈ s₁.map (lift p), 1 ≤ v ∧ v ≤ N ∧ v % 2 = p := by
  intro v hv
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hv
  have := (hP.2 r).1 (List.mem_append_right _ hr)
  simp only [lift]; omega

theorem part_disj : ∀ v ∈ s₁.map (lift p), v ∉ π := by
  intro v hv hvπ
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hv
  have h1 := (hP.2 r).1 (List.mem_append_right _ hr)
  have hc : r ∈ cls p π :=
    mem_cls.2 ⟨lift p r, hvπ, lift_mod hp h1.1, half_lift hp h1.1⟩
  exact (List.nodup_append.1 hP.1).2.2 r hc r hr rfl

theorem part_cover : ∀ v, 1 ≤ v → v ≤ N → v % 2 = p → v ∈ π ∨ v ∈ s₁.map (lift p) := by
  intro v h1 h2 h3
  have hm := (hP.2 (half v)).2 (by simp only [half]; omega)
  rcases List.mem_append.1 hm with hm | hm
  · obtain ⟨x, hx, hxp, e⟩ := mem_cls.1 hm
    left
    have : x = v := by simp only [half] at e; omega
    exact this ▸ hx
  · right
    exact List.mem_map.2 ⟨half v, hm, lift_half h3⟩

theorem part_nodup : (s₁.map (lift p)).Nodup :=
  ((List.nodup_append.1 hP.1).2.1).map (lift_inj hp)

omit hp in
theorem part_one_le : ∀ r ∈ cls p π ++ s₁, 1 ≤ r := fun r hr => ((hP.2 r).1 hr).1

end classPart

/-- **Theorem E, "if"**: the explicit completion `π ++ (rest of σ) ++ (rest of τ)`. -/
theorem ext_of_cond {N w : ℕ} {π t : List ℕ} (hπ : π = w :: t) (hnd : π.Nodup)
    (hr : ∀ v ∈ π, 1 ≤ v ∧ v ≤ N) (hA : CondA N w π) (hB : CondB N w π)
    (hD : Ext ((N + w % 2) / 2) (cls (w % 2) π))
    (hC : Ext ((N + (1 - w % 2)) / 2) (cls (1 - w % 2) π)) : Ext N π := by
  obtain ⟨s₁, hP₁, hap₁⟩ := hD
  obtain ⟨s₂, hP₂, hap₂⟩ := hC
  have hp1 : w % 2 ≤ 1 := by omega
  have hq1 : 1 - w % 2 ≤ 1 := by omega
  set A := s₁.map (lift (w % 2)) with hAdef
  set B := s₂.map (lift (1 - w % 2)) with hBdef
  have rA := part_range hp1 hP₁
  have rB := part_range hq1 hP₂
  have dA := part_disj hp1 hP₁
  have dB := part_disj hq1 hP₂
  have cA := part_cover hp1 hP₁
  have cB := part_cover hq1 hP₂
  have hnd' : (π ++ (A ++ B)).Nodup := by
    refine List.nodup_append.2 ⟨hnd, List.nodup_append.2 ⟨part_nodup hp1 hP₁,
      part_nodup hq1 hP₂, ?_⟩, ?_⟩
    · intro x hx y hy e
      have := (rA x hx).2.2; have := (rB y hy).2.2; omega
    · intro x hx y hy e
      subst e
      rcases List.mem_append.1 hy with hy | hy
      · exact dA x hy hx
      · exact dB x hy hx
  have hI : ∀ v, v ∈ π ++ (A ++ B) ↔ 1 ≤ v ∧ v ≤ N := by
    intro v
    simp only [List.mem_append]
    constructor
    · rintro (h | h | h)
      · exact hr v h
      · exact ⟨(rA v h).1, (rA v h).2.1⟩
      · exact ⟨(rB v h).1, (rB v h).2.1⟩
    · rintro ⟨h1, h2⟩
      by_cases hv : v % 2 = w % 2
      · rcases cA v h1 h2 hv with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases cB v h1 h2 (by omega) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
  have ha : π ++ (A ++ B) = w :: (t ++ (A ++ B)) := by rw [hπ]; rfl
  refine ⟨A ++ B, ⟨hnd', hI⟩, (merge_iff ha hnd' hI).2 ⟨?_, ?_, ?_⟩⟩
  · have e1 : A.filter (fun v => decide (v % 2 = w % 2)) = A :=
      List.filter_eq_self.2 fun v hv => by simpa using (rA v hv).2.2
    have e2 : B.filter (fun v => decide (v % 2 = w % 2)) = [] :=
      List.filter_eq_nil_iff.2 fun v hv => by have := (rB v hv).2.2; simp; omega
    rw [List.filter_append, List.filter_append, e1, e2, List.append_nil, ← map_lift_cls,
      hAdef, ← List.map_append]
    exact apf_map_lift hp1 (part_one_le hP₁) hap₁
  · rw [filter_ne_eq]
    have e1 : A.filter (fun v => decide (v % 2 = 1 - w % 2)) = [] :=
      List.filter_eq_nil_iff.2 fun v hv => by have := (rA v hv).2.2; simp; omega
    have e2 : B.filter (fun v => decide (v % 2 = 1 - w % 2)) = B :=
      List.filter_eq_self.2 fun v hv => by simpa using (rB v hv).2.2
    rw [List.filter_append, List.filter_append, e1, e2, List.nil_append, ← map_lift_cls,
      hBdef, ← List.map_append]
    exact apf_map_lift hq1 (part_one_le hP₂) hap₂
  · intro y u hy hu hyw huw hl
    simp only [List.mem_append] at hy hu
    rcases hy with hy | hy | hy
    · rcases hu with hu | hu | hu
      · exact bef_append_left (hA y hy u hu hyw huw hl)
      · exact absurd (rA u hu).2.2 huw
      · exact bef_append_mid hy (List.mem_append_right _ hu)
    · rcases hu with hu | hu | hu
      · exact absurd hl (hB u hu y (List.mem_range'_1.2 ⟨(rA y hy).1, by
          have := (rA y hy).2.1; omega⟩) (dA y hy) hyw huw)
      · exact absurd (rA u hu).2.2 huw
      · exact bef_append_right (bef_append_mid hy hu)
    · exact absurd (rB y hy).2.2 (by omega)

/-- **Theorem E (the extension test).**  A nonempty list `π = w :: t` of distinct elements
of `[1, N]` is a prefix of a 3-AP-free permutation of `[1, N]` iff
(a) `D` precedes `C` on linked pairs inside `π`, (b) no `C`-entry of `π` is linked to a
`D`-value outside `π`, and (c), (d) the two rescaled parity subsequences of `π` are
extendable in their own (rescaled) classes `[1, ⌊(N + p)/2⌋]`. -/
theorem ext_iff_cond {N w : ℕ} {π t : List ℕ} (hπ : π = w :: t) (hnd : π.Nodup)
    (hr : ∀ v ∈ π, 1 ≤ v ∧ v ≤ N) :
    Ext N π ↔ CondA N w π ∧ CondB N w π ∧ Ext ((N + w % 2) / 2) (cls (w % 2) π) ∧
      Ext ((N + (1 - w % 2)) / 2) (cls (1 - w % 2) π) :=
  ⟨ext_imp hπ, fun ⟨hA, hB, hD, hC⟩ => ext_of_cond hπ hnd hr hA hB hD hC⟩

/-- Every `N` has a 3-AP-free permutation, and for `N ≥ 1` one starting with `1`. -/
theorem ext_nil_one : ∀ N, Ext N [] ∧ (1 ≤ N → Ext N [1]) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases (show N = 0 ∨ N = 1 ∨ 2 ≤ N by omega) with rfl | rfl | hN
  · exact ⟨ext_zero, fun h => absurd h (by omega)⟩
  · exact ⟨(show Ext 1 ([] ++ [1]) from ext_one).of_append, fun _ => ext_one⟩
  · have h1 : Ext N [1] := by
      refine ext_of_cond (w := 1) (t := []) rfl (by simp) (by simp; omega) ?_ ?_ ?_ ?_
      · intro y hy u hu _ huw; simp at hu; omega
      · intro u hu y _ _ _ huw; simp at hu; omega
      · have : cls (1 % 2) [1] = [1] := by decide
        rw [this]; exact (ih _ (by omega)).2 (by omega)
      · have : cls (1 - 1 % 2) [1] = [] := by decide
        rw [this]; exact (ih _ (by omega)).1
    exact ⟨(show Ext N ([] ++ [1]) from h1).of_append, fun _ => h1⟩

theorem ext_nil (N : ℕ) : Ext N [] := (ext_nil_one N).1

/-! ## A decision procedure for extendability (Theorem E as an algorithm) -/

/-- The recursive extension test of Theorem E (with fuel `f ≥ N`). -/
def extB : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => true
  | _ + 1, _, [] => true
  | f + 1, N, w :: t =>
    if N ≤ 1 then true else
      decide (CondA N w (w :: t)) && decide (CondB N w (w :: t)) &&
      extB f ((N + w % 2) / 2) (cls (w % 2) (w :: t)) &&
      extB f ((N + (1 - w % 2)) / 2) (cls (1 - w % 2) (w :: t))

theorem extB_iff : ∀ f N π, N ≤ f → π.Nodup → (∀ v ∈ π, 1 ≤ v ∧ v ≤ N) →
    (extB f N π = true ↔ Ext N π) := by
  intro f
  induction f with
  | zero =>
    intro N π hN hnd hr
    simp only [extB, true_iff]
    exact ext_of_le_one (by omega) hnd hr
  | succ f ih =>
    intro N π hN hnd hr
    rcases π with _ | ⟨w, t⟩
    · simp only [extB, true_iff]; exact ext_nil N
    by_cases h1 : N ≤ 1
    · simp only [extB, h1, ite_true, true_iff]; exact ext_of_le_one h1 hnd hr
    simp only [extB, h1, ite_false, Bool.and_eq_true, decide_eq_true_eq]
    rw [ext_iff_cond rfl hnd hr, ih _ _ (by omega) (cls_nodup hnd) (cls_range (by omega) hr),
      ih _ _ (by omega) (cls_nodup hnd) (cls_range (by omega) hr)]
    tauto

/-! ### Exhaustive search for long extendable prefixes inside a top segment -/

/-- `noLong K a d π`: no extension of `π` by `d` further values from the top segment
`(K - a, K]` is extendable (depth-first search, pruned by extendability). -/
def noLong (K a : ℕ) : ℕ → List ℕ → Bool
  | 0, _ => false
  | d + 1, π => (List.range' (K + 1 - a) a).all fun v =>
      decide (v ∈ π) || !extB K K (π ++ [v]) || noLong K a d (π ++ [v])

theorem noLong_spec {K a : ℕ} : ∀ d π, noLong K a d π = true → ∀ ρ : List ℕ, ρ.length = d →
    (∀ v ∈ ρ, K < v + a) → ¬ Ext K (π ++ ρ) := by
  intro d
  induction d with
  | zero => intro π h; simp [noLong] at h
  | succ d ih =>
    intro π h ρ hl htop hE
    rcases ρ with _ | ⟨v, ρ'⟩
    · simp at hl
    have hE' : Ext K ((π ++ [v]) ++ ρ') := by simpa using hE
    have hv := hE.range v (by simp)
    have hvπ : v ∉ π := by
      have := hE.nodup
      rw [List.nodup_append] at this
      exact fun hv' => this.2.2 v hv' v (by simp) rfl
    have hB : extB K K (π ++ [v]) = true :=
      (extB_iff K K _ le_rfl hE'.of_append.nodup hE'.of_append.range).2 hE'.of_append
    simp only [noLong, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at h
    have hvt := htop v (by simp)
    rcases h v (List.mem_range'_1.2 ⟨by omega, by omega⟩) with (h | h) | h
    · exact hvπ h
    · rw [hB] at h; exact absurd h (by decide)
    · exact ih _ h ρ' (by simpa using hl) (fun x hx => htop x (by simp [hx])) hE'

/-- A successful search bounds every extendable prefix inside the top segment by `6`. -/
theorem le_six_of_noLong {K a : ℕ} (h : noLong K a 7 [] = true) {π : List ℕ} (hE : Ext K π)
    (htop : ∀ v ∈ π, K < v + a) : π.length ≤ 6 := by
  by_contra hl
  refine noLong_spec 7 [] h (π.take 7) (by simp; omega)
    (fun v hv => htop v (List.mem_of_mem_take hv)) ?_
  exact hE.of_prefix (by simpa using List.take_prefix 7 π)


end SymStructure2
end Folds
