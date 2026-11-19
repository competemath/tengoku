import Tengoku
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.Perm
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
**The `Cperm = C` bridge** (the manuscript's own Prop 2.1-style cycle-index identification),
flagged throughout this codebase as "not re-derived here" since `StrongTwoAdic.lean`. Proved
here in full: `Cperm n = C n` for every `n`, i.e. the permutation-native cycle-index sum
(`Perm.lean`, literal sum over `Equiv.Perm (Fin n)`) and the abstract cycle-index polynomial
(`Basic.lean`, falling-factorial recurrence) are the *same* object.

**Proof strategy**: show `Cperm` satisfies `C`'s own defining recurrence (`C_succ`), via a
genuine combinatorial bijection — the manuscript's own "expose the cycle containing a
distinguished point" decomposition (`Basic.lean`'s docstring / the `Remark` after
`prop:recurrence`), formalized here directly on permutations for the first time in this
codebase:
```
  Equiv.Perm (Fin (m+1)) ≃ Σ r ≤ m, (ordered r-tuple of points ≠ 0) × Equiv.Perm (remaining m-r points)
```
via `g ↦ (r, the cycle of `0` in `g` as an ordered tuple, `g` restricted to the complement)`.
Built from `List.formPerm` (the cyclic permutation of a list) and `Equiv.Perm.toList`/
`Equiv.Perm.formPerm_toList` (Mathlib's list-cycle correspondence), plus `Equiv.Perm.ofSubtype`/
`subtypePerm` for the disjoint complement gluing. `CycleTuple m r := Fin r ↪ NZ m` (the tuple),
`CycleCompl m r t` (the complement predicate), `gAssemble` (the assembled permutation),
`ci_gAssemble` (its cycle-indicator monomial is exactly `X_{r+1} * ci h`), and
`exists_decomp_zero`/`exists_decomp_pos` + `gAssemble_injective_zero`/`_pos` (existence and
uniqueness of the decomposition) combine via `Finset.sum_bij` and `Fintype.sum_sigma` into
`Cperm_succ_alt`, which has *exactly* `C_succ`'s recursive form. `Cperm_eq_C` then follows by
the same strong induction that defines `C`.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm MvPolynomial

open scoped Classical

variable (m r : ℕ)

/-- The `m`-element subtype of points other than `0`.-/
abbrev NZ (m : ℕ) := {x : Fin (m + 1) // x ≠ 0}

/--
@isnad1 id=eq.0h1v.s7.fb93fb87765e from=translated src=- shape=47dcad53 vocab=0616d525
-/
theorem card_NZ (m : ℕ) : Fintype.card (NZ m) = m := by
  unfold NZ; rw [Fintype.card_subtype_compl]; simp

/-- Tuples of `r` distinct points of `Fin (m+1)`, all different from `0` — the data of an
ordered listing of the `r` points that, together with `0`, form the cycle of `0`.-/
abbrev CycleTuple (m r : ℕ) := Fin r ↪ NZ m

noncomputable instance : Fintype (CycleTuple m r) := by unfold CycleTuple; infer_instance

/--
@isnad1 id=eq.0h2v.s4.ef8c7655a5e6 from=translated src=- shape=26a905d5 vocab=25104a4c
-/
theorem card_CycleTuple : Fintype.card (CycleTuple m r) = m.descFactorial r := by
  unfold CycleTuple
  rw [Fintype.card_embedding_eq, card_NZ, Fintype.card_fin]

/-- Complement predicate: points other than `0` and not among the tuple's values — the points
left over after removing the cycle through `0`.-/
def CycleCompl (t : CycleTuple m r) (x : Fin (m + 1)) : Prop :=
  x ≠ 0 ∧ ∀ i, (t i : Fin (m + 1)) ≠ x

noncomputable instance (t : CycleTuple m r) : Fintype {x // CycleCompl m r t x} :=
  Fintype.ofFinite _

/--
@isnad1 id=eq.1h3v.s6.896e0e1326c3 from=translated src=- shape=f28fb72c vocab=0e791b22
-/
theorem card_CycleCompl (t : CycleTuple m r) (hr : r ≤ m) :
    Fintype.card {x : Fin (m + 1) // CycleCompl m r t x} = m - r := by
  rw [Fintype.card_subtype]
  have hsub : (Finset.univ.filter (CycleCompl m r t)) =
      (Finset.univ.filter (fun x : Fin (m + 1) => x ≠ 0)) \
        (Finset.univ.image (fun i : Fin r => (t i : Fin (m + 1)))) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_image]
    unfold CycleCompl
    constructor
    · rintro ⟨hx0, hxt⟩
      refine ⟨hx0, ?_⟩
      rintro ⟨i, hi⟩
      exact hxt i hi
    · rintro ⟨hx0, hxt⟩
      refine ⟨hx0, ?_⟩
      intro i hi
      exact hxt ⟨i, hi⟩
  have himg_subset : (Finset.univ.image (fun i : Fin r => (t i : Fin (m + 1)))) ⊆
      (Finset.univ.filter (fun x : Fin (m + 1) => x ≠ 0)) := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨i, _, hi⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hi]
    exact (t i).2
  rw [hsub, Finset.card_sdiff, Finset.inter_eq_left.mpr himg_subset]
  rw [Finset.card_image_of_injective _ (fun i j hij => t.injective (Subtype.ext hij))]
  rw [Finset.card_univ, Fintype.card_fin]
  have hcard0 : (Finset.univ.filter (fun x : Fin (m + 1) => x ≠ 0)).card = m := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0)]
    simp
  rw [hcard0]

/-- The list `[0, t 0, t 1, ..., t (r-1)]`.-/
def cycleList (t : CycleTuple m r) : List (Fin (m + 1)) :=
  0 :: List.ofFn (fun i => (t i : Fin (m + 1)))

/--
@isnad1 id=eq.0h3v.s5.b898e80823c9 from=translated src=- shape=f57bfc8e vocab=eb933a8f
-/
theorem cycleList_length (t : CycleTuple m r) : (cycleList m r t).length = r + 1 := by
  simp [cycleList]

/--
@isnad1 id=nodup.0h3v.s4.f43cf36c954d from=translated src=- shape=575bb733 vocab=deab9d70
-/
theorem cycleList_nodup (t : CycleTuple m r) : (cycleList m r t).Nodup := by
  simp only [cycleList, List.nodup_cons, List.mem_ofFn]
  refine ⟨?_, List.nodup_ofFn.mpr (fun i j hij => t.injective (Subtype.ext hij))⟩
  rintro ⟨i, hi⟩
  exact (t i).2 hi

/-- The `(r+1)`-cycle `(0, t 0, t 1, ..., t (r-1))`, or the identity when `r = 0`.-/
def cyc (t : CycleTuple m r) : Equiv.Perm (Fin (m + 1)) := List.formPerm (cycleList m r t)

/--
@isnad1 id=le.0h3v.s7.bdf91d3ddbe5 from=translated src=- shape=72e268cd vocab=eb56d813
-/
theorem cyc_support_subset (t : CycleTuple m r) :
    (cyc m r t).support ⊆ (cycleList m r t).toFinset := by
  intro x hx
  rw [Equiv.Perm.mem_support] at hx
  by_contra hxnot
  rw [List.mem_toFinset] at hxnot
  exact hx (List.formPerm_apply_of_notMem hxnot)

/--
@isnad1 id=disjoint.0h4v.s9.1730b2385c08 from=translated src=- shape=15ea737c vocab=429afa91
-/
theorem cyc_disjoint_ofSubtype (t : CycleTuple m r) (h : Equiv.Perm {x // CycleCompl m r t x}) :
    Disjoint (cyc m r t) (Equiv.Perm.ofSubtype h) := by
  rw [Equiv.Perm.disjoint_iff_disjoint_support]
  apply Finset.disjoint_left.mpr
  intro x hxc hxo
  have hxc' : x ∈ (cycleList m r t).toFinset := cyc_support_subset m r t hxc
  rw [List.mem_toFinset] at hxc'
  obtain ⟨hp, _⟩ := (Equiv.Perm.mem_support_ofSubtype x h).mp hxo
  simp only [cycleList, List.mem_cons, List.mem_ofFn] at hxc'
  rcases hxc' with h0 | ⟨i, hi⟩
  · exact hp.1 h0
  · exact hp.2 i hi

/--
@isnad1 id=iscycle.1h3v.s5.605287419d03 from=translated src=- shape=465c355a vocab=49aef750
-/
theorem cyc_isCycle_of_pos (t : CycleTuple m r) (hr : 1 ≤ r) : IsCycle (cyc m r t) :=
  List.isCycle_formPerm (cycleList_nodup m r t) (by rw [cycleList_length]; omega)

/--
@isnad1 id=eq.1h3v.s6.0fd01e5fb277 from=translated src=- shape=836ca81d vocab=eb56d813
-/
theorem cyc_support_eq (t : CycleTuple m r) (hr : 1 ≤ r) :
    (cyc m r t).support = (cycleList m r t).toFinset := by
  apply List.support_formPerm_of_nodup _ (cycleList_nodup m r t)
  intro x hx
  have hlen := cycleList_length m r t
  rw [hx] at hlen
  simp at hlen
  omega

/--
@isnad1 id=ne.1h3v.s7.4106bddddb4a from=translated src=- shape=26abdfd7 vocab=2e801b83
-/
theorem cyc_apply_zero_ne_zero (t : CycleTuple m r) (hr : 1 ≤ r) : cyc m r t 0 ≠ 0 := by
  have hsupp : (0 : Fin (m + 1)) ∈ (cyc m r t).support := by
    rw [cyc_support_eq m r t hr]; simp [cycleList]
  exact (Equiv.Perm.mem_support.mp hsupp)

/--
@isnad1 id=eq.0h2v.s6.f55673172df2 from=translated src=- shape=f971882f vocab=6078ef88
-/
theorem cyc_eq_one_of_zero (t : CycleTuple m 0) : cyc m 0 t = 1 := by
  unfold cyc cycleList; simp

/--
@isnad1 id=iff.0h4v.s7.ef39a6bd5176 from=translated src=- shape=d2a7ac55 vocab=f02f717f
-/
theorem not_CycleCompl_iff (t : CycleTuple m r) (x : Fin (m + 1)) :
    ¬ CycleCompl m r t x ↔ (x = 0 ∨ ∃ i, (t i : Fin (m + 1)) = x) := by
  unfold CycleCompl
  constructor
  · intro h
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      by_contra hcontra
      push_neg at hcontra
      exact h ⟨hx0, hcontra⟩
  · rintro (rfl | ⟨i, hi⟩) ⟨hx0, hall⟩
    · exact hx0 rfl
    · exact hall i hi

/--
@isnad1 id=iff.1h4v.s7.65eb34925de3 from=translated src=- shape=3944dbc7 vocab=1de504e9
-/
theorem mem_support_cyc_iff (t : CycleTuple m r) (hr : 1 ≤ r) (x : Fin (m + 1)) :
    x ∈ (cyc m r t).support ↔ ¬ CycleCompl m r t x := by
  rw [cyc_support_eq m r t hr, List.mem_toFinset]
  simp only [cycleList, List.mem_cons, List.mem_ofFn]
  rw [not_CycleCompl_iff]

/-- The permutation assembled from a cycle-tuple `t` (the cycle through `0`) and a permutation
`h` of the complement.-/
noncomputable def gAssemble (t : CycleTuple m r) (h : Equiv.Perm {x // CycleCompl m r t x}) :
    Equiv.Perm (Fin (m + 1)) := cyc m r t * Equiv.Perm.ofSubtype h

/--
@isnad1 id=eq.0h3v.s8.021abcf0ff77 from=translated src=- shape=d11d7358 vocab=b12e8d79
-/
theorem gAssemble_cycleType_zero (t : CycleTuple m 0) (h : Equiv.Perm {x // CycleCompl m 0 t x}) :
    (gAssemble m 0 t h).cycleType = h.cycleType := by
  unfold gAssemble
  rw [cyc_eq_one_of_zero m t, one_mul, Equiv.Perm.cycleType_ofSubtype]

/--
@isnad1 id=eq.1h4v.s8.66f1c9629371 from=translated src=- shape=69b7fa97 vocab=5f34c214
-/
theorem gAssemble_cycleType_pos (t : CycleTuple m r) (h : Equiv.Perm {x // CycleCompl m r t x})
    (hpos : 1 ≤ r) :
    (gAssemble m r t h).cycleType = {r + 1} + h.cycleType := by
  have hdisj := cyc_disjoint_ofSubtype m r t h
  have hcyc : (cyc m r t).cycleType = {r + 1} := by
    have hic : IsCycle (cyc m r t) := cyc_isCycle_of_pos m r t hpos
    rw [Equiv.Perm.IsCycle.cycleType hic, cyc_support_eq m r t hpos,
      List.toFinset_card_of_nodup (cycleList_nodup m r t), cycleList_length]
  unfold gAssemble
  rw [hdisj.cycleType_mul, hcyc, Equiv.Perm.cycleType_ofSubtype]

/-- The cycle-indicator monomial of an assembled permutation is `X_{r+1}` times that of the
complement permutation `h` — matching the manuscript's "assign weight `w_{r+1}`" remark.
@isnad1 id=eq.1h4v.s8.4bdc249f3cd8 from=translated src=- shape=74956061 vocab=179954fa
-/
theorem ci_gAssemble (hr : r ≤ m) (t : CycleTuple m r) (h : Equiv.Perm {x // CycleCompl m r t x}) :
    ci (gAssemble m r t h) = X (r + 1) * ci h := by
  unfold ci
  rw [show (Fintype.card (Fin (m + 1)) : ℕ) = m + 1 by simp]
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0
    rw [gAssemble_cycleType_zero m t h]
    have hcardcompl : Fintype.card {x : Fin (m + 1) // CycleCompl m 0 t x} = m :=
      card_CycleCompl m 0 t hr
    rw [hcardcompl]
    rw [show m + 1 - h.cycleType.sum = 1 + (m - h.cycleType.sum) by
      have hle : h.cycleType.sum ≤ m := by
        rw [Equiv.Perm.sum_cycleType]
        have := Finset.card_le_univ h.support
        rwa [hcardcompl] at this
      omega]
    rw [pow_add, pow_one]
    ring
  · rw [gAssemble_cycleType_pos m r t h hpos]
    have hcardcompl : Fintype.card {x : Fin (m + 1) // CycleCompl m r t x} = m - r :=
      card_CycleCompl m r t hr
    rw [hcardcompl]
    have hle : h.cycleType.sum ≤ m - r := by
      rw [Equiv.Perm.sum_cycleType]
      have := Finset.card_le_univ h.support
      rwa [hcardcompl] at this
    rw [Multiset.sum_add, Multiset.sum_singleton]
    rw [show m + 1 - (r + 1 + h.cycleType.sum) = (m - r) - h.cycleType.sum by omega]
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_singleton, Multiset.prod_singleton]
    ring

/-- Recovering the tuple: the cycle of `0` in an assembled permutation is exactly `cyc t`.
@isnad1 id=eq.1h4v.s7.216da56ea714 from=translated src=- shape=bdfc7e7d vocab=2f5d8fd5
-/
theorem cycleOf_gAssemble (t : CycleTuple m r) (h : Equiv.Perm {x // CycleCompl m r t x})
    (hr1 : 1 ≤ r) :
    (gAssemble m r t h).cycleOf 0 = cyc m r t := by
  unfold gAssemble
  have hdisj := cyc_disjoint_ofSubtype m r t h
  have hcomm : Commute (cyc m r t) (Equiv.Perm.ofSubtype h) := hdisj.commute
  have h0fix : (Equiv.Perm.ofSubtype h) 0 = 0 := by
    apply Equiv.Perm.ofSubtype_apply_of_not_mem
    simp [CycleCompl]
  rw [Equiv.Perm.cycleOf_mul_of_apply_right_eq_self hcomm 0 h0fix]
  exact Equiv.Perm.IsCycle.cycleOf_eq (cyc_isCycle_of_pos m r t hr1) (cyc_apply_zero_ne_zero m r t hr1)

/--
@isnad1 id=eq.2h4v.s5.68547d4b11c6 from=translated src=- shape=80cb0d6c vocab=ebc08644
-/
theorem cyc_injective (hr1 : 1 ≤ r) (t1 t2 : CycleTuple m r) (heq : cyc m r t1 = cyc m r t2) :
    t1 = t2 := by
  have hl1 : 2 ≤ (cycleList m r t1).length := by rw [cycleList_length]; omega
  have hl2 : 2 ≤ (cycleList m r t2).length := by rw [cycleList_length]; omega
  have hget1 : (cycleList m r t1).get ⟨0, by omega⟩ = 0 := by simp [cycleList]
  have hget2 : (cycleList m r t2).get ⟨0, by omega⟩ = 0 := by simp [cycleList]
  have h1 := Equiv.Perm.toList_formPerm_nontrivial (cycleList m r t1) hl1 (cycleList_nodup m r t1)
  have h2 := Equiv.Perm.toList_formPerm_nontrivial (cycleList m r t2) hl2 (cycleList_nodup m r t2)
  rw [hget1] at h1
  rw [hget2] at h2
  have hcl : cycleList m r t1 = cycleList m r t2 := by
    rw [← h1, ← h2]; unfold cyc at heq; rw [heq]
  have hofFn : (fun i => (t1 i : Fin (m + 1))) = (fun i => (t2 i : Fin (m + 1))) := by
    have hc : List.ofFn (fun i => (t1 i : Fin (m + 1))) =
        List.ofFn (fun i => (t2 i : Fin (m + 1))) := by
      simpa [cycleList] using hcl
    exact List.ofFn_inj.mp hc
  apply Function.Embedding.ext
  intro i
  exact Subtype.ext (congrFun hofFn i)

/--
@isnad1 id=ex.2h6v.s7.67b331db906b from=translated src=- shape=38a2a2c3 vocab=be21b6e3
-/
theorem gAssemble_injective_pos (hr1 : 1 ≤ r) (t1 t2 : CycleTuple m r)
    (h1 : Equiv.Perm {x // CycleCompl m r t1 x}) (h2 : Equiv.Perm {x // CycleCompl m r t2 x})
    (heq : gAssemble m r t1 h1 = gAssemble m r t2 h2) :
    ∃ ht : t1 = t2, ht ▸ h1 = h2 := by
  have hcyceq : cyc m r t1 = cyc m r t2 := by
    rw [← cycleOf_gAssemble m r t1 h1 hr1, ← cycleOf_gAssemble m r t2 h2 hr1, heq]
  have ht : t1 = t2 := cyc_injective m r hr1 t1 t2 hcyceq
  subst ht
  refine ⟨rfl, ?_⟩
  simp only [eq_mpr_eq_cast, cast_eq]
  have hofsub : Equiv.Perm.ofSubtype h1 = Equiv.Perm.ofSubtype h2 := by
    have := heq
    unfold gAssemble at this
    exact mul_left_cancel this
  exact Equiv.Perm.ofSubtype_injective hofsub

/-- If a permutation fixes everything outside a predicate `p`, then `p` is invariant under it —
the general fact behind gluing a "cycle part" and a "complement part" back into one
`subtypePerm`.
@isnad1 id=iff.1h4v.s5.955dafc29807 from=translated src=- shape=261585b6 vocab=26837e6f
-/
theorem invariant_of_fixes_compl {α : Type*} {f : Equiv.Perm α} {p : α → Prop}
    (hfix : ∀ x, ¬ p x → f x = x) : ∀ x, p (f x) ↔ p x := by
  intro x
  by_cases hpx : p x
  · constructor
    · intro _; exact hpx
    · intro _
      by_contra hpfx
      have h1 : f (f x) = f x := hfix (f x) hpfx
      have h3 : x = f x := f.injective h1.symm
      rw [← h3] at hpfx
      exact hpfx hpx
  · rw [hfix x hpx]

/--
@isnad1 id=eq.2h3v.s7.73d294bf8a27 from=translated src=- shape=c349686b vocab=bd85f7ed
-/
theorem ofSubtype_subtypePerm_eq_self {α : Type*} [DecidableEq α] {p : α → Prop} [DecidablePred p]
    (f : Equiv.Perm α) (hf : ∀ x, p (f x) ↔ p x) (hsupp : ∀ x, ¬ p x → f x = x) :
    Equiv.Perm.ofSubtype (f.subtypePerm hf) = f := by
  ext x
  by_cases hx : p x
  · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx, Equiv.Perm.subtypePerm_apply]
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hx, hsupp x hx]

instance : Subsingleton (CycleTuple m 0) := by
  constructor
  intro t1 t2
  apply Function.Embedding.ext
  intro i
  exact i.elim0

/--
@isnad1 id=ex.1h2v.s8.148b2417ae37 from=translated src=- shape=b28ef4ca vocab=6eb799f5
-/
theorem exists_decomp_zero (g : Equiv.Perm (Fin (m + 1))) (hg0 : g 0 = 0) :
    ∃ (t : CycleTuple m 0) (h : Equiv.Perm {x // CycleCompl m 0 t x}), gAssemble m 0 t h = g := by
  classical
  set t : CycleTuple m 0 := ⟨Fin.elim0, fun {a} _ _ => a.elim0⟩ with ht_def
  have htriv : ∀ x, CycleCompl m 0 t x ↔ x ≠ 0 := by
    intro x
    unfold CycleCompl
    simp
  have hfix : ∀ x, ¬ CycleCompl m 0 t x → g x = x := by
    intro x hx
    rw [htriv] at hx
    simp only [ne_eq, not_not] at hx
    rw [hx, hg0]
  have hinv : ∀ x, CycleCompl m 0 t (g x) ↔ CycleCompl m 0 t x := by
    intro x
    rw [htriv, htriv]
    constructor
    · intro h hcontra
      rw [hcontra, hg0] at h
      exact h rfl
    · intro h hcontra
      apply h
      have heq : g x = g 0 := by rw [hcontra, hg0]
      exact g.injective heq
  refine ⟨t, g.subtypePerm hinv, ?_⟩
  unfold gAssemble
  rw [cyc_eq_one_of_zero m t, one_mul]
  exact ofSubtype_subtypePerm_eq_self g hinv hfix

/--
@isnad1 id=ex.1h5v.s8.96cd6f2ea5fa from=translated src=- shape=e40e2437 vocab=8f0b23a8
-/
theorem gAssemble_injective_zero (t1 t2 : CycleTuple m 0)
    (h1 : Equiv.Perm {x // CycleCompl m 0 t1 x}) (h2 : Equiv.Perm {x // CycleCompl m 0 t2 x})
    (heq : gAssemble m 0 t1 h1 = gAssemble m 0 t2 h2) :
    ∃ ht : t1 = t2, ht ▸ h1 = h2 := by
  have ht : t1 = t2 := Subsingleton.elim t1 t2
  subst ht
  refine ⟨rfl, ?_⟩
  simp only [eq_mpr_eq_cast, cast_eq]
  have hofsub : Equiv.Perm.ofSubtype h1 = Equiv.Perm.ofSubtype h2 := by
    unfold gAssemble at heq
    exact mul_left_cancel heq
  exact Equiv.Perm.ofSubtype_injective hofsub

/--
@isnad1 id=ex.2h3v.s8.18bcb85b2e05 from=translated src=- shape=ad1dec75 vocab=7cc5ccc1
-/
theorem exists_decomp_pos (g : Equiv.Perm (Fin (m + 1))) (hr1 : 1 ≤ r)
    (hcard : (g.cycleOf 0).support.card = r + 1) :
    ∃ (t : CycleTuple m r) (h : Equiv.Perm {x // CycleCompl m r t x}), gAssemble m r t h = g := by
  classical
  set l := g.toList 0 with hl_def
  have hlen : l.length = r + 1 := by rw [hl_def, Equiv.Perm.length_toList, hcard]
  have hnodup : l.Nodup := Equiv.Perm.nodup_toList g 0
  have hg0 : (0 : Fin (m + 1)) ∈ g.support := by
    rw [Equiv.Perm.mem_support]
    intro hz
    rw [(Equiv.Perm.cycleOf_eq_one_iff g).mpr hz] at hcard
    simp at hcard
  have hhead : l[0]'(by omega) = 0 := Equiv.Perm.toList_getElem_zero g 0 hg0
  have htne : ∀ i : Fin r, l[i.1 + 1]'(by omega) ≠ 0 := by
    intro i hcontra
    have heq := hnodup.getElem_inj_iff (i := 0) (hi := by omega) (j := i.1 + 1) (hj := by omega)
    rw [hhead, hcontra] at heq
    have := heq.mp rfl
    omega
  set t : CycleTuple m r :=
    ⟨fun i => ⟨l[i.1 + 1]'(by omega), htne i⟩, by
      intro i j hij
      have hval : l[i.1 + 1]'(by omega) = l[j.1 + 1]'(by omega) := congrArg Subtype.val hij
      have heq := (hnodup.getElem_inj_iff (i := i.1 + 1) (hi := by omega)
        (j := j.1 + 1) (hj := by omega)).mp hval
      exact Fin.ext (by omega)⟩ with ht_def
  have hlist_eq : cycleList m r t = l := by
    apply List.ext_getElem
    · rw [cycleList_length, hlen]
    · intro i h1 h2
      match i with
      | 0 => simpa [cycleList] using hhead.symm
      | (i + 1) =>
        simp only [cycleList] at h1 h2 ⊢
        rw [List.getElem_cons_succ, List.getElem_ofFn]
        rfl
  have hcyc_eq : cyc m r t = g.cycleOf 0 := by
    unfold cyc; rw [hlist_eq, hl_def, Equiv.Perm.formPerm_toList]
  set f := g * (g.cycleOf 0)⁻¹ with hf_def
  have hdisj0 : Disjoint (g * (g.cycleOf 0)⁻¹) (g.cycleOf 0) := by
    apply Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset
    rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]
    exact hg0
  have hdisj : Disjoint f (cyc m r t) := by rw [hf_def, hcyc_eq]; exact hdisj0
  have hfix : ∀ x, ¬ CycleCompl m r t x → f x = x := by
    intro x hx
    have hxsupp : (cyc m r t) x ≠ x :=
      Equiv.Perm.mem_support.mp ((mem_support_cyc_iff m r t hr1 x).mpr hx)
    rcases hdisj x with h1 | h2
    · exact h1
    · exact absurd h2 hxsupp
  have hinv := invariant_of_fixes_compl hfix
  refine ⟨t, f.subtypePerm hinv, ?_⟩
  have hofsub : Equiv.Perm.ofSubtype (f.subtypePerm hinv) = f :=
    ofSubtype_subtypePerm_eq_self f hinv hfix
  unfold gAssemble
  rw [hofsub, hcyc_eq, hf_def]
  have hcomm0 : Commute (g.cycleOf 0) (g * (g.cycleOf 0)⁻¹) := hdisj0.symm.commute
  calc g.cycleOf 0 * (g * (g.cycleOf 0)⁻¹)
      = (g * (g.cycleOf 0)⁻¹) * g.cycleOf 0 := hcomm0
    _ = g * ((g.cycleOf 0)⁻¹ * g.cycleOf 0) := by rw [mul_assoc]
    _ = g := by simp

/--
@isnad1 id=eq.0h4v.s8.cec6f1977714 from=translated src=- shape=7439c9df vocab=2c891036
-/
theorem rCard_gAssemble (t : CycleTuple m r) (h : Equiv.Perm {x // CycleCompl m r t x}) :
    ((gAssemble m r t h).cycleOf 0).support.card = if r = 0 then 0 else r + 1 := by
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0
    rw [ite_eq_left rfl]
    have hg0 : (gAssemble m 0 t h) 0 = 0 := by
      unfold gAssemble
      rw [cyc_eq_one_of_zero m t, one_mul]
      apply Equiv.Perm.ofSubtype_apply_of_not_mem
      simp [CycleCompl]
    rw [(Equiv.Perm.cycleOf_eq_one_iff _).mpr hg0]
    simp
  · rw [ite_eq_right (by omega), cycleOf_gAssemble m r t h hpos, cyc_support_eq m r t hpos,
      List.toFinset_card_of_nodup (cycleList_nodup m r t), cycleList_length]

/--
@isnad1 id=eq.1h7v.s6.157fdff2bae5 from=translated src=- shape=54901b2b vocab=5a9e18d4
-/
theorem r_eq_of_gAssemble_eq (t1 : CycleTuple m r) (t2 : CycleTuple m r')
    (h1 : Equiv.Perm {x // CycleCompl m r t1 x}) (h2 : Equiv.Perm {x // CycleCompl m r' t2 x})
    (heq : gAssemble m r t1 h1 = gAssemble m r' t2 h2) : r = r' := by
  have e1 := rCard_gAssemble m r t1 h1
  have e2 := rCard_gAssemble m r' t2 h2
  rw [heq] at e1
  rw [e1] at e2
  by_cases hr : r = 0 <;> by_cases hr' : r' = 0 <;> simp [hr, hr'] at e2 <;> omega

/-- Cycle type is invariant under transporting a permutation across any equivalence of the
ambient finite type.
@isnad1 id=eq.0h4v.s6.ac46bb9c00e9 from=translated src=- shape=c44a43b3 vocab=e1b0fd3c
-/
theorem cycleType_permCongr {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (e : β ≃ γ) (g : Equiv.Perm β) : (e.permCongr g).cycleType = g.cycleType := by
  set f : β ≃ Subtype (fun _ : γ => True) :=
    e.trans (Equiv.subtypeUnivEquiv fun _ => trivial).symm with hf
  have hext : g.extendDomain f = e.permCongr g := by
    ext x
    rw [Equiv.Perm.extendDomain_apply_subtype g f trivial]
    simp [hf, Equiv.permCongr_apply]
  rw [← hext, Equiv.Perm.cycleType_extendDomain]

/-- The cycle-indicator monomial is invariant under transporting a permutation across any
equivalence of the ambient finite type.
@isnad1 id=eq.0h4v.s6.8c03544386da from=translated src=- shape=3124445b vocab=f02fbd8f
-/
theorem ci_permCongr {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (e : β ≃ γ) (g : Equiv.Perm β) : ci (e.permCongr g) = ci g := by
  unfold ci
  rw [cycleType_permCongr e g, Fintype.card_congr e.symm]

/-- The `Cperm`-sum over any Fintype `β` of cardinality `n` equals `Cperm n` — lets `Cperm`'s
defining sum be computed over any finite type of the right size, not just `Fin n` itself.
@isnad1 id=eq.1h2v.s5.b500103fffad from=translated src=- shape=c42d664d vocab=2bbd4c02
-/
theorem Cperm_eq_sum_of_card_eq {β : Type*} [Fintype β] [DecidableEq β] {n : ℕ}
    (hβ : Fintype.card β = n) : Cperm n = ∑ g : Equiv.Perm β, ci g := by
  subst hβ
  have e : β ≃ Fin (Fintype.card β) := Fintype.equivFin β
  unfold Cperm
  exact (Fintype.sum_equiv e.permCongr (fun h : Equiv.Perm β => ci h)
    (fun g : Equiv.Perm (Fin (Fintype.card β)) => ci g)
    (fun h => (ci_permCongr e h).symm)).symm

/--
@isnad1 id=eq.1h2v.s4.10967f41d2f5 from=translated src=- shape=8ec67f47 vocab=8d53d620
-/
theorem fall_eq_descFactorial_nat (n s : ℕ) (hs : s ≤ n) :
    (fall n s : ℤ) = (n.descFactorial s : ℤ) := by
  rw [fall, Nat.descFactorial_eq_prod_range]
  push_cast
  apply Finset.prod_congr rfl
  intro i hi
  have his : i < s := Finset.mem_range.mp hi
  have : i ≤ n := by omega
  omega

/-- **`Cperm` satisfies `C`'s own recurrence** (`C_succ`, `Basic.lean`): the manuscript's
"distinguished-point" decomposition, proved directly for the permutation-native cycle-index
sum via the bijection `gAssemble`/`exists_decomp_*`/`gAssemble_injective_*` above.
@isnad1 id=eq.0h1v.s7.62f12d1d7932 from=translated src=- shape=ad8c62e1 vocab=f120e1ce
-/
theorem Cperm_succ_alt (m : ℕ) :
    Cperm (m + 1) =
      ∑ s ∈ Finset.range (m + 1), (fall m s : MvPolynomial ℕ ℤ) * (X (s + 1) * Cperm (m - s)) := by
  classical
  have hCperm : Cperm (m + 1) = ∑ g : Equiv.Perm (Fin (m + 1)), ci g :=
    Cperm_eq_sum_of_card_eq (by simp)
  rw [hCperm]
  have hbij : ∑ g : Equiv.Perm (Fin (m + 1)), ci g =
      ∑ x : (Σ i : Fin (m + 1), Σ t : CycleTuple m i.1, Equiv.Perm {y // CycleCompl m i.1 t y}),
        ci (gAssemble m x.1.1 x.2.1 x.2.2) := by
    symm
    apply Finset.sum_bij (fun x (_ : x ∈ (Finset.univ : Finset (Σ i : Fin (m + 1),
      Σ t : CycleTuple m i.1, Equiv.Perm {y // CycleCompl m i.1 t y}))) =>
      gAssemble m x.1.1 x.2.1 x.2.2)
    · intro a _; exact Finset.mem_univ _
    · rintro ⟨⟨r1, hr1m⟩, t1, h1⟩ _ ⟨⟨r2, hr2m⟩, t2, h2⟩ _ heq
      simp only at heq
      have hreq : r1 = r2 := r_eq_of_gAssemble_eq m r1 t1 t2 h1 h2 heq
      subst hreq
      by_cases hr0 : r1 = 0
      · subst hr0
        obtain ⟨ht, hh⟩ := gAssemble_injective_zero m t1 t2 h1 h2 heq
        subst ht
        simp only [eq_mpr_eq_cast, cast_eq] at hh
        subst hh
        rfl
      · have hrpos : 1 ≤ r1 := by omega
        obtain ⟨ht, hh⟩ := gAssemble_injective_pos m r1 hrpos t1 t2 h1 h2 heq
        subst ht
        simp only [eq_mpr_eq_cast, cast_eq] at hh
        subst hh
        rfl
    · intro g _
      by_cases hg0 : g 0 = 0
      · obtain ⟨t, h, hgh⟩ := exists_decomp_zero m g hg0
        refine ⟨⟨⟨0, by omega⟩, t, h⟩, Finset.mem_univ _, ?_⟩
        exact hgh
      · have hg0supp : (0 : Fin (m + 1)) ∈ g.support := Equiv.Perm.mem_support.mpr hg0
        set r := (g.cycleOf 0).support.card - 1 with hr_def
        have hcardge : 2 ≤ (g.cycleOf 0).support.card :=
          Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hg0supp |>.trans_eq
            (by rw [Equiv.Perm.length_toList])
        have hr1 : 1 ≤ r := by omega
        have hcard : (g.cycleOf 0).support.card = r + 1 := by omega
        have hrm : r < m + 1 := by
          have := Finset.card_le_univ (g.cycleOf 0).support
          simp only [Fintype.card_fin] at this
          omega
        obtain ⟨t, h, hgh⟩ := exists_decomp_pos m r g hr1 hcard
        refine ⟨⟨⟨r, hrm⟩, t, h⟩, Finset.mem_univ _, ?_⟩
        exact hgh
    · intro a _
      rfl
  rw [hbij, Fintype.sum_sigma]
  rw [show (∑ i : Fin (m + 1), ∑ y : (Σ t : CycleTuple m i.1,
        Equiv.Perm {y // CycleCompl m i.1 t y}), ci (gAssemble m i.1 y.1 y.2)) =
      ∑ i : Fin (m + 1), (X (i.1 + 1) : MvPolynomial ℕ ℤ) *
        ∑ t : CycleTuple m i.1, ∑ h : Equiv.Perm {y // CycleCompl m i.1 t y}, ci h by
    apply Finset.sum_congr rfl
    intro i _
    rw [Fintype.sum_sigma]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    have hle : (i.1 : ℕ) ≤ m := by omega
    exact ci_gAssemble m i.1 hle t h]
  have hinner : ∀ i : Fin (m + 1),
      (∑ t : CycleTuple m i.1, ∑ h : Equiv.Perm {y // CycleCompl m i.1 t y}, ci h) =
        (m.descFactorial i.1 : MvPolynomial ℕ ℤ) * Cperm (m - i.1) := by
    intro i
    have hle : (i.1 : ℕ) ≤ m := by omega
    have hstep : ∀ t : CycleTuple m i.1,
        (∑ h : Equiv.Perm {y // CycleCompl m i.1 t y}, ci h) = Cperm (m - i.1) :=
      fun t => (Cperm_eq_sum_of_card_eq (card_CycleCompl m i.1 t hle)).symm
    rw [Finset.sum_congr rfl (fun t _ => hstep t)]
    rw [Finset.sum_const, Finset.card_univ, card_CycleTuple]
    simp [mul_comm]
  simp_rw [hinner]
  rw [Fin.sum_univ_eq_sum_range
      (fun s => (X (s + 1) : MvPolynomial ℕ ℤ) * ((m.descFactorial s : MvPolynomial ℕ ℤ) *
        Cperm (m - s))) (m + 1)]
  apply Finset.sum_congr rfl
  intro s hs
  have hsm : s ≤ m := by have := Finset.mem_range.mp hs; omega
  rw [fall_eq_descFactorial_nat m s hsm]
  push_cast
  ring

/--
@isnad1 id=eq.0h0v.s5.c1fb16099f50 from=translated src=- shape=978b4adc vocab=86699c3a
-/
theorem Cperm_zero : Cperm 0 = 1 := by
  unfold Cperm
  rw [show (Finset.univ : Finset (Equiv.Perm (Fin 0))) = {1} from by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_univ 1, ?_⟩
    intro g _
    apply Equiv.Perm.ext
    intro x
    exact x.elim0]
  simp only [Finset.sum_singleton]
  unfold ci
  simp

/-- **The `Cperm = C` bridge, in full.**
@isnad1 id=eq.0h1v.s3.5066050e8c7b from=translated src=- shape=a951267f vocab=45dab96a
-/
theorem Cperm_eq_C : ∀ n, Cperm n = C n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [Cperm_zero, C_zero]
    | m + 1 =>
      rw [Cperm_succ_alt m, C_succ m]
      apply Finset.sum_congr rfl
      intro s hs
      have hsm : s ≤ m := by have := Finset.mem_range.mp hs; omega
      rw [ih (m - s) (by omega)]

end CongruenceTheory
