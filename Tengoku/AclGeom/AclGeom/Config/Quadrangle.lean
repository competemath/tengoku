/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Config.WitnessTable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The partial quadrangle of the soundness witness

Clause (vi) of Ψ at the table-7.1 witness: the six points
`(S, T, U, S', T', U') = ([a], [c], [ac], [b], [acb], [cb])` form a
partial quadrangle. Their monomial exponent vectors with respect to
`(a, c, b)` are

`(1,0,0), (0,1,0), (1,1,0), (0,0,1), (1,1,1), (0,1,1)`;

the four named triples are dependent because `U = S·T`, `T' = S·U'`,
`U' = S'·T`(-wise) and `T' = S'·U`, and every other triple recovers all
of `a, c, b` (unimodular exponent determinant), hence has rank three.

This file provides the tuple `qQuad`, the pairwise non-membership kit,
and its distinctness; the rank clauses complete in the next increment.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4, checklist G3 soundness, clause (vi)).
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- Distinct principal closures from one-sided non-algebraicity.-/
theorem point_ne_of_notMem {z w : K} (h : w ∉ racl k {z}) :
    ClosedIF.point k z ≠ ClosedIF.point k w := by
  intro heq
  exact h (ClosedIF.point_eq_point_iff.1 heq).2

/-- Distinct points from one-sided non-algebraicity, in `Point.mk'`
form (second generator over the first).-/
theorem Point.mk'_ne {z w : K} {hz : z ∉ (⊥ : ClosedIF k K)}
    {hw : w ∉ (⊥ : ClosedIF k K)} (h : w ∉ racl k {z}) :
    Point.mk' k z hz ≠ Point.mk' k w hw := by
  intro heq
  exact point_ne_of_notMem h (congrArg Subtype.val heq)

/-- Distinct points from one-sided non-algebraicity, in `Point.mk'`
form (first generator over the second).-/
theorem Point.mk'_ne' {z w : K} {hz : z ∉ (⊥ : ClosedIF k K)}
    {hw : w ∉ (⊥ : ClosedIF k K)} (h : z ∉ racl k {w}) :
    Point.mk' k z hz ≠ Point.mk' k w hw := by
  intro heq
  have h2 := ClosedIF.point_eq_point_iff.1 (congrArg Subtype.val heq)
  exact h h2.1

section QTable

variable {a b c d x : K} (hind : AlgebraicIndependent k ![a, b, c, d, x])

include hind

theorem qtable_a_notMem_c : a ∉ racl k ({c} : Set K) := by
  have h : AlgebraicIndependent k ![a, c] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 0) (j := 2) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair' h

theorem qtable_a_notMem_bc' : a ∉ racl k ({b, c} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {1, 2}) (i := 0) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_a_notMem_cb : a ∉ racl k ({c, b} : Set K) := by
  rw [Set.pair_comm c b]
  exact qtable_a_notMem_bc' hind

/-! ### Non-membership of the quadrangle monomials in each other's
closures -/

/-- `ac ∉ racl{a}`: dividing by `a` would make `c` algebraic over `a`.-/
theorem qtable_ac_notMem_a : a * c ∉ racl k ({a} : Set K) := by
  intro hmem
  have ha : a ∈ racl k ({a} : Set K) := subset_racl k _ rfl
  have h := MulMemClass.mul_mem (inv_mem ha) hmem
  rw [inv_mul_cancel_left₀ (qtable_a_ne_zero hind)] at h
  exact qtable_c_notMem_a hind h

/-- `ac ∉ racl{c}`.-/
theorem qtable_ac_notMem_c : a * c ∉ racl k ({c} : Set K) := by
  intro hmem
  have hc : c ∈ racl k ({c} : Set K) := subset_racl k _ rfl
  have h := MulMemClass.mul_mem hmem (inv_mem hc)
  rw [mul_inv_cancel_right₀ (qtable_c_ne_zero hind)] at h
  exact qtable_a_notMem_c hind h

/-- `ac ∉ racl{b}`: dividing by `c` puts `a` in `racl{b, c}`.-/
theorem qtable_ac_notMem_b : a * c ∉ racl k ({b} : Set K) := by
  intro hmem
  have hsub : racl k ({b} : Set K) ≤ racl k ({b, c} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2
      (subset_racl k _ (by simp)))
  have hc : c ∈ racl k ({b, c} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem (hsub hmem) (inv_mem hc)
  rw [mul_inv_cancel_right₀ (qtable_c_ne_zero hind)] at h
  exact qtable_a_notMem_bc' hind h

/-- `cb ∉ racl{a}`: dividing by `c` puts `b` in `racl{a, c}`.-/
theorem qtable_cb_notMem_a : c * b ∉ racl k ({a} : Set K) := by
  intro hmem
  have hsub : racl k ({a} : Set K) ≤ racl k ({a, c} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2
      (subset_racl k _ (by simp)))
  have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem (inv_mem hc) (hsub hmem)
  rw [inv_mul_cancel_left₀ (qtable_c_ne_zero hind)] at h
  exact qtable_b_notMem_ac hind h

/-- `cb ∉ racl{c}`.-/
theorem qtable_cb_notMem_c : c * b ∉ racl k ({c} : Set K) := by
  intro hmem
  have hc : c ∈ racl k ({c} : Set K) := subset_racl k _ rfl
  have h := MulMemClass.mul_mem (inv_mem hc) hmem
  rw [inv_mul_cancel_left₀ (qtable_c_ne_zero hind)] at h
  exact qtable_b_notMem_c hind h

/-- `cb ∉ racl{b}`.-/
theorem qtable_cb_notMem_b : c * b ∉ racl k ({b} : Set K) := by
  intro hmem
  have hb : b ∈ racl k ({b} : Set K) := subset_racl k _ rfl
  have h := MulMemClass.mul_mem hmem (inv_mem hb)
  rw [mul_inv_cancel_right₀ (qtable_b_ne_zero hind)] at h
  exact qtable_c_notMem_b hind h

/-- `cb ∉ racl{ac}`: the closure of `ac` sits inside `racl{a, c}`.-/
theorem qtable_cb_notMem_ac : c * b ∉ racl k ({a * c} : Set K) := by
  intro hmem
  have hsub : racl k ({a * c} : Set K) ≤ racl k ({a, c} : Set K) := by
    refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
    have ha : a ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
    have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
    exact MulMemClass.mul_mem ha hc
  have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem (inv_mem hc) (hsub hmem)
  rw [inv_mul_cancel_left₀ (qtable_c_ne_zero hind)] at h
  exact qtable_b_notMem_ac hind h

/-- `acb ∉ racl{a}`.-/
theorem qtable_acb_notMem_a : a * c * b ∉ racl k ({a} : Set K) := by
  intro hmem
  have hsub : racl k ({a} : Set K) ≤ racl k ({a, c} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2
      (subset_racl k _ (by simp)))
  have ha : a ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
  have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem
    (inv_mem (MulMemClass.mul_mem ha hc)) (hsub hmem)
  rw [inv_mul_cancel_left₀ (mul_ne_zero (qtable_a_ne_zero hind)
    (qtable_c_ne_zero hind))] at h
  exact qtable_b_notMem_ac hind h

/-- `acb ∉ racl{c}`: dividing by `cb` puts `a` in `racl{c, b}`.-/
theorem qtable_acb_notMem_c : a * c * b ∉ racl k ({c} : Set K) := by
  intro hmem
  have hsub : racl k ({c} : Set K) ≤ racl k ({c, b} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2
      (subset_racl k _ (by simp)))
  have hc : c ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
  have hb : b ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem (hsub hmem)
    (inv_mem (MulMemClass.mul_mem hc hb))
  have harith : a * c * b * (c * b)⁻¹ = a := by
    rw [mul_assoc a c b, mul_inv_cancel_right₀ (mul_ne_zero
      (qtable_c_ne_zero hind) (qtable_b_ne_zero hind))]
  rw [harith] at h
  exact qtable_a_notMem_cb hind h

/-- `acb ∉ racl{b}`.-/
theorem qtable_acb_notMem_b : a * c * b ∉ racl k ({b} : Set K) := by
  intro hmem
  have hsub : racl k ({b} : Set K) ≤ racl k ({b, c} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2
      (subset_racl k _ (by simp)))
  have hc : c ∈ racl k ({b, c} : Set K) := subset_racl k _ (by simp)
  have hb : b ∈ racl k ({b, c} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem (hsub hmem)
    (inv_mem (MulMemClass.mul_mem hc hb))
  have harith : a * c * b * (c * b)⁻¹ = a := by
    rw [mul_assoc a c b, mul_inv_cancel_right₀ (mul_ne_zero
      (qtable_c_ne_zero hind) (qtable_b_ne_zero hind))]
  rw [harith] at h
  exact qtable_a_notMem_bc' hind h

/-- `acb ∉ racl{ac}`.-/
theorem qtable_acb_notMem_ac : a * c * b ∉ racl k ({a * c} : Set K) := by
  intro hmem
  have hsub : racl k ({a * c} : Set K) ≤ racl k ({a, c} : Set K) := by
    refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
    have ha : a ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
    have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
    exact MulMemClass.mul_mem ha hc
  have ha : a ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
  have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem
    (inv_mem (MulMemClass.mul_mem ha hc)) (hsub hmem)
  rw [inv_mul_cancel_left₀ (mul_ne_zero (qtable_a_ne_zero hind)
    (qtable_c_ne_zero hind))] at h
  exact qtable_b_notMem_ac hind h

/-- `acb ∉ racl{cb}`.-/
theorem qtable_acb_notMem_cb : a * c * b ∉ racl k ({c * b} : Set K) := by
  intro hmem
  have hsub : racl k ({c * b} : Set K) ≤ racl k ({c, b} : Set K) := by
    refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
    have hc : c ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
    have hb : b ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
    exact MulMemClass.mul_mem hc hb
  have hc : c ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
  have hb : b ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem (hsub hmem)
    (inv_mem (MulMemClass.mul_mem hc hb))
  have harith : a * c * b * (c * b)⁻¹ = a := by
    rw [mul_assoc a c b, mul_inv_cancel_right₀ (mul_ne_zero
      (qtable_c_ne_zero hind) (qtable_b_ne_zero hind))]
  rw [harith] at h
  exact qtable_a_notMem_cb hind h

/-! ### The quadrangle tuple and its distinctness -/

/-- The six quadrangle points `(S, T, U, S', T', U')` of table 7.1/7.2:
`([a], [c], [ac], [b], [acb], [cb])`.-/
def qQuad : Fin 6 → Point k K :=
  ![Point.mk' k a (qtable_a_notMem_bot hind),
    Point.mk' k c (qtable_c_notMem_bot hind),
    Point.mk' k (a * c) (qtable_mul_ac_notMem_bot hind),
    Point.mk' k b (qtable_b_notMem_bot hind),
    Point.mk' k (a * c * b) (qtable_acb_notMem_bot hind),
    Point.mk' k (c * b) (qtable_mul_cb_notMem_bot hind)]

/-- The six quadrangle points are pairwise distinct.-/
theorem qQuad_injective : Function.Injective (qQuad hind) := by
  have hne : ∀ i j : Fin 6, i < j → qQuad hind i ≠ qQuad hind j := by
    intro i j hlt
    fin_cases i <;> fin_cases j
    · exact absurd hlt (by decide)
    · show Point.mk' k a (qtable_a_notMem_bot hind) ≠ Point.mk' k c (qtable_c_notMem_bot hind)
      exact Point.mk'_ne (qtable_c_notMem_a hind)
    · show Point.mk' k a (qtable_a_notMem_bot hind) ≠ Point.mk' k (a * c) (qtable_mul_ac_notMem_bot hind)
      exact Point.mk'_ne (qtable_ac_notMem_a hind)
    · show Point.mk' k a (qtable_a_notMem_bot hind) ≠ Point.mk' k b (qtable_b_notMem_bot hind)
      exact Point.mk'_ne' (qtable_a_notMem_b hind)
    · show Point.mk' k a (qtable_a_notMem_bot hind) ≠ Point.mk' k (a * c * b) (qtable_acb_notMem_bot hind)
      exact Point.mk'_ne (qtable_acb_notMem_a hind)
    · show Point.mk' k a (qtable_a_notMem_bot hind) ≠ Point.mk' k (c * b) (qtable_mul_cb_notMem_bot hind)
      exact Point.mk'_ne (qtable_cb_notMem_a hind)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · show Point.mk' k c (qtable_c_notMem_bot hind) ≠ Point.mk' k (a * c) (qtable_mul_ac_notMem_bot hind)
      exact Point.mk'_ne (qtable_ac_notMem_c hind)
    · show Point.mk' k c (qtable_c_notMem_bot hind) ≠ Point.mk' k b (qtable_b_notMem_bot hind)
      exact Point.mk'_ne (qtable_b_notMem_c hind)
    · show Point.mk' k c (qtable_c_notMem_bot hind) ≠ Point.mk' k (a * c * b) (qtable_acb_notMem_bot hind)
      exact Point.mk'_ne (qtable_acb_notMem_c hind)
    · show Point.mk' k c (qtable_c_notMem_bot hind) ≠ Point.mk' k (c * b) (qtable_mul_cb_notMem_bot hind)
      exact Point.mk'_ne (qtable_cb_notMem_c hind)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · show Point.mk' k (a * c) (qtable_mul_ac_notMem_bot hind) ≠ Point.mk' k b (qtable_b_notMem_bot hind)
      exact Point.mk'_ne' (qtable_ac_notMem_b hind)
    · show Point.mk' k (a * c) (qtable_mul_ac_notMem_bot hind) ≠ Point.mk' k (a * c * b) (qtable_acb_notMem_bot hind)
      exact Point.mk'_ne (qtable_acb_notMem_ac hind)
    · show Point.mk' k (a * c) (qtable_mul_ac_notMem_bot hind) ≠ Point.mk' k (c * b) (qtable_mul_cb_notMem_bot hind)
      exact Point.mk'_ne (qtable_cb_notMem_ac hind)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · show Point.mk' k b (qtable_b_notMem_bot hind) ≠ Point.mk' k (a * c * b) (qtable_acb_notMem_bot hind)
      exact Point.mk'_ne (qtable_acb_notMem_b hind)
    · show Point.mk' k b (qtable_b_notMem_bot hind) ≠ Point.mk' k (c * b) (qtable_mul_cb_notMem_bot hind)
      exact Point.mk'_ne (qtable_cb_notMem_b hind)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · show Point.mk' k (a * c * b) (qtable_acb_notMem_bot hind) ≠ Point.mk' k (c * b) (qtable_mul_cb_notMem_bot hind)
      exact Point.mk'_ne' (qtable_acb_notMem_cb hind)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
  intro i j hij
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hij (hne i j h)
  · exact h
  · exact absurd hij.symm (hne j i h)

end QTable

/-! ### Generic recovery and rank helpers -/

/-- Cancel a known nonzero left factor inside any intermediate field.-/
theorem mem_of_mul_mem_left {E : IntermediateField k K} {u v : K}
    (hu : u ∈ E) (hu0 : u ≠ 0) (huv : u * v ∈ E) : v ∈ E := by
  have h := MulMemClass.mul_mem (inv_mem hu) huv
  rwa [inv_mul_cancel_left₀ hu0] at h

/-- Cancel a known nonzero right factor inside any intermediate field.-/
theorem mem_of_mul_mem_right {E : IntermediateField k K} {u v : K}
    (hv : v ∈ E) (hv0 : v ≠ 0) (huv : u * v ∈ E) : u ∈ E := by
  have h := MulMemClass.mul_mem huv (inv_mem hv)
  rwa [mul_inv_cancel_right₀ hv0] at h

theorem range_pair (u v : K) : Set.range ![u, v] = ({u, v} : Set K) := by
  ext z
  simp [Matrix.range_cons, Matrix.range_empty]
  tauto

theorem range_triple (u v w : K) :
    Set.range ![u, v, w] = ({u, v, w} : Set K) := by
  ext z
  simp [Matrix.range_cons, Matrix.range_empty]
  tauto

/-- Rank two for a triple join of principal closures whose generators
close to an independent pair.-/
theorem rankEq_two_points {z₁ z₂ z₃ u v : K}
    (huv : AlgebraicIndependent k ![u, v])
    (h : racl k ({z₁, z₂, z₃} : Set K) = racl k ({u, v} : Set K)) :
    RankEq 2 (ClosedIF.point k z₁ ⊔
      (ClosedIF.point k z₂ ⊔ ClosedIF.point k z₃)) := by
  refine rankEq_of_coe_eq_racl huv ?_
  rw [coe_sup_point₃, range_pair]
  exact h

/-- Rank three for a triple join of principal closures whose generators
close to an independent triple.-/
theorem rankEq_three_points {z₁ z₂ z₃ u v w : K}
    (huvw : AlgebraicIndependent k ![u, v, w])
    (h : racl k ({z₁, z₂, z₃} : Set K) = racl k ({u, v, w} : Set K)) :
    RankEq 3 (ClosedIF.point k z₁ ⊔
      (ClosedIF.point k z₂ ⊔ ClosedIF.point k z₃)) := by
  refine rankEq_of_coe_eq_racl huvw ?_
  rw [coe_sup_point₃, range_triple]
  exact h

section QTable2

variable {a b c d x : K} (hind : AlgebraicIndependent k ![a, b, c, d, x])

include hind

/-- The independent triple `(a, c, b)`, restricted from the five-tuple.-/
theorem qtable_indep_acb : AlgebraicIndependent k ![a, c, b] := by
  have h := AlgebraicIndependent.comp hind
    (![0, 2, 1] : Fin 3 -> Fin 5) (by decide)
  have heq : (![a, b, c, d, x] ∘ (![0, 2, 1] : Fin 3 -> Fin 5)) =
      ![a, c, b] := by
    funext i
    fin_cases i <;> rfl
  rwa [heq] at h

/-! Memberships of the six quadrangle monomials in `racl {a, c, b}`. -/

theorem qtable_acb_mem_a : a ∈ racl k ({a, c, b} : Set K) :=
  subset_racl k _ (by simp)

theorem qtable_acb_mem_c : c ∈ racl k ({a, c, b} : Set K) :=
  subset_racl k _ (by simp)

theorem qtable_acb_mem_b : b ∈ racl k ({a, c, b} : Set K) :=
  subset_racl k _ (by simp)

theorem qtable_acb_mem_ac : a * c ∈ racl k ({a, c, b} : Set K) :=
  MulMemClass.mul_mem (qtable_acb_mem_a hind) (qtable_acb_mem_c hind)

theorem qtable_acb_mem_acb : a * c * b ∈ racl k ({a, c, b} : Set K) :=
  MulMemClass.mul_mem (qtable_acb_mem_ac hind) (qtable_acb_mem_b hind)

theorem qtable_acb_mem_cb : c * b ∈ racl k ({a, c, b} : Set K) :=
  MulMemClass.mul_mem (qtable_acb_mem_c hind) (qtable_acb_mem_b hind)

/-! Independence of the dependent-triple base pairs. -/

theorem qtable_indep_a_cb : AlgebraicIndependent k ![a, c * b] := by
  refine algebraicIndependent_pair ?_ (qtable_cb_notMem_a hind)
  intro hmem
  have hsub : racl k ({c * b} : Set K) <= racl k ({c, b} : Set K) := by
    refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
    have hc : c ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
    have hb : b ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
    exact MulMemClass.mul_mem hc hb
  exact qtable_a_notMem_cb hind (hsub hmem)

theorem qtable_indep_ac_b : AlgebraicIndependent k ![a * c, b] := by
  refine algebraicIndependent_pair (qtable_ac_notMem_b hind) ?_
  intro hmem
  have hsub : racl k ({a * c} : Set K) <= racl k ({a, c} : Set K) := by
    refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
    have ha : a ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
    have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
    exact MulMemClass.mul_mem ha hc
  exact qtable_b_notMem_ac hind (hsub hmem)

theorem qtable_indep_ac : AlgebraicIndependent k ![a, c] := by
  simpa using AlgebraicIndependent.comp_pair hind (i := 0) (j := 2)
    (by decide)

theorem qtable_indep_cb : AlgebraicIndependent k ![c, b] := by
  simpa using AlgebraicIndependent.comp_pair hind (i := 2) (j := 1)
    (by decide)

/-! ### The four dependent triples -/

theorem qQuad_rank_dep :
    ∀ s ∈ quadTriples, RankEq 2 (s.sup fun i ↦ ((qQuad hind) i).1) := by
  intro s hs
  fin_cases hs
  · -- (S, T, U) = (a, c, ac)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 2 (ClosedIF.point k a ⊔
      (ClosedIF.point k c ⊔ ClosedIF.point k (a * c)))
    refine rankEq_two_points (qtable_indep_ac hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro z (rfl | rfl | rfl)
      · exact subset_racl k _ (by simp)
      · exact subset_racl k _ (by simp)
      · have ha : a ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
        have hc : c ∈ racl k ({a, c} : Set K) := subset_racl k _ (by simp)
        exact MulMemClass.mul_mem ha hc
    · rintro z (rfl | rfl)
      · exact subset_racl k _ (by simp)
      · exact subset_racl k _ (by simp)
  · -- (S, T', U') = (a, acb, cb)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 2 (ClosedIF.point k a ⊔
      (ClosedIF.point k (a * c * b) ⊔ ClosedIF.point k (c * b)))
    refine rankEq_two_points (qtable_indep_a_cb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro z (rfl | rfl | rfl)
      · exact subset_racl k _ (by simp)
      · have ha : a ∈ racl k ({a, c * b} : Set K) :=
          subset_racl k _ (by simp)
        have hcb : c * b ∈ racl k ({a, c * b} : Set K) :=
          subset_racl k _ (by simp)
        have h := MulMemClass.mul_mem ha hcb
        rwa [← mul_assoc] at h
      · exact subset_racl k _ (by simp)
    · rintro z (rfl | rfl)
      · exact subset_racl k _ (by simp)
      · exact subset_racl k _ (by simp)
  · -- (T, S', U') = (c, b, cb)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 2 (ClosedIF.point k c ⊔
      (ClosedIF.point k b ⊔ ClosedIF.point k (c * b)))
    refine rankEq_two_points (qtable_indep_cb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro z (rfl | rfl | rfl)
      · exact subset_racl k _ (by simp)
      · exact subset_racl k _ (by simp)
      · have hc : c ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
        have hb : b ∈ racl k ({c, b} : Set K) := subset_racl k _ (by simp)
        exact MulMemClass.mul_mem hc hb
    · rintro z (rfl | rfl)
      · exact subset_racl k _ (by simp)
      · exact subset_racl k _ (by simp)
  · -- (U, S', T') = (ac, b, acb)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 2 (ClosedIF.point k (a * c) ⊔
      (ClosedIF.point k b ⊔ ClosedIF.point k (a * c * b)))
    refine rankEq_two_points (qtable_indep_ac_b hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro z (rfl | rfl | rfl)
      · exact subset_racl k _ (by simp)
      · exact subset_racl k _ (by simp)
      · have hac : a * c ∈ racl k ({a * c, b} : Set K) :=
          subset_racl k _ (by simp)
        have hb : b ∈ racl k ({a * c, b} : Set K) :=
          subset_racl k _ (by simp)
        exact MulMemClass.mul_mem hac hb
    · rintro z (rfl | rfl)
      · exact subset_racl k _ (by simp)
      · exact subset_racl k _ (by simp)

end QTable2

section QTable3

variable {a b c d x : K} (hind : AlgebraicIndependent k ![a, b, c, d, x])

include hind

/-- Every free triple of the quadrangle has rank three: the unimodular
exponent matrix lets each one recover all of `a, c, b`.-/
theorem qQuad_rank_free :
    ∀ s : Finset (Fin 6), s.card = 3 → s ∉ quadTriples →
      RankEq 3 (s.sup fun i ↦ ((qQuad hind) i).1) := by
  intro s hs3 hsnot
  have hall : ∀ t : Finset (Fin 6), t.card = 3 → t ∉ quadTriples →
      t ∈ ({{0,1,3}, {0,2,3}, {1,2,3}, {0,1,4}, {0,2,4}, {1,2,4}, {0,3,4},
        {1,3,4}, {0,1,5}, {0,2,5}, {1,2,5}, {0,3,5}, {2,3,5}, {1,4,5},
        {2,4,5}, {3,4,5}} : Finset (Finset (Fin 6))) := by decide
  have hmem := hall s hs3 hsnot
  fin_cases hmem
  · -- {0,1,3} = (a, c, b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (a) ⊔
      (ClosedIF.point k (c) ⊔ ClosedIF.point k (b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_a hind
      · exact qtable_acb_mem_c hind
      · exact qtable_acb_mem_b hind
    · -- recoveries
      have h0 : a ∈ racl k ({a, c, b} : Set K) :=
        subset_racl k _ (by simp)
      have h1 : c ∈ racl k ({a, c, b} : Set K) :=
        subset_racl k _ (by simp)
      have h3 : b ∈ racl k ({a, c, b} : Set K) :=
        subset_racl k _ (by simp)
      have hA := h0
      have hC := h1
      have hB := h3
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {0,2,3} = (a, a * c, b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (a) ⊔
      (ClosedIF.point k (a * c) ⊔ ClosedIF.point k (b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_a hind
      · exact qtable_acb_mem_ac hind
      · exact qtable_acb_mem_b hind
    · -- recoveries
      have h0 : a ∈ racl k ({a, a * c, b} : Set K) :=
        subset_racl k _ (by simp)
      have h2 : a * c ∈ racl k ({a, a * c, b} : Set K) :=
        subset_racl k _ (by simp)
      have h3 : b ∈ racl k ({a, a * c, b} : Set K) :=
        subset_racl k _ (by simp)
      have hA := h0
      have hC := mem_of_mul_mem_left h0 (qtable_a_ne_zero hind) h2
      have hB := h3
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {1,2,3} = (c, a * c, b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (c) ⊔
      (ClosedIF.point k (a * c) ⊔ ClosedIF.point k (b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_c hind
      · exact qtable_acb_mem_ac hind
      · exact qtable_acb_mem_b hind
    · -- recoveries
      have h1 : c ∈ racl k ({c, a * c, b} : Set K) :=
        subset_racl k _ (by simp)
      have h2 : a * c ∈ racl k ({c, a * c, b} : Set K) :=
        subset_racl k _ (by simp)
      have h3 : b ∈ racl k ({c, a * c, b} : Set K) :=
        subset_racl k _ (by simp)
      have hA := mem_of_mul_mem_right h1 (qtable_c_ne_zero hind) h2
      have hC := h1
      have hB := h3
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {0,1,4} = (a, c, a * c * b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (a) ⊔
      (ClosedIF.point k (c) ⊔ ClosedIF.point k (a * c * b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_a hind
      · exact qtable_acb_mem_c hind
      · exact qtable_acb_mem_acb hind
    · -- recoveries
      have h0 : a ∈ racl k ({a, c, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h1 : c ∈ racl k ({a, c, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h4 : a * c * b ∈ racl k ({a, c, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have hA := h0
      have hC := h1
      have hB := mem_of_mul_mem_left (MulMemClass.mul_mem h0 h1) (mul_ne_zero (qtable_a_ne_zero hind) (qtable_c_ne_zero hind)) h4
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {0,2,4} = (a, a * c, a * c * b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (a) ⊔
      (ClosedIF.point k (a * c) ⊔ ClosedIF.point k (a * c * b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_a hind
      · exact qtable_acb_mem_ac hind
      · exact qtable_acb_mem_acb hind
    · -- recoveries
      have h0 : a ∈ racl k ({a, a * c, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h2 : a * c ∈ racl k ({a, a * c, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h4 : a * c * b ∈ racl k ({a, a * c, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have hA := h0
      have hC := mem_of_mul_mem_left h0 (qtable_a_ne_zero hind) h2
      have hB := mem_of_mul_mem_left h2 (mul_ne_zero (qtable_a_ne_zero hind) (qtable_c_ne_zero hind)) h4
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {1,2,4} = (c, a * c, a * c * b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (c) ⊔
      (ClosedIF.point k (a * c) ⊔ ClosedIF.point k (a * c * b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_c hind
      · exact qtable_acb_mem_ac hind
      · exact qtable_acb_mem_acb hind
    · -- recoveries
      have h1 : c ∈ racl k ({c, a * c, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h2 : a * c ∈ racl k ({c, a * c, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h4 : a * c * b ∈ racl k ({c, a * c, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have hA := mem_of_mul_mem_right h1 (qtable_c_ne_zero hind) h2
      have hC := h1
      have hB := mem_of_mul_mem_left h2 (mul_ne_zero (qtable_a_ne_zero hind) (qtable_c_ne_zero hind)) h4
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {0,3,4} = (a, b, a * c * b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (a) ⊔
      (ClosedIF.point k (b) ⊔ ClosedIF.point k (a * c * b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_a hind
      · exact qtable_acb_mem_b hind
      · exact qtable_acb_mem_acb hind
    · -- recoveries
      have h0 : a ∈ racl k ({a, b, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h3 : b ∈ racl k ({a, b, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h4 : a * c * b ∈ racl k ({a, b, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have hA := h0
      have hac := mem_of_mul_mem_right h3 (qtable_b_ne_zero hind) h4
      have hC := mem_of_mul_mem_left h0 (qtable_a_ne_zero hind) hac
      have hB := h3
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {1,3,4} = (c, b, a * c * b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (c) ⊔
      (ClosedIF.point k (b) ⊔ ClosedIF.point k (a * c * b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_c hind
      · exact qtable_acb_mem_b hind
      · exact qtable_acb_mem_acb hind
    · -- recoveries
      have h1 : c ∈ racl k ({c, b, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h3 : b ∈ racl k ({c, b, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h4 : a * c * b ∈ racl k ({c, b, a * c * b} : Set K) :=
        subset_racl k _ (by simp)
      have hac := mem_of_mul_mem_right h3 (qtable_b_ne_zero hind) h4
      have hA := mem_of_mul_mem_right h1 (qtable_c_ne_zero hind) hac
      have hC := h1
      have hB := h3
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {0,1,5} = (a, c, c * b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (a) ⊔
      (ClosedIF.point k (c) ⊔ ClosedIF.point k (c * b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_a hind
      · exact qtable_acb_mem_c hind
      · exact qtable_acb_mem_cb hind
    · -- recoveries
      have h0 : a ∈ racl k ({a, c, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h1 : c ∈ racl k ({a, c, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h5 : c * b ∈ racl k ({a, c, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have hA := h0
      have hC := h1
      have hB := mem_of_mul_mem_left h1 (qtable_c_ne_zero hind) h5
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {0,2,5} = (a, a * c, c * b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (a) ⊔
      (ClosedIF.point k (a * c) ⊔ ClosedIF.point k (c * b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_a hind
      · exact qtable_acb_mem_ac hind
      · exact qtable_acb_mem_cb hind
    · -- recoveries
      have h0 : a ∈ racl k ({a, a * c, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h2 : a * c ∈ racl k ({a, a * c, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h5 : c * b ∈ racl k ({a, a * c, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have hA := h0
      have hC := mem_of_mul_mem_left h0 (qtable_a_ne_zero hind) h2
      have hB := mem_of_mul_mem_left hC (qtable_c_ne_zero hind) h5
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {1,2,5} = (c, a * c, c * b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (c) ⊔
      (ClosedIF.point k (a * c) ⊔ ClosedIF.point k (c * b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_c hind
      · exact qtable_acb_mem_ac hind
      · exact qtable_acb_mem_cb hind
    · -- recoveries
      have h1 : c ∈ racl k ({c, a * c, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h2 : a * c ∈ racl k ({c, a * c, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h5 : c * b ∈ racl k ({c, a * c, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have hA := mem_of_mul_mem_right h1 (qtable_c_ne_zero hind) h2
      have hC := h1
      have hB := mem_of_mul_mem_left h1 (qtable_c_ne_zero hind) h5
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {0,3,5} = (a, b, c * b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (a) ⊔
      (ClosedIF.point k (b) ⊔ ClosedIF.point k (c * b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_a hind
      · exact qtable_acb_mem_b hind
      · exact qtable_acb_mem_cb hind
    · -- recoveries
      have h0 : a ∈ racl k ({a, b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h3 : b ∈ racl k ({a, b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h5 : c * b ∈ racl k ({a, b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have hA := h0
      have hC := mem_of_mul_mem_right h3 (qtable_b_ne_zero hind) h5
      have hB := h3
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {2,3,5} = (a * c, b, c * b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (a * c) ⊔
      (ClosedIF.point k (b) ⊔ ClosedIF.point k (c * b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_ac hind
      · exact qtable_acb_mem_b hind
      · exact qtable_acb_mem_cb hind
    · -- recoveries
      have h2 : a * c ∈ racl k ({a * c, b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h3 : b ∈ racl k ({a * c, b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h5 : c * b ∈ racl k ({a * c, b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have hC := mem_of_mul_mem_right h3 (qtable_b_ne_zero hind) h5
      have hA := mem_of_mul_mem_right hC (qtable_c_ne_zero hind) h2
      have hB := h3
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {1,4,5} = (c, a * c * b, c * b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (c) ⊔
      (ClosedIF.point k (a * c * b) ⊔ ClosedIF.point k (c * b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_c hind
      · exact qtable_acb_mem_acb hind
      · exact qtable_acb_mem_cb hind
    · -- recoveries
      have h1 : c ∈ racl k ({c, a * c * b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h4 : a * c * b ∈ racl k ({c, a * c * b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h5 : c * b ∈ racl k ({c, a * c * b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have hB := mem_of_mul_mem_left h1 (qtable_c_ne_zero hind) h5
      have hac := mem_of_mul_mem_right hB (qtable_b_ne_zero hind) h4
      have hA := mem_of_mul_mem_right h1 (qtable_c_ne_zero hind) hac
      have hC := h1
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {2,4,5} = (a * c, a * c * b, c * b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (a * c) ⊔
      (ClosedIF.point k (a * c * b) ⊔ ClosedIF.point k (c * b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_ac hind
      · exact qtable_acb_mem_acb hind
      · exact qtable_acb_mem_cb hind
    · -- recoveries
      have h2 : a * c ∈ racl k ({a * c, a * c * b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h4 : a * c * b ∈ racl k ({a * c, a * c * b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h5 : c * b ∈ racl k ({a * c, a * c * b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have hB := mem_of_mul_mem_left h2 (mul_ne_zero (qtable_a_ne_zero hind) (qtable_c_ne_zero hind)) h4
      have hC := mem_of_mul_mem_right hB (qtable_b_ne_zero hind) h5
      have hA := mem_of_mul_mem_right hC (qtable_c_ne_zero hind) h2
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB
  · -- {3,4,5} = (b, a * c * b, c * b)
    simp only [Finset.sup_insert, Finset.sup_singleton]
    show RankEq 3 (ClosedIF.point k (b) ⊔
      (ClosedIF.point k (a * c * b) ⊔ ClosedIF.point k (c * b)))
    refine rankEq_three_points (qtable_indep_acb hind) ?_
    refine racl_congr_of_subset_racl ?_ ?_
    · rintro w (rfl | rfl | rfl)
      · exact qtable_acb_mem_b hind
      · exact qtable_acb_mem_acb hind
      · exact qtable_acb_mem_cb hind
    · -- recoveries
      have h3 : b ∈ racl k ({b, a * c * b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h4 : a * c * b ∈ racl k ({b, a * c * b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have h5 : c * b ∈ racl k ({b, a * c * b, c * b} : Set K) :=
        subset_racl k _ (by simp)
      have hC := mem_of_mul_mem_right h3 (qtable_b_ne_zero hind) h5
      have hac := mem_of_mul_mem_right h3 (qtable_b_ne_zero hind) h4
      have hA := mem_of_mul_mem_right hC (qtable_c_ne_zero hind) hac
      have hB := h3
      rintro w (rfl | rfl | rfl)
      · exact hA
      · exact hC
      · exact hB

/-- The join of all six quadrangle points has rank three.-/
theorem qQuad_rank_total :
    RankEq 3 (Finset.univ.sup fun i ↦ ((qQuad hind) i).1) := by
  refine rankEq_of_coe_eq_racl (qtable_indep_acb hind) ?_
  rw [range_triple]
  refine ClosedIF.coe_eq_racl_of_le ?_ ?_
  · refine Finset.sup_le ?_
    intro i _
    fin_cases i
    · exact ClosedIF.point_le_iff.2 (qtable_acb_mem_a hind)
    · exact ClosedIF.point_le_iff.2 (qtable_acb_mem_c hind)
    · exact ClosedIF.point_le_iff.2 (qtable_acb_mem_ac hind)
    · exact ClosedIF.point_le_iff.2 (qtable_acb_mem_b hind)
    · exact ClosedIF.point_le_iff.2 (qtable_acb_mem_acb hind)
    · exact ClosedIF.point_le_iff.2 (qtable_acb_mem_cb hind)
  · rintro w (rfl | rfl | rfl)
    · have hle : ((qQuad hind) 0).1 ≤
          Finset.univ.sup fun i ↦ ((qQuad hind) i).1 :=
        Finset.le_sup (f := fun i ↦ ((qQuad hind) i).1)
          (Finset.mem_univ (0 : Fin 6))
      exact (ClosedIF.le_iff.1 hle) (ClosedIF.mem_point_self w)
    · have hle : ((qQuad hind) 1).1 ≤
          Finset.univ.sup fun i ↦ ((qQuad hind) i).1 :=
        Finset.le_sup (f := fun i ↦ ((qQuad hind) i).1)
          (Finset.mem_univ (1 : Fin 6))
      exact (ClosedIF.le_iff.1 hle) (ClosedIF.mem_point_self w)
    · have hle : ((qQuad hind) 3).1 ≤
          Finset.univ.sup fun i ↦ ((qQuad hind) i).1 :=
        Finset.le_sup (f := fun i ↦ ((qQuad hind) i).1)
          (Finset.mem_univ (3 : Fin 6))
      exact (ClosedIF.le_iff.1 hle) (ClosedIF.mem_point_self w)

/-- The table-7.2 sextuple is a partial quadrangle.-/
theorem qQuad_isPartialQuadrangle : IsPartialQuadrangle (qQuad hind) :=
  ⟨qQuad_injective hind, qQuad_rank_dep hind, qQuad_rank_free hind,
    qQuad_rank_total hind⟩

/-- Clause (vi) of Ψ at the soundness witness.-/
theorem qWitness_quad :
    ∃ S' T' U' : Point k K,
      IsPartialQuadrangle
        ![(qWitness hind).S, (qWitness hind).T, (qWitness hind).U,
          S', T', U'] := by
  refine ⟨Point.mk' k b (qtable_b_notMem_bot hind),
    Point.mk' k (a * c * b) (qtable_acb_notMem_bot hind),
    Point.mk' k (c * b) (qtable_mul_cb_notMem_bot hind), ?_⟩
  have heq : ![(qWitness hind).S, (qWitness hind).T, (qWitness hind).U,
      Point.mk' k b (qtable_b_notMem_bot hind),
      Point.mk' k (a * c * b) (qtable_acb_notMem_bot hind),
      Point.mk' k (c * b) (qtable_mul_cb_notMem_bot hind)] = qQuad hind := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact qQuad_isPartialQuadrangle hind

end QTable3

end

end AclGeom
