/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.Seed.Algebra.MvPolynomial.Eval
import Tengoku.Seed.Algebra.Polynomial.AlgebraMap
import Tengoku.Seed.RingTheory.Algebraic.Defs
import Tengoku.Seed.RingTheory.MvPolynomial.WeightedHomogeneous

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Curves with a `(2, 1)`-weighted-homogeneous equation

If a nonzero `F(X, Y)` is weighted homogeneous for the weights `(2, 1)` and vanishes at `(s, u)`
with `u ≠ 0`, then `τ = s/u²` is algebraic over the coefficient field
(`isAlgebraic_div_sq_of_isWeightedHomogeneous`).  The reason is that `F(s, u) = u^W P(τ)` for the
one-variable polynomial `P = ∑ c_m X^{m₀}`.  `P ≠ 0` because `m ↦ m₀` is injective on a support of
fixed weight.

The hypothesis is reached from coefficient characters of support pairs: if every pair of support
monomials satisfies `2(m₁₀ - m₂₀) + (m₁₁ - m₂₁) = 0`, then `F` is weighted homogeneous
(`isWeightedHomogeneous_of_support_pairs`). In the #25 semantic obstruction
(`isAlgebraic_div_sq_of_qLocus`), these are the characters `t^{2d+e} ∈ M` of the curve of
`(s, u₀)` from the scaled-locus lemma.

**Status:** the displayed prerequisites and their concrete Q/Q′ refutation consumers are
proved (#25); the consumers are in Counterexamples/QSemantic and QRefutation.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open MvPolynomial

variable {M Ω : Type*} [Field M] [Field Ω] [Algebra M Ω]

/-- The `(2, 1)`-weight of an exponent in two variables.-/
theorem weight_two_one (m : Fin 2 →₀ ℕ) : Finsupp.weight ![2, 1] m = 2 * m 0 + m 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  ring

/-- If all pairs of support monomials have `(2, 1)`-weight difference zero, the polynomial is
weighted homogeneous for the weights `(2, 1)`.-/
theorem isWeightedHomogeneous_of_support_pairs {F : MvPolynomial (Fin 2) M} (hF0 : F ≠ 0)
    (h : ∀ m₁ ∈ F.support, ∀ m₂ ∈ F.support,
      2 * ((m₁ 0 : ℤ) - m₂ 0) + ((m₁ 1 : ℤ) - m₂ 1) = 0) :
    ∃ W : ℕ, F.IsWeightedHomogeneous ![2, 1] W := by
  obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 fun he ↦ hF0 (support_eq_empty.1 he)
  refine ⟨2 * m 0 + m 1, fun ⦃d⦄ hd ↦ ?_⟩
  have := h d (mem_support_iff.2 hd) m hm
  rw [weight_two_one]
  omega

/-- **A `(2, 1)`-weighted-homogeneous locus determines `s/u²`.**  If `F ≠ 0` is weighted
homogeneous for the weights `(2, 1)` and `F(s, u) = 0` with `u ≠ 0`, then `s/u²` is algebraic over
the coefficient field.-/
theorem isAlgebraic_div_sq_of_isWeightedHomogeneous {F : MvPolynomial (Fin 2) M} {W : ℕ}
    (hF0 : F ≠ 0) (hF : F.IsWeightedHomogeneous ![2, 1] W) {s u : Ω} (hu : u ≠ 0)
    (hsu : MvPolynomial.aeval ![s, u] F = 0) : IsAlgebraic M (s / u ^ 2) := by
  classical
  have hw : ∀ m ∈ F.support, 2 * m 0 + m 1 = W := fun m hm ↦ by
    rw [← weight_two_one]
    exact hF (mem_support_iff.1 hm)
  -- The one-variable polynomial in `τ = s/u²`.
  obtain ⟨P, hP⟩ : ∃ P : Polynomial M,
      P = ∑ m ∈ F.support, Polynomial.monomial (m 0) (F.coeff m) := ⟨_, rfl⟩
  -- `F(s, u) = u^W P(s/u²)`.
  have heval : MvPolynomial.aeval ![s, u] F = u ^ W * Polynomial.aeval (s / u ^ 2) P := by
    rw [hP, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [Polynomial.aeval_monomial, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hW : u ^ W = u ^ (2 * m 0) * u ^ m 1 := by
      rw [← pow_add, hw m hm]
    rw [hW, div_pow, ← pow_mul, mul_div_assoc', mul_div_assoc', eq_div_iff (pow_ne_zero _ hu)]
    ring
  -- `P ≠ 0`: its coefficient at `m⋆ 0` is `F.coeff m⋆`, since `m ↦ m 0` is injective on the
  -- support of fixed weight.
  obtain ⟨m', hm'⟩ := Finset.nonempty_iff_ne_empty.2 fun he ↦ hF0 (support_eq_empty.1 he)
  have hcoeff : P.coeff (m' 0) = F.coeff m' := by
    rw [hP, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single m']
    · simp
    · intro m hm hne
      refine ite_eq_right_iff.2 fun h0 ↦ absurd ?_ hne
      ext j
      fin_cases j
      · exact h0
      · change m 1 = m' 1
        have h1 := hw m hm
        have h2 := hw m' hm'
        omega
    · intro hnot
      exact absurd hm' hnot
  have hP0 : P ≠ 0 := fun h0 ↦ (mem_support_iff.1 hm') (by
    rw [← hcoeff, h0, Polynomial.coeff_zero])
  refine ⟨P, hP0, ?_⟩
  have h0 : u ^ W * Polynomial.aeval (s / u ^ 2) P = 0 := by
    rw [← heval]
    exact hsu
  exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hu)

end AclGeom
