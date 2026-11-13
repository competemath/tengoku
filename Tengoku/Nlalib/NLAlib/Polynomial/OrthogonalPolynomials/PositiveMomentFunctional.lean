import Tengoku.Nlalib.NLAlib.Polynomial.OrthogonalPolynomials.MomentPositivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive finite moment functionals

Positive definiteness is a condition on a finite Hankel matrix and needs no
representing measure. It gives nonsingular lower-order systems and positive
monic norms throughout that degree space. Source: Gautschi (2004), Chapter 1.
-/

noncomputable section
open Polynomial Finset Matrix
namespace NLAlib

/-- A real Hankel matrix is positive definite exactly when its polynomial
squared form is positive on every nonzero polynomial below its order.
@isnad1 id=iff.0h2v.s7.2f6481f30b00 from=translated src=- shape=a36bb222 vocab=7039bbd9
-/
theorem posDef_hankelMomentMatrix_iff_functional_sq_pos (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) :
    (hankelMomentMatrix L n).PosDef ↔
      ∀ p : ℝ[X], p.degree < n → p ≠ 0 → 0 < L (p ^ 2) := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨_, hpos⟩ p hp hp0
    let c : Fin n → ℝ := fun i => p.coeff i.val
    have hc : c ≠ 0 := by
      intro hzero
      apply hp0
      rw [eq_sum_monomial_fin_of_degree_lt hp]
      have hc' (i : Fin n) : p.coeff i.val = 0 := congrFun hzero i
      simp only [hc', monomial_zero_right, Finset.sum_const_zero]
    have h := hpos hc
    rw [star_trivial, ← functional_sum_monomial_sq_eq_dotProduct] at h
    rw [show (∑ i : Fin n, monomial i.val (c i)) = p from
      (eq_sum_monomial_fin_of_degree_lt hp).symm] at h
    exact h
  · intro hpos
    refine ⟨isHermitian_hankelMomentMatrix _ _, ?_⟩
    intro c hc
    rw [star_trivial, ← functional_sum_monomial_sq_eq_dotProduct]
    exact hpos _ (degree_sum_monomial_fin_lt c)
      ((sum_monomial_fin_eq_zero_iff c).not.mpr hc)

/-- Positive definiteness of a finite real moment form passes to every lower
order, including the empty order-zero system.
@isnad1 id=posdef.2h3v.s6.a488e151d1ff from=translated src=- shape=7df2bb2c vocab=6a1c1819
-/
theorem posDef_hankelMomentMatrix_of_le {L : ℝ[X] →ₗ[ℝ] ℝ} {n k : ℕ}
    (hL : (hankelMomentMatrix L n).PosDef) (hk : k ≤ n) :
    (hankelMomentMatrix L k).PosDef := by
  rw [posDef_hankelMomentMatrix_iff_functional_sq_pos] at hL ⊢
  intro p hp hp0
  exact hL p (hp.trans_le (by exact_mod_cast hk)) hp0

/-- Each lower-order Hankel system of a positive finite moment form is
nonsingular.
@isnad1 id=ne.2h3v.s6.af8f02cb322e from=translated src=- shape=314ec1d9 vocab=13cbd191
-/
theorem hankelMomentDet_ne_zero_of_posDef_of_le {L : ℝ[X] →ₗ[ℝ] ℝ} {n k : ℕ}
    (hL : (hankelMomentMatrix L n).PosDef) (hk : k ≤ n) :
    hankelMomentDet L k ≠ 0 := by
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (posDef_hankelMomentMatrix_of_le hL hk).isUnit)

/-- All included canonical monic polynomial norms are positive in a positive
finite moment form. No representing measure is assumed.
@isnad1 id=lt.2h3v.s6.8219a846fe84 from=translated src=- shape=0079f4c4 vocab=81c9adf2
-/
theorem orthogonalPolynomialNorm_pos_of_posDef {L : ℝ[X] →ₗ[ℝ] ℝ} {n k : ℕ}
    (hL : (hankelMomentMatrix L n).PosDef) (hk : k < n) :
    0 < orthogonalPolynomialNorm L k := by
  apply (posDef_hankelMomentMatrix_iff_functional_sq_pos L n).mp hL
  · rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L k).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    exact_mod_cast hk
  · exact (monic_monicOrthogonalPolynomial L k).ne_zero

end NLAlib
