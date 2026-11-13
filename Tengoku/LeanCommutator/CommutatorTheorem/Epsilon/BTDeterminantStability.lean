import Tengoku.Seed.Algebra.MvPolynomial.PDeriv
import Tengoku.Seed.Analysis.Matrix.Hermitian
import Tengoku.Seed.LinearAlgebra.Matrix.MvPolynomial
import Tengoku.Seed.LinearAlgebra.Matrix.ToLinearEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The determinantal base case for exact-MDP stability

For a Hermitian matrix `A`, the polynomial-valued determinant
`det (diag z - A)` cannot vanish when every coordinate of `z` lies in the
open upper half-plane.  This is the elementary definite-determinantal input
to the real-stability argument used for mixed determinantal polynomials.
-/

namespace CommutatorTheorem.BTDeterminantStability

open scoped BigOperators ComplexConjugate
open Matrix Finset MvPolynomial

/-- A complex multivariate polynomial is stable if it does not vanish when
every variable lies in the open upper half-plane.-/
def ComplexStable {ι : Type*} (p : MvPolynomial ι ℂ) : Prop :=
  ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) → MvPolynomial.eval z p ≠ 0

/-- The real-coefficient version of upper-half-plane stability.-/
def RealStable {ι : Type*} (p : MvPolynomial ι ℝ) : Prop :=
  ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) →
    MvPolynomial.eval₂ (algebraMap ℝ ℂ) z p ≠ 0

/-- The multivariate determinant `det (diag X - A)`.-/
noncomputable def hermitianDetPoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : MvPolynomial ι ℂ :=
  (Matrix.diagonal (fun i => MvPolynomial.X i) -
    A.map MvPolynomial.C).det

/--
@isnad1 id=eq.0h3v.s7.d60c7334576e from=translated src=- shape=1bd91f4a vocab=b283d568
-/
theorem eval_hermitianDetPoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (z : ι → ℂ) :
    MvPolynomial.eval z (hermitianDetPoly A) =
      (Matrix.diagonal z - A).det := by
  unfold hermitianDetPoly
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst j
    simp [MvPolynomial.eval_X]
  · simp [h]

/-- The imaginary part of the diagonal quadratic form is the weighted sum of
the coordinate imaginary parts.
@isnad1 id=eq.0h3v.s7.8d9cbe19273d from=translated src=- shape=2f9f390d vocab=6fbe426e
-/
theorem im_star_dotProduct_diagonal_mulVec
    {n : Type*} [Fintype n] [DecidableEq n]
    (z v : n → ℂ) :
    (star v ⬝ᵥ (Matrix.diagonal z *ᵥ v)).im =
      ∑ i, Complex.normSq (v i) * (z i).im := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Complex.im_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.star_apply]
  rw [Complex.star_def]
  rw [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.mul_im]
  rw [Complex.normSq_apply]
  ring

/-- A nonzero vector gives a strictly positive imaginary diagonal quadratic
form when all diagonal entries lie in the open upper half-plane.
@isnad1 id=lt.2h3v.s6.fc5f9d6f73c3 from=translated src=- shape=11904974 vocab=bb6ac422
-/
theorem im_star_dotProduct_diagonal_mulVec_pos
    {n : Type*} [Fintype n] [DecidableEq n]
    (z v : n → ℂ) (hz : ∀ i, 0 < (z i).im) (hv : v ≠ 0) :
    0 < (star v ⬝ᵥ (Matrix.diagonal z *ᵥ v)).im := by
  rw [im_star_dotProduct_diagonal_mulVec]
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (Complex.normSq_nonneg _) (hz j).le
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    exact mul_pos (Complex.normSq_pos.mpr hi) (hz i)

/-- If `A` is Hermitian and every `z i` is in the open upper half-plane,
then `diag z - A` is nonsingular.
@isnad1 id=ne.2h3v.s6.227d3b22f3ff from=translated src=- shape=04eae98c vocab=e9d32f0b
-/
theorem det_diagonal_sub_hermitian_ne_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (z : n → ℂ) (hz : ∀ i, 0 < (z i).im) :
    (Matrix.diagonal z - A).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hker⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hquad : star v ⬝ᵥ ((Matrix.diagonal z - A) *ᵥ v) = 0 := by
    rw [hker, dotProduct_zero]
  have himquad :
      (star v ⬝ᵥ (Matrix.diagonal z *ᵥ v)).im -
        (star v ⬝ᵥ (A *ᵥ v)).im = 0 := by
    have h := congrArg Complex.im hquad
    simpa only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im,
      Complex.zero_im] using h
  have himA : (star v ⬝ᵥ (A *ᵥ v)).im = 0 :=
    hA.im_star_dotProduct_mulVec_self v
  have himDiag : (star v ⬝ᵥ (Matrix.diagonal z *ᵥ v)).im = 0 := by
    linarith
  exact (ne_of_gt (im_star_dotProduct_diagonal_mulVec_pos z v hz hv)) himDiag

/-- Definite determinantal polynomials of Hermitian matrices are complex
stable.
@isnad1 id=complexs.1h2v.s5.f7d782965d9e from=translated src=- shape=9daa187a vocab=6b7384fb
-/
theorem hermitianDetPoly_complexStable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ComplexStable (hermitianDetPoly A) := by
  intro z hz
  rw [eval_hermitianDetPoly]
  exact det_diagonal_sub_hermitian_ne_zero A hA z hz

/-- Hermitian symmetry makes every coefficient of the determinantal
polynomial fixed by complex conjugation.
@isnad1 id=eq.1h2v.s7.f26b8d647962 from=translated src=- shape=39261b5e vocab=ce205cae
-/
theorem map_star_hermitianDetPoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    MvPolynomial.map (starRingEnd ℂ) (hermitianDetPoly A) =
      hermitianDetPoly A := by
  unfold hermitianDetPoly
  rw [RingHom.map_det]
  calc
    ((MvPolynomial.map (starRingEnd ℂ)).mapMatrix
        (Matrix.diagonal (fun i => MvPolynomial.X i) -
          A.map MvPolynomial.C)).det =
        (Matrix.diagonal (fun i => MvPolynomial.X i) -
          A.map MvPolynomial.C).transpose.det := by
      congr 1
      apply Matrix.ext
      intro i j
      by_cases hij : i = j
      · subst j
        have hd : star (A i i) = A i i := hA.apply i i
        simp [starRingEnd_apply, hd]
      · have hentry : star (A i j) = A j i := hA.apply j i
        simp [hij, Ne.symm hij, starRingEnd_apply, hentry]
    _ = _ := Matrix.det_transpose _

end CommutatorTheorem.BTDeterminantStability
