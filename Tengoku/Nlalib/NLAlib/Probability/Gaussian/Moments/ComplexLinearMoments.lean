import Tengoku.Nlalib.NLAlib.Probability.Gaussian.Basic.StandardVector
import Tengoku.Seed.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Tengoku.Seed.Data.Complex.BigOperators
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complex linear forms of real standard Gaussian coordinates

These are actual functions under the canonical Gaussian product law, with
real continuous linear maps, Gaussian law, zero mean, integrable pair products,
and exact complex bilinear covariance (without conjugation).
These lemmas extend the real second-moment identities in `Basic.StandardVector`
to complex coefficient linear forms.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- A complex linear form of actual real standard Gaussian coordinates.
Its second moment below is bilinear, without complex conjugation.-/
def complexGaussianLinearForm {κ : Type*} [Fintype κ]
    (a : κ → ℂ) (x : κ → ℝ) : ℂ :=
  ∑ k, a k * (x k : ℂ)

/-- The real continuous linear map underlying a complex Gaussian linear form.-/
def complexGaussianLinearFormCLM {κ : Type*} [Fintype κ] (a : κ → ℂ) :
    (κ → ℝ) →L[ℝ] ℂ := by
  classical
  exact ∑ k, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) k).smulRight (a k)

/-- Evaluate the continuous linear map as its actual finite Gaussian linear form.
@isnad1 id=eq.0h3v.s7.a1f0ced6727a from=translated src=- shape=574830ba vocab=039acbfb
-/
@[simp] theorem complexGaussianLinearFormCLM_apply
    {κ : Type*} [Fintype κ] (a : κ → ℂ) (x : κ → ℝ) :
    complexGaussianLinearFormCLM a x = complexGaussianLinearForm a x := by
  classical
  simp [complexGaussianLinearFormCLM, complexGaussianLinearForm, mul_comm]

/-- Every complex linear form has an actual Gaussian law as a real vector.
@isnad1 id=hasgauss.0h2v.s6.ee4b776f2916 from=translated src=- shape=0ede9071 vocab=91755bc9
-/
theorem hasGaussianLaw_complexGaussianLinearForm
    {κ : Type*} [Fintype κ] (a : κ → ℂ) :
    HasGaussianLaw (complexGaussianLinearForm a) (gaussianVector κ) := by
  simpa only [complexGaussianLinearFormCLM_apply] using
    (hasGaussianLaw_id_gaussianVector κ).map_fun (complexGaussianLinearFormCLM a)

/-- The actual mean of a complex linear form of centered standard coordinates is zero.
@isnad1 id=eq.0h2v.s5.5a8d8539713b from=translated src=- shape=8e182816 vocab=e263f255
-/
theorem integral_complexGaussianLinearForm_eq_zero
    {κ : Type*} [Fintype κ] (a : κ → ℂ) :
    (∫ x : κ → ℝ, complexGaussianLinearForm a x ∂gaussianVector κ) = 0 := by
  classical
  have hint (k : κ) : Integrable (fun x : κ → ℝ => (x k : ℂ)) (gaussianVector κ) :=
    ((memLp_two_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector k)).integrable one_le_two).ofReal
  have hzero (k : κ) : (∫ x : κ → ℝ, x k ∂gaussianVector κ) = 0 :=
    integral_eq_zero_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector k)
  change (∫ x : κ → ℝ, ∑ k, a k * (x k : ℂ) ∂gaussianVector κ) = 0
  rw [integral_finsetSum _ (fun k _ => (hint k).const_mul (a k))]
  simp only [integral_const_mul, integral_complex_ofReal, hzero,
    Complex.ofReal_zero, mul_zero, Finset.sum_const_zero]

/-- Products of two actual complex Gaussian linear forms are integrable.
@isnad1 id=integrab.0h3v.s6.08588ceb3742 from=translated src=- shape=09b82f34 vocab=3e8923a8
-/
theorem integrable_complexGaussianLinearForm_mul
    {κ : Type*} [Fintype κ] (a b : κ → ℂ) :
    Integrable (fun x : κ → ℝ =>
      complexGaussianLinearForm a x * complexGaussianLinearForm b x)
      (gaussianVector κ) := by
  classical
  have hexp : (fun x : κ → ℝ =>
      complexGaussianLinearForm a x * complexGaussianLinearForm b x) =
      fun x => ∑ i, ∑ j, (a i * b j) * ((x i * x j : ℝ) : ℂ) := by
    funext x
    simp only [complexGaussianLinearForm, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [hexp]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_mul_apply_gaussianVector i j).ofReal.const_mul (a i * b j)

/-- Exact complex bilinear covariance of two linear forms of actual standard
real Gaussian coordinates. This is the normalization input for GUE Wick.
@isnad1 id=eq.0h3v.s6.40e90ff41a82 from=translated src=- shape=2f8c2b72 vocab=30024700
-/
theorem integral_complexGaussianLinearForm_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] (a b : κ → ℂ) :
    (∫ x : κ → ℝ, complexGaussianLinearForm a x * complexGaussianLinearForm b x
      ∂gaussianVector κ) = a ⬝ᵥ b := by
  have hexp : (fun x : κ → ℝ =>
      complexGaussianLinearForm a x * complexGaussianLinearForm b x) =
      fun x => ∑ i, ∑ j, (a i * b j) * ((x i * x j : ℝ) : ℂ) := by
    funext x
    simp only [complexGaussianLinearForm, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  have hint (i j : κ) : Integrable
      (fun x : κ → ℝ => (a i * b j) * ((x i * x j : ℝ) : ℂ))
      (gaussianVector κ) :=
    (integrable_mul_apply_gaussianVector i j).ofReal.const_mul (a i * b j)
  rw [hexp, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => hint i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j),
    integral_const_mul, integral_complex_ofReal, integral_mul_apply_gaussianVector]
  simp [dotProduct, apply_ite]

end NLAlib
