import Tengoku.AbelFormalization.AbelFormalization.ContourFunctional
import Tengoku.AbelFormalization.AbelFormalization.HermiteAnalytic
import Tengoku.AbelFormalization.AbelFormalization.HermiteContour
import Tengoku.Seed.Topology.ContinuousMap.Units

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analytic dependence of the integrated Hermite coefficients

We work in the Banach algebra of continuous complex functions on the contour.
The denominator and numerator are polynomial maps of the nodes with values in
that algebra. At a tuple with no node on the contour, the denominator is a unit.
Analytic inversion followed by the bounded linear contour functional proves
multivariable analyticity of the actual contour coefficients.
-/

noncomputable section

namespace AbelFormalization

open Set Metric Polynomial
open scoped Topology

/-- The coordinate function on the contour circle.-/
def contourCoordinate (R : ℝ) : C(sphere (0 : ℂ) R, ℂ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/--
@isnad1 id=eq.0h2v.s7.1a43c8e1fa48 from=translated src=- shape=518398a3 vocab=cd818fda
-/
@[simp]
theorem contourCoordinate_apply (R : ℝ) (z : sphere (0 : ℂ) R) :
    contourCoordinate R z = z := rfl

variable {ι : Type*} [Fintype ι]

/-- The node polynomial restricted to the contour, expressed in its Banach algebra.-/
def nodeContourDenominator (R : ℝ) (δ : ι → ℂ) (m : ι → ℕ) :
    C(sphere (0 : ℂ) R, ℂ) :=
  ∏ i, (contourCoordinate R - δ i • 1) ^ m i

/--
@isnad1 id=eq.0h5v.s8.d801ec615ea9 from=translated src=- shape=32b7fd2b vocab=80061936
-/
@[simp]
theorem nodeContourDenominator_apply (R : ℝ) (δ : ι → ℂ) (m : ι → ℕ)
    (z : sphere (0 : ℂ) R) :
    nodeContourDenominator R δ m z = (nodePolynomial δ m).eval (z : ℂ) := by
  simp [nodeContourDenominator, nodePolynomial_eval]

/-- The coefficient numerator, expressed in the contour Banach algebra.-/
def nodeContourNumerator (R : ℝ) (δ : ι → ℂ) (m : ι → ℕ) (j : ℕ) :
    C(sphere (0 : ℂ) R, ℂ) :=
  ∑ i ∈ Finset.Icc (j + 1) (totalMultiplicity m),
    (nodePolynomial δ m).coeff i • contourCoordinate R ^ (i - (j + 1))

/--
@isnad1 id=eq.0h6v.s8.2be657d179d5 from=translated src=- shape=8c99d21f vocab=b0acae6e
-/
@[simp]
theorem nodeContourNumerator_apply (R : ℝ) (δ : ι → ℂ) (m : ι → ℕ) (j : ℕ)
    (z : sphere (0 : ℂ) R) :
    nodeContourNumerator R δ m j z = (hermiteKernel (nodePolynomial δ m) z).coeff j := by
  simp [nodeContourNumerator, hermiteKernel_coeff, nodePolynomial_natDegree, mul_comm]

/-- The denominator is an entire map into the Banach algebra of contour functions.
@isnad1 id=analytic.0h4v.s8.4d9c6bc7e5eb from=translated src=- shape=3e22d005 vocab=1b94c303
-/
theorem analyticAt_nodeContourDenominator (R : ℝ) (m : ι → ℕ) (δ : ι → ℂ) :
    AnalyticAt ℂ (fun ε : ι → ℂ => nodeContourDenominator R ε m) δ := by
  unfold nodeContourDenominator
  apply Finset.analyticAt_fun_prod
  intro i _
  apply AnalyticAt.fun_pow
  apply AnalyticAt.fun_sub analyticAt_const
  have hp : AnalyticAt ℂ (fun ε : ι → ℂ => ε i) δ := by
    exact ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt δ).congr
      (Filter.Eventually.of_forall fun ε => ContinuousLinearMap.proj_apply i ε)
  exact hp.fun_smul analyticAt_const

/-- The numerator is an entire map into the same Banach algebra.
@isnad1 id=analytic.0h5v.s8.92c650d93495 from=translated src=- shape=7106bc19 vocab=87e36610
-/
theorem analyticAt_nodeContourNumerator (R : ℝ) (m : ι → ℕ) (j : ℕ) (δ : ι → ℂ) :
    AnalyticAt ℂ (fun ε : ι → ℂ => nodeContourNumerator R ε m j) δ := by
  unfold nodeContourNumerator
  exact Finset.analyticAt_fun_sum _ fun i _ =>
    (analyticAt_nodePolynomial_coeff m i δ).fun_smul analyticAt_const

/--
@isnad1 id=isunit.1h4v.s7.82f1f382bfe3 from=translated src=- shape=a9c1aef2 vocab=ee8ffb0a
-/
theorem isUnit_nodeContourDenominator (R : ℝ) (δ : ι → ℂ) (m : ι → ℕ)
    (h : ∀ z ∈ sphere (0 : ℂ) R, (nodePolynomial δ m).eval z ≠ 0) :
    IsUnit (nodeContourDenominator R δ m) := by
  apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
  intro z
  rw [nodeContourDenominator_apply]
  exact h z z.property

/-- Inverting a unit continuous function agrees pointwise with scalar inversion.
@isnad1 id=eq.1h3v.s7.9c8e90dd65f1 from=translated src=- shape=90a7b669 vocab=d81f51d0
-/
theorem continuousMap_ringInverse_apply {X : Type*} [TopologicalSpace X]
    (g : C(X, ℂ)) (hg : IsUnit g) (z : X) :
    Ring.inverse g z = (g z)⁻¹ := by
  have hz := ((ContinuousMap.isUnit_iff_forall_ne_zero g).mp hg) z
  have hm := congrArg (fun f : C(X, ℂ) => f z) (Ring.mul_inverse_cancel g hg)
  simp only [ContinuousMap.mul_apply, ContinuousMap.one_apply] at hm
  apply mul_left_cancel₀ hz
  simpa only [mul_inv_cancel₀ hz] using hm

/-- The Banach-algebra version of the coefficient kernel.-/
def hermiteContourKernelMap (R : ℝ) (δ : ι → ℂ) (m : ι → ℕ) (j : ℕ) :
    C(sphere (0 : ℂ) R, ℂ) :=
  nodeContourNumerator R δ m j * Ring.inverse (nodeContourDenominator R δ m)

/-- Analytic Banach-valued coefficient kernels at every invertible denominator.
@isnad1 id=analytic.1h5v.s8.33c35b8768c5 from=translated src=- shape=5ec7e0a2 vocab=ac655f26
-/
theorem analyticAt_hermiteContourKernelMap (R : ℝ) (m : ι → ℕ) (j : ℕ) (δ : ι → ℂ)
    (h : IsUnit (nodeContourDenominator R δ m)) :
    AnalyticAt ℂ (fun ε : ι → ℂ => hermiteContourKernelMap R ε m j) δ := by
  have hi : AnalyticAt ℂ Ring.inverse (nodeContourDenominator R δ m) :=
    analyticOnNhd_inverse _ h
  exact (analyticAt_nodeContourNumerator R m j δ).fun_mul
    (hi.fun_comp (f := fun ε : ι → ℂ => nodeContourDenominator R ε m)
      (analyticAt_nodeContourDenominator R m δ))

end AbelFormalization
