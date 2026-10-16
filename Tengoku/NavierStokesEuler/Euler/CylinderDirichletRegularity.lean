import Tengoku.NavierStokesEuler.Euler.CylinderDirichletTranslation
import Tengoku.NavierStokesEuler.Euler.FixedEvolutionRegularity

/-!
# Actual mixed-translation smoothness of the cylinder history

The translated variational problems live on one fixed Hilbert space.
Smoothness follows from their genuine coercive inverses, and exact covariance
identifies that family with the translation orbit of the constructed field.
No regularity assumption is imposed on a solved history field.
-/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerTimeLpBoundedMap EulerVolterraConvolution EulerMeanCoefficients
open scoped BoundedContinuousFunction ContDiff

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

private local instance : NormedAddCommGroup (CylinderL2 P U) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P U) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P U →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P U →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P E →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P E →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E) := inferInstance

omit [CompleteSpace U] [CompleteSpace E] in
theorem frameOrbit_contDiff (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => (D.shifted a.1).frame P) :=
  (fullPathMap (K := Icc (0 : ℝ) T) (E := U) (F := E) P).contDiff.comp
    (hQ.comp contDiff_fst)

omit [CompleteSpace U] [CompleteSpace E] in
theorem frameDerivativeOrbit_contDiff (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => (D.shifted a.1).frameDerivative P) :=
  (fullPathMap (K := Icc (0 : ℝ) T) (E := U) (F := E) P).contDiff.comp
    (hQ₁.comp contDiff_fst)

omit [CompleteSpace U] [CompleteSpace E] in
theorem hessianOrbit_contDiff (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => (D.shifted a.1).hessian P) :=
  (fullPathMap (K := Icc (0 : ℝ) T) (E := E) (F := E) P).contDiff.comp
    (hH.comp contDiff_fst)

variable (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q))
  (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁))
  (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H))

include hQ hQ₁ hH

end EulerCylinderDirichlet.Coefficients
