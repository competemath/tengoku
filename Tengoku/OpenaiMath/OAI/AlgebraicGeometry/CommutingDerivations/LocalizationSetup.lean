import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.CommutingDerivations.ParameterBezout
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.AbhyankarSathaye.Reconstruction
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.AbhyankarSathaye.Quotient
import Tengoku

namespace OAI

/-!
The Laurent coefficient algebra and localization coordinates.
The coefficient map is the lift of `t ↦ F + 1`.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

def ambientC : R := F + 1
abbrev LocalizedAmbient := Localization.Away ambientC
abbrev LaurentCoefficients := Localization.Away (Polynomial.X : Polynomial ℂ)
abbrev RelativePlane := MvPolynomial (Fin 3) LaurentCoefficients

def loc : R →+* LocalizedAmbient := algebraMap R LocalizedAmbient
def coefficientC : LaurentCoefficients :=
  algebraMap (Polynomial ℂ) LaurentCoefficients Polynomial.X
def coefficientD : LaurentCoefficients :=
  IsLocalization.Away.invSelf (Polynomial.X : Polynomial ℂ)
def localD : LocalizedAmbient := IsLocalization.Away.invSelf ambientC

/--
@isnad1 id=eq.0h0v.s7.47f6d0bd214e from=translated src=- shape=33aceabd vocab=979f7bc6
-/
theorem coefficient_unit : coefficientC * coefficientD = 1 :=
  IsLocalization.Away.mul_invSelf _

/--
@isnad1 id=eq.0h0v.s9.233ac8e2f895 from=translated src=- shape=dad3f95b vocab=639eb2a7
-/
theorem local_unit : loc ambientC * localD = 1 :=
  IsLocalization.Away.mul_invSelf _

def polynomialCoefficientMap : Polynomial ℂ →+* LocalizedAmbient :=
  (Polynomial.aeval (loc ambientC)).toRingHom

def coefficientMap : LaurentCoefficients →+* LocalizedAmbient :=
  IsLocalization.Away.lift Polynomial.X
    (by
      refine ⟨⟨polynomialCoefficientMap Polynomial.X, localD, ?_, ?_⟩, rfl⟩
      · simpa [polynomialCoefficientMap] using local_unit
      · simpa [polynomialCoefficientMap, mul_comm] using local_unit)

/--
@isnad1 id=eq.0h0v.s9.d6ffe0f4685d from=translated src=- shape=4ea32f46 vocab=53196f47
-/
@[simp] theorem coefficientMap_C : coefficientMap coefficientC = loc ambientC := by
  simp [coefficientMap, coefficientC, polynomialCoefficientMap]

/--
@isnad1 id=eq.0h0v.s8.ca950a1f675b from=translated src=- shape=501f93a1 vocab=de8a42eb
-/
@[simp] theorem coefficientMap_D : coefficientMap coefficientD = localD := by
  have h1 : loc ambientC * coefficientMap coefficientD = 1 := by
    simpa using congrArg coefficientMap coefficient_unit
  calc
    coefficientMap coefficientD = (loc ambientC * localD) * coefficientMap coefficientD := by
      rw [local_unit, one_mul]
    _ = localD * (loc ambientC * coefficientMap coefficientD) := by ring
    _ = localD := by rw [h1, mul_one]

def localAlpha : LocalizedAmbient := localD^2 * parameterA (loc ambientC) (loc x) (loc s)
def localBeta : LocalizedAmbient :=
  localD^2 * parameterB (loc ambientC) (loc x) (loc y) (loc s)
def localT : LocalizedAmbient := parameter localAlpha localBeta (loc u) (loc v) (loc w)
def localCoordinates : Fin 3 → LocalizedAmbient := ![loc shiftX, loc shiftY, localT]

/--
@isnad1 id=eq.0h0v.s10.51680c8af736 from=translated src=- shape=386d5a4a vocab=ad6c4386
-/
theorem local_cusp : (loc x)^2 + (loc y)^3 = loc s * loc h := by
  simpa [mul_comm] using congrArg loc cusp

/--
@isnad1 id=eq.0h0v.s10.1e57f8c546dd from=translated src=- shape=9afadb2f vocab=9bd6937f
-/
theorem local_section : loc h = loc ambientC + P (loc x) (loc y) (loc s) := by
  have he : h = ambientC + P x y s := by unfold ambientC F p; ring
  simpa using congrArg loc he

/--
@isnad1 id=eq.0h0v.s10.65e008201567 from=translated src=- shape=22977525 vocab=e0abfed2
-/
theorem local_bezout : localAlpha * loc h + localBeta * loc y = 1 :=
  parameter_bezout_unit _ _ _ _ _ _ local_cusp local_section local_unit

/--
@isnad1 id=eq.0h0v.s10.71ebc0e0c6b0 from=translated src=- shape=a505f39d vocab=55a844c7
-/
theorem local_recover_s : localD * ((loc shiftX)^2 + (loc shiftY)^3) = loc s := by
  simpa [shiftX, shiftY] using
    parameter_recover_s _ _ _ _ _ _ local_cusp local_section local_unit

/-- Evaluation at the displayed X,Y,T, with the explicit relative coefficient map. -/
def relativeBackward : RelativePlane →+* LocalizedAmbient :=
  eval₂Hom coefficientMap localCoordinates

/--
@isnad1 id=eq.0h1v.s10.fea48c5c1d28 from=translated src=- shape=bfc7bf48 vocab=9cbd35e1
-/
@[simp] theorem relativeBackward_C (a : LaurentCoefficients) :
    relativeBackward (C a) = coefficientMap a := by
  simp [relativeBackward]

/--
@isnad1 id=eq.0h1v.s8.40c110025ca7 from=translated src=- shape=dbf39def vocab=a054ef42
-/
@[simp] theorem relativeBackward_X (i : Fin 3) :
    relativeBackward (X i) = localCoordinates i := by
  simp [relativeBackward]

/-- A relative algebra equivalence over `ℂ[c,c⁻¹]`, with `c = F + 1`,
and its coordinate equations. -/
def RelativeLocalizationContract : Prop :=
  ∃ e : LocalizedAmbient ≃+* RelativePlane,
    (∀ a, e (coefficientMap a) = C a) ∧
    e (loc shiftX) = X 0 ∧ e (loc shiftY) = X 1 ∧ e localT = X 2 ∧
    e.symm.toRingHom = relativeBackward

end AbhyankarSathaye.CommutingDerivations

end

end OAI
