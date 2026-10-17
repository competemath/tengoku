import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.CommutingDerivations.LocalizationSetup
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.CommutingDerivations.ParameterBridge

namespace OAI

/-!
Explicit maps between the ambient localization and the polynomial algebra
over Laurent coefficients, using the unrestricted reconstruction formulas.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

def ambientToFree : R →+* RelativePlane :=
  eval₂Hom (C.comp (algebraMap ℂ LaurentCoefficients))
    (ParameterBridge.values LaurentCoefficients coefficientC coefficientD)

/--
@isnad1 id=eq.0h1v.s10.66a3bdef856c from=translated src=- shape=b8a78bc3 vocab=f4ecb7c5
-/
@[simp] theorem ambientToFree_constant (a : ℂ) :
    ambientToFree (C a) = C (algebraMap ℂ LaurentCoefficients a) := by
  simp [ambientToFree]

/--
@isnad1 id=eq.0h0v.s8.a6bcc398bfa7 from=translated src=- shape=b049e67f vocab=15c5c51b
-/
@[simp] theorem ambientToFree_h :
    ambientToFree h = ParameterBridge.freeH LaurentCoefficients coefficientC coefficientD := by
  simp [ambientToFree, h, ParameterBridge.values]
/--
@isnad1 id=eq.0h0v.s8.b5b6dca6c54a from=translated src=- shape=b049e67f vocab=60d307bf
-/
@[simp] theorem ambientToFree_u :
    ambientToFree u = ParameterBridge.freeU LaurentCoefficients coefficientC coefficientD := by
  simp [ambientToFree, u, ParameterBridge.values]
/--
@isnad1 id=eq.0h0v.s8.5fa66ba32b50 from=translated src=- shape=b049e67f vocab=a641e678
-/
@[simp] theorem ambientToFree_v :
    ambientToFree v = ParameterBridge.freeV LaurentCoefficients coefficientC coefficientD := by
  simp [ambientToFree, v, ParameterBridge.values]
/--
@isnad1 id=eq.0h0v.s8.af4a5f32b2e3 from=translated src=- shape=b049e67f vocab=0ad2f73f
-/
@[simp] theorem ambientToFree_w :
    ambientToFree w = ParameterBridge.freeW LaurentCoefficients coefficientC coefficientD := by
  simp [ambientToFree, w, ParameterBridge.values]
/--
@isnad1 id=eq.0h0v.s8.09fbe96579e5 from=translated src=- shape=67234e75 vocab=aaf71ab4
-/
@[simp] theorem ambientToFree_x : ambientToFree x = ParameterBridge.freeX LaurentCoefficients coefficientD := by
  simpa [x] using (ParameterBridge.free_relations _ _ _ coefficient_unit).1
/--
@isnad1 id=eq.0h0v.s8.c25bd77386b0 from=translated src=- shape=67234e75 vocab=dd4bb6fb
-/
@[simp] theorem ambientToFree_y : ambientToFree y = ParameterBridge.freeY LaurentCoefficients coefficientD := by
  simpa [y] using (ParameterBridge.free_relations _ _ _ coefficient_unit).2.1
/--
@isnad1 id=eq.0h0v.s8.34d1d18d9527 from=translated src=- shape=67234e75 vocab=b113e54c
-/
@[simp] theorem ambientToFree_s : ambientToFree s = ParameterBridge.freeS LaurentCoefficients coefficientD := by
  simpa [s] using (ParameterBridge.free_relations _ _ _ coefficient_unit).2.2

/--
@isnad1 id=eq.0h0v.s9.566d078f7b79 from=translated src=- shape=595cbb25 vocab=02171a58
-/
@[simp] theorem ambientToFree_c : ambientToFree ambientC = C coefficientC := by
  simp [ambientC, F, p, ParameterBridge.freeH]

/--
@isnad1 id=eq.0h0v.s8.08dc4510b67d from=translated src=- shape=d6f76674 vocab=4a897382
-/
@[simp] theorem ambientToFree_shiftX : ambientToFree shiftX = X 0 := by
  simp [shiftX, ParameterBridge.freeX]
/--
@isnad1 id=eq.0h0v.s8.2f21bd0b8554 from=translated src=- shape=d6f76674 vocab=fb3c3b72
-/
@[simp] theorem ambientToFree_shiftY : ambientToFree shiftY = X 1 := by
  simp [shiftY, ParameterBridge.freeY]

/--
@isnad1 id=eq.0h1v.s9.ef7fd57c5179 from=translated src=- shape=96979b01 vocab=b3bd9797
-/
@[simp] theorem coefficientMap_complex (a : ℂ) :
    coefficientMap (algebraMap ℂ LaurentCoefficients a) = loc (C a) := by
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) LaurentCoefficients]
  change coefficientMap (algebraMap (Polynomial ℂ) LaurentCoefficients (Polynomial.C a)) = _
  simp [coefficientMap, polynomialCoefficientMap, loc,
    IsScalarTower.algebraMap_apply ℂ R LocalizedAmbient]

def relativeForward : LocalizedAmbient →+* RelativePlane :=
  IsLocalization.Away.lift ambientC
    (show IsUnit (ambientToFree ambientC) by
      rw [ambientToFree_c]
      exact (IsUnit.of_mul_eq_one coefficientD coefficient_unit).map C)

/--
@isnad1 id=eq.0h1v.s9.76bb38adefad from=translated src=- shape=390f4ebc vocab=b5ed63e5
-/
@[simp] theorem relativeForward_loc (f : R) : relativeForward (loc f) = ambientToFree f := by
  simp [relativeForward, loc]

/--
@isnad1 id=eq.0h0v.s8.b06d2c715ce0 from=translated src=- shape=5362e07c vocab=c925e5ae
-/
theorem relativeForward_coefficientMap :
    relativeForward.comp coefficientMap = (C : LaurentCoefficients →+* RelativePlane) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial ℂ))
  apply Polynomial.ringHom_ext
  · intro a
    simp [coefficientMap, polynomialCoefficientMap, relativeForward, ambientToFree,
      IsScalarTower.algebraMap_apply ℂ R LocalizedAmbient,
      IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) LaurentCoefficients]
  · simp [coefficientMap, polynomialCoefficientMap, coefficientC]

/--
@isnad1 id=eq.0h1v.s10.45bf12e5d04b from=translated src=- shape=4366ec8a vocab=312101b5
-/
@[simp] theorem relativeForward_coefficient (a : LaurentCoefficients) :
    relativeForward (coefficientMap a) = C a :=
  RingHom.congr_fun relativeForward_coefficientMap a

/--
@isnad1 id=eq.0h0v.s9.fd9c12135a7b from=translated src=- shape=595cbb25 vocab=48483ecb
-/
@[simp] theorem relativeForward_d : relativeForward localD = C coefficientD := by
  rw [← coefficientMap_D, relativeForward_coefficient]

/--
@isnad1 id=eq.0h0v.s8.677c454afb40 from=translated src=- shape=b049e67f vocab=a931be78
-/
@[simp] theorem relativeForward_alpha :
    relativeForward localAlpha = ParameterBridge.freeAlpha LaurentCoefficients coefficientC coefficientD := by
  simp [localAlpha, ParameterBridge.freeAlpha]
/--
@isnad1 id=eq.0h0v.s8.38755be43269 from=translated src=- shape=b049e67f vocab=5e789114
-/
@[simp] theorem relativeForward_beta :
    relativeForward localBeta = ParameterBridge.freeBeta LaurentCoefficients coefficientC coefficientD := by
  simp [localBeta, ParameterBridge.freeBeta]

/--
@isnad1 id=eq.0h0v.s9.e112b04afc09 from=translated src=- shape=4d3f1e31 vocab=d3051275
-/
@[simp] theorem relativeForward_shiftX : relativeForward (loc shiftX) = X 0 := by
  simp [shiftX, ParameterBridge.freeX]
/--
@isnad1 id=eq.0h0v.s9.cceffce80f8b from=translated src=- shape=4d3f1e31 vocab=abaf9b7b
-/
@[simp] theorem relativeForward_shiftY : relativeForward (loc shiftY) = X 1 := by
  simp [shiftY, ParameterBridge.freeY]
/--
@isnad1 id=eq.0h0v.s8.c785ca6d2dd5 from=translated src=- shape=d6f76674 vocab=d68be6b2
-/
@[simp] theorem relativeForward_T : relativeForward localT = X 2 := by
  simpa [localT, ParameterBridge.freeU, ParameterBridge.freeV, ParameterBridge.freeW, ParameterBridge.freeG] using
    (inverse_parameter
      (ParameterBridge.freeH LaurentCoefficients coefficientC coefficientD)
      (ParameterBridge.freeX LaurentCoefficients coefficientD)
      (ParameterBridge.freeY LaurentCoefficients coefficientD)
      (ParameterBridge.freeS LaurentCoefficients coefficientD)
      (ParameterBridge.freeAlpha LaurentCoefficients coefficientC coefficientD)
      (ParameterBridge.freeBeta LaurentCoefficients coefficientC coefficientD) (X 2 : RelativePlane)
      (ParameterBridge.free_bezout LaurentCoefficients coefficientC coefficientD coefficient_unit))

/--
@isnad1 id=eq.0h0v.s9.3fb365a1ef4d from=translated src=- shape=12c378ba vocab=d33fc684
-/
theorem relativeForward_backward :
    relativeForward.comp relativeBackward = RingHom.id RelativePlane := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    fin_cases i <;> simp [localCoordinates]

/--
@isnad1 id=eq.0h0v.s9.b0e15948ea2d from=translated src=- shape=7e773be5 vocab=ccf34768
-/
@[simp] theorem relativeBackward_freeS :
    relativeBackward (ParameterBridge.freeS LaurentCoefficients coefficientD) = loc s := by
  simpa [ParameterBridge.freeS, localCoordinates] using local_recover_s
/--
@isnad1 id=eq.0h0v.s9.78f52ebc0256 from=translated src=- shape=7e773be5 vocab=dd31d8a6
-/
@[simp] theorem relativeBackward_freeX :
    relativeBackward (ParameterBridge.freeX LaurentCoefficients coefficientD) = loc x := by
  simp [ParameterBridge.freeX, localCoordinates, shiftX]
/--
@isnad1 id=eq.0h0v.s9.a9b88cac21d7 from=translated src=- shape=7e773be5 vocab=7c0ad47a
-/
@[simp] theorem relativeBackward_freeY :
    relativeBackward (ParameterBridge.freeY LaurentCoefficients coefficientD) = loc y := by
  simp [ParameterBridge.freeY, localCoordinates, shiftY]
/--
@isnad1 id=eq.0h0v.s9.c3597896dd79 from=translated src=- shape=b4b2e001 vocab=5df93194
-/
@[simp] theorem relativeBackward_freeH :
    relativeBackward (ParameterBridge.freeH LaurentCoefficients coefficientC coefficientD) = loc h := by
  simpa [ParameterBridge.freeH] using local_section.symm
/--
@isnad1 id=eq.0h0v.s8.faeadd9f1be7 from=translated src=- shape=7b50d794 vocab=02a11e43
-/
@[simp] theorem relativeBackward_freeAlpha :
    relativeBackward (ParameterBridge.freeAlpha LaurentCoefficients coefficientC coefficientD) = localAlpha := by
  simp [ParameterBridge.freeAlpha, localAlpha]
/--
@isnad1 id=eq.0h0v.s8.68e4df5f4bcc from=translated src=- shape=7b50d794 vocab=84902d32
-/
@[simp] theorem relativeBackward_freeBeta :
    relativeBackward (ParameterBridge.freeBeta LaurentCoefficients coefficientC coefficientD) = localBeta := by
  simp [ParameterBridge.freeBeta, localBeta]

/--
@isnad1 id=and.0h0v.s11.d7a49f74cc88 from=translated src=- shape=6456c0f8 vocab=5bdee620
-/
theorem relativeBackward_free_original :
    relativeBackward (ParameterBridge.freeU LaurentCoefficients coefficientC coefficientD) = loc u ∧
    relativeBackward (ParameterBridge.freeV LaurentCoefficients coefficientC coefficientD) = loc v ∧
    relativeBackward (ParameterBridge.freeW LaurentCoefficients coefficientC coefficientD) = loc w := by
  have hx : (loc u)^3 + loc h * loc v = loc x := by simp [x]
  have hy : -(loc u)^2 + loc h * loc w = loc y := by simp [y]
  have hs : S (loc h) (loc u) (loc v) (loc w) = loc s := by simp [s]
  simpa [ParameterBridge.freeU, ParameterBridge.freeV, ParameterBridge.freeW, ParameterBridge.freeG, localCoordinates, localT] using
    original_reconstruction (loc h) (loc x) (loc y) (loc s) localAlpha localBeta
      (loc u) (loc v) (loc w) local_bezout hx hy hs

/--
@isnad1 id=eq.0h0v.s9.d98fa80fba32 from=translated src=- shape=4aefcdc6 vocab=d33fc684
-/
theorem relativeBackward_forward :
    relativeBackward.comp relativeForward = RingHom.id LocalizedAmbient := by
  apply IsLocalization.ringHom_ext (Submonoid.powers ambientC)
  apply MvPolynomial.ringHom_ext
  · intro a
    change relativeBackward (relativeForward (loc (C a))) = loc (C a)
    rw [relativeForward_loc, ambientToFree_constant, relativeBackward_C, coefficientMap_complex]
  · intro i
    obtain ⟨hu, hv, hw⟩ := relativeBackward_free_original
    change relativeBackward (relativeForward (loc (X i))) = loc (X i)
    fin_cases i
    · change relativeBackward (relativeForward (loc h)) = loc h
      rw [relativeForward_loc, ambientToFree_h]
      exact relativeBackward_freeH
    · change relativeBackward (relativeForward (loc u)) = loc u
      rw [relativeForward_loc, ambientToFree_u]
      exact hu
    · change relativeBackward (relativeForward (loc v)) = loc v
      rw [relativeForward_loc, ambientToFree_v]
      exact hv
    · change relativeBackward (relativeForward (loc w)) = loc w
      rw [relativeForward_loc, ambientToFree_w]
      exact hw

/-- Actual localized ring equivalence, with explicit maps and both composites. -/
def localizationRingEquiv : LocalizedAmbient ≃+* RelativePlane :=
  RingEquiv.ofRingHom relativeForward relativeBackward
    relativeForward_backward relativeBackward_forward

/-- The algebra structure is exactly the specified map c ↦ F+1. -/
def relativeAlgebra : Algebra LaurentCoefficients LocalizedAmbient := coefficientMap.toAlgebra

/-- Actual equivalence over the Laurent coefficient ring. -/
def localizationEquiv :
    letI := relativeAlgebra
    LocalizedAmbient ≃ₐ[LaurentCoefficients] RelativePlane :=
  letI := relativeAlgebra
  { localizationRingEquiv with
    commutes' := relativeForward_coefficient }

/-- The same explicit equivalence also preserves the original complex scalars. -/
def localizationComplexEquiv : LocalizedAmbient ≃ₐ[ℂ] RelativePlane :=
  { localizationRingEquiv with
    commutes' := by
      intro a
      change relativeForward (algebraMap ℂ LocalizedAmbient a) =
        algebraMap ℂ RelativePlane a
      rw [IsScalarTower.algebraMap_apply ℂ R LocalizedAmbient]
      change relativeForward (loc (C a)) = C (algebraMap ℂ LaurentCoefficients a)
      rw [relativeForward_loc, ambientToFree_constant] }

/--
@isnad1 id=relative.0h0v.s0.47ef47b9f0a8 from=translated src=- shape=45709ebd vocab=47ef47b9
-/
theorem relativeLocalizationContract_proved : RelativeLocalizationContract := by
  refine ⟨localizationRingEquiv, relativeForward_coefficient,
    relativeForward_shiftX, relativeForward_shiftY, relativeForward_T, ?_⟩
  rfl

end AbhyankarSathaye.CommutingDerivations

end

end OAI
