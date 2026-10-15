import Tengoku.NavierStokesEuler.Euler.CylinderSobolevOperators
import Tengoku

/-! A genuine bounded angular primitive on the full cylinder L² space. -/

noncomputable section

namespace EulerCylinderAnglePrimitive

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSpatialSobolevInverse EulerPressureSpatialRegularity EulerCylinderMollifier

variable (P : ℝ) [Fact (0 < P)]

def angleShift (s : ℝ) : LiftDomain P := (0,(s : AddCircle P))

omit [Fact (0 < P)] in
/--
@isnad1 id=continuo.0h1v.s6.8dba8faa7314 from=translated src=- shape=0fc427d2 vocab=3525529c
-/
theorem angleShift_continuous : Continuous (angleShift P) :=
  continuous_const.prodMk (AddCircle.continuous_mk' P)

def kernelCurve (u : LiftL2 P) (s : ℝ) : LiftL2 P :=
  s • translation P (angleShift P s) u

/--
@isnad1 id=continuo.0h2v.s13.e73447f4dfc1 from=translated src=- shape=6adfc97c vocab=6764d60a
-/
theorem kernelCurve_continuous (u : LiftL2 P) : Continuous (kernelCurve P u) :=
  continuous_id.smul ((translation_continuous P u).comp (angleShift_continuous P))

def kernelIntegral (u : LiftL2 P) : LiftL2 P := P⁻¹ • (∫ s in (0 : ℝ)..P, kernelCurve P u s)

/--
@isnad1 id=eq.0h3v.s14.43e9525a5ea2 from=translated src=- shape=79b085e1 vocab=da3514f2
-/
theorem kernelIntegral_add (u v : LiftL2 P) :
    kernelIntegral P (u+v) = kernelIntegral P u+kernelIntegral P v := by
  have he : kernelCurve P (u+v) = kernelCurve P u+kernelCurve P v := by
    funext s
    simp only [kernelCurve, map_add, smul_add, Pi.add_apply]
  rw [kernelIntegral, he]
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_add
    ((kernelCurve_continuous P u).intervalIntegrable 0 P)
    ((kernelCurve_continuous P v).intervalIntegrable 0 P), smul_add]
  rfl

/--
@isnad1 id=eq.0h3v.s15.55792d58e453 from=translated src=- shape=237a7239 vocab=8d4a6339
-/
theorem kernelIntegral_smul (r : ℝ) (u : LiftL2 P) :
    kernelIntegral P (r • u) = r • kernelIntegral P u := by
  have he : kernelCurve P (r • u) = r • kernelCurve P u := by
    funext s
    change s • translation P (angleShift P s) (r • u) = r • (s • translation P (angleShift P s) u)
    rw [map_smul, smul_comm s r]
  rw [kernelIntegral, he]
  simp only [Pi.smul_apply]
  rw [intervalIntegral.integral_smul, smul_comm P⁻¹ r]
  rfl

/--
@isnad1 id=le.0h2v.s12.b41e77293043 from=translated src=- shape=7218c08d vocab=62d77cdb
-/
theorem kernelIntegral_norm (u : LiftL2 P) : ‖kernelIntegral P u‖ ≤ P*‖u‖ := by
  have hP : 0 < P := Fact.out
  have hb : ‖∫ s in (0 : ℝ)..P, kernelCurve P u s‖ ≤ (P*‖u‖)*P := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := P) (f := kernelCurve P u) (C := P*‖u‖) (fun s hs => by
        rw [uIoc_of_le hP.le] at hs
        simp only [kernelCurve, norm_smul, Real.norm_eq_abs, abs_of_pos hs.1,
          (translation P (angleShift P s)).norm_map]
        exact mul_le_mul_of_nonneg_right hs.2 (norm_nonneg u))
    simpa only [sub_zero, abs_of_pos hP] using h
  change ‖P⁻¹ • (∫ s in (0 : ℝ)..P, kernelCurve P u s)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hP)]
  calc
    _ ≤ P⁻¹*((P*‖u‖)*P) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hP.le)
    _ = P*‖u‖ := by field_simp

def primitiveLinear : LiftL2 P →ₗ[ℝ] LiftL2 P where
  toFun := kernelIntegral P
  map_add' := kernelIntegral_add P
  map_smul' := kernelIntegral_smul P

def primitive : LiftL2 P →L[ℝ] LiftL2 P :=
  (primitiveLinear P).mkContinuous P (kernelIntegral_norm P)

/--
@isnad1 id=eq.0h2v.s15.1036373c6750 from=translated src=- shape=0883c98d vocab=d7e63b5d
-/
@[simp] theorem primitive_apply (u : LiftL2 P) : primitive P u = kernelIntegral P u := rfl

/--
@isnad1 id=le.0h1v.s14.6270a3131ef4 from=translated src=- shape=8382239e vocab=37d807c6
-/
theorem primitive_norm : ‖primitive P‖ ≤ P :=
  ContinuousLinearMap.opNorm_le_bound _ (le_of_lt (Fact.out : 0 < P)) (kernelIntegral_norm P)

/-- The actual angular operator commutes with all spatial and angular translations.
@isnad1 id=eq.0h3v.s16.0504b03db1ae from=translated src=- shape=95fce484 vocab=f4129d01
-/
theorem primitive_translation (a : LiftDomain P) (u : LiftL2 P) :
    primitive P (translation P a u) = translation P a (primitive P u) := by
  change P⁻¹ • (∫ s in (0 : ℝ)..P, kernelCurve P (translation P a u) s) =
    translation P a (P⁻¹ • (∫ s in (0 : ℝ)..P, kernelCurve P u s))
  rw [map_smul]
  change P⁻¹ • _ = P⁻¹ • (translation P a).toContinuousLinearMap _
  rw [← (translation P a).toContinuousLinearMap.intervalIntegral_comp_comm
    ((kernelCurve_continuous P u).intervalIntegrable 0 P)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  change s • translation P (angleShift P s) (translation P a u) =
    translation P a (s • translation P (angleShift P s) u)
  rw [map_smul, translations_commute P (angleShift P s) a u]

/-- This same operator acts on every genuine Sobolev derivative coordinate. -/
def sobolevPrimitive (q : ℕ) : SobolevSpace P q →L[ℝ] SobolevSpace P q :=
  liftOperator P q (primitive P) (primitive_translation P)

/--
@isnad1 id=le.0h2v.s19.de6c6b2a7189 from=translated src=- shape=6d5af165 vocab=211c4921
-/
theorem sobolevPrimitive_norm (q : ℕ) : ‖sobolevPrimitive P q‖ ≤ P :=
  (norm_liftOperator_le P q (primitive P) (primitive_translation P)).trans (primitive_norm P)

end EulerCylinderAnglePrimitive
