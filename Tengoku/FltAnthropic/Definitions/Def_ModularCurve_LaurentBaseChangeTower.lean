import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace ModularCurve

set_option synthInstance.maxHeartbeats 400000

variable (L : Type*) [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

section Tower

def baseChangeRingHom : F₀ →+* laurentBaseChange L F₀ where
  toFun y := ⟨coeffEmb L (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L y.2⟩
  map_one' := Subtype.ext (map_one (coeffEmb L))
  map_mul' _ _ := Subtype.ext (map_mul (coeffEmb L) _ _)
  map_zero' := Subtype.ext (map_zero (coeffEmb L))
  map_add' _ _ := Subtype.ext (map_add (coeffEmb L) _ _)

/--
@isnad1 id=eq.0h3v.s12.5fdd02c59bb1 from=translated src=- shape=c24e8f86 vocab=e1464770
-/
@[simp]
theorem coe_baseChangeRingHom (y : F₀) :
    (baseChangeRingHom L F₀ y : LaurentSeries L) = coeffEmb L (y : LaurentSeries ℚ) :=
  rfl

@[reducible] def baseChangeAlgebra : Algebra F₀ (laurentBaseChange L F₀) :=
  (baseChangeRingHom L F₀).toAlgebra

attribute [local instance] baseChangeAlgebra

/--
@isnad1 id=eq.0h2v.s11.d4c79dfc5d41 from=translated src=- shape=34356593 vocab=e9fad2f2
-/
theorem algebraMap_laurentBaseChange_eq :
    algebraMap F₀ (laurentBaseChange L F₀) = baseChangeRingHom L F₀ :=
  rfl

@[reducible] def baseChangeAlgebraRat : Algebra ℚ (laurentBaseChange L F₀) :=
  ((algebraMap L (laurentBaseChange L F₀)).comp (algebraMap ℚ L)).toAlgebra

attribute [local instance] baseChangeAlgebraRat

/--
@isnad1 id=isscalar.0h2v.s11.fafe5c6f0e57 from=translated src=- shape=aa632e04 vocab=8b12184d
-/
instance instTowerRatLBaseChange :
    @IsScalarTower ℚ L (laurentBaseChange L F₀)
      (Algebra.toSMul (R := ℚ) (A := L))
      (Algebra.toSMul (R := L) (A := laurentBaseChange L F₀))
      (Algebra.toSMul (R := ℚ) (A := laurentBaseChange L F₀)) :=
  IsScalarTower.of_algebraMap_eq' rfl

/--
@isnad1 id=isscalar.0h2v.s12.28eadea10559 from=translated src=- shape=d5e29854 vocab=2d1a2662
-/
instance instTowerRatF₀BaseChange :
    @IsScalarTower ℚ F₀ (laurentBaseChange L F₀)
      (Algebra.toSMul (R := ℚ) (A := F₀))
      (Algebra.toSMul (R := F₀) (A := laurentBaseChange L F₀))
      (Algebra.toSMul (R := ℚ) (A := laurentBaseChange L F₀)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

end Tower

end ModularCurve

end
