/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNormBase
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Valuation-subring units in complete-DVF extensions

This file proves compatibility of valuation-ring units with scalar extension
and relates the value of an embedded base uniformizer to the ramification
index.
-/

noncomputable section

universe u v x

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace ValuedExtension

open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type u} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{u, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- Compatibility between the valuation-ring unit map and the field-unit map.
@isnad1 id=eq.0h5v.s11.ef12651f0040 from=translated src=- shape=01af806a vocab=166738c8
-/
theorem baseUnitsMap_valuationSubringUnitsToFieldUnits
    (a : base.valuationSubringˣ) :
    baseUnitsMap (K := K) (L := L)
        ((CompleteDVF.valuationSubringUnitsToFieldUnits base) a) =
      (CompleteDVF.valuationSubringUnitsToFieldUnits target)
        (Units.map (integerMap base.toDVF target.toDVF).toMonoidHom a) := by
  ext
  simp [CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply,
    integerMap_apply base.toDVF target.toDVF]

/-- The ramification-ideal unit-multiple source gives the value of the embedded
base uniformizer.

This is the source-producing bridge from
`exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image` to the
`hϖmap` input used by `ValuationScaling.lean`.
@isnad1 id=eq.4h7v.s10.e2982691da76 from=translated src=- shape=d5ee0fb5 vocab=a14a1872
-/
theorem base_uniformizer_image_val_eq_ramificationIndex
    (vL : MultiplicativeIntegerValuation Lˣ)
    (hunit :
      ∀ u : target.valuationSubringˣ,
        (CompleteDVF.valuationSubringUnitsToFieldUnits target) u ∈ vL.zeroSubgroup)
    {ϖ : base.valuationSubring} {π : target.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K))
    (hπ : target.valuation.IsUniformizer (π : L))
    (hπval : vL.val (Units.mk0 (π : L) hπ.ne_zero) = 1) :
    vL.val
        (baseUnitsMap (K := K) (L := L)
          (Units.mk0 (ϖ : K) hϖ.ne_zero)) =
      (ramificationIndex base.toDVF target.toDVF : ℤ) := by
  rcases
      (exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image
        base target hϖ hπ) with
    ⟨u, hu⟩
  let ϖK : Kˣ := Units.mk0 (ϖ : K) hϖ.ne_zero
  let πL : Lˣ := Units.mk0 (π : L) hπ.ne_zero
  have hfield :
      algebraMap K L (ϖ : K) =
        ((u : target.valuationSubring) : L) *
          (π : L) ^ ramificationIndex base.toDVF target.toDVF := by
    calc
      algebraMap K L (ϖ : K) =
          ((integerMap base.toDVF target.toDVF ϖ :
              target.valuationSubring) : L) :=
        (integerMap_apply base.toDVF target.toDVF ϖ).symm
      _ = (((u : target.valuationSubring) *
            π ^ ramificationIndex base.toDVF target.toDVF :
            target.valuationSubring) : L) := by
        rw [hu]
      _ = ((u : target.valuationSubring) : L) *
          (π : L) ^ ramificationIndex base.toDVF target.toDVF := by
        exact (map_mul target.valuation.valuationSubring.subtype
          (u : target.valuationSubring) (π ^ ramificationIndex base.toDVF target.toDVF)).trans
            (congrArg (fun z : L => ((u : target.valuationSubring) : L) * z)
              (map_pow target.valuation.valuationSubring.subtype π _))
  have hbase :
      baseUnitsMap (K := K) (L := L) ϖK =
        (CompleteDVF.valuationSubringUnitsToFieldUnits target) u *
          πL ^ ramificationIndex base.toDVF target.toDVF := by
    ext
    simpa [ϖK, πL,
      CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply] using hfield
  have hπLval : vL.val πL = 1 := by
    simpa [πL] using hπval
  change
    vL.val (baseUnitsMap (K := K) (L := L) ϖK) =
      (ramificationIndex base.toDVF target.toDVF : ℤ)
  rw [hbase, vL.val_mul,
    (vL.mem_zeroSubgroup_iff _).1 (hunit u), vL.val_pow, hπLval]
  ring

end ValuedExtension

end LocalFieldTheory.DiscreteValuationField

end
