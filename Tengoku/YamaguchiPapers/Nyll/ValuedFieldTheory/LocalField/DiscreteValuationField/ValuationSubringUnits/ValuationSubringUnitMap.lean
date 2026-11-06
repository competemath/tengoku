/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Valuation-subring units inside field units

This file defines the canonical homomorphism from units of a complete-DVF
valuation ring to units of its fraction field.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The inclusion `O_K^* -> K^*` for the chosen valuation ring of a complete
DVF.-/
noncomputable def valuationSubringUnitsToFieldUnits
    (F : CompleteDVF.{u, v} K) : F.valuationSubringˣ →* Kˣ :=
  F.valuation.valuationSubring.unitGroup.subtype.comp
    F.valuation.valuationSubring.unitGroupMulEquiv.symm.toMonoidHom

/--
The defining evaluation formula for `coe_valuationSubringUnitsToFieldUnits` is
`(((CompleteDVF.valuationSubringUnitsToFieldUnits F) a : Kˣ) : K) = (a : F.valuationSubring)`.
@isnad1 id=eq.0h3v.s9.b05a913aaa20 from=translated src=- shape=2c13689f vocab=43e449e4
-/
@[simp] theorem coe_valuationSubringUnitsToFieldUnits_apply
    (F : CompleteDVF.{u, v} K) (a : F.valuationSubringˣ) :
    (((LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits F)
      a : Kˣ) : K) =
      (a : F.valuationSubring) := by
  change
    ((F.valuation.valuationSubring.unitGroupMulEquiv.symm a : Kˣ) : K) =
      (a : K)
  exact _root_.ValuationSubring.coe_unitGroupMulEquiv_symm_apply
    (A := F.valuation.valuationSubring) (K := K) a

end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
