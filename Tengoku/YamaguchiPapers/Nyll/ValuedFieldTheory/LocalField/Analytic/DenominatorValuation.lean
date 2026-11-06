/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Valuations of natural-number denominators

For a complete discrete valuation with value group `WithZero (Multiplicative ℤ)`
and finite residue field, this file constructs the ramification index
`e = v_K(p)` from the valuation itself.  In mixed characteristic it then proves
the natural-number valuation formula used in the logarithm and exponential theorems.
-/

noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

variable {K : Type u} [Field K]

/-- The full ordered group structure whose ordered-monoid parent is the
canonical one used by `Valuation` on `ℤᵐ⁰`.-/
@[reducible] def coherentWithZeroMultiplicativeIntGroup :
    LinearOrderedCommGroupWithZero
      (WithZero (Multiplicative ℤ)) where
  __ :=
    (inferInstance :
      LinearOrderedCommMonoidWithZero
        (WithZero (Multiplicative ℤ)))
  __ :=
    (inferInstance :
      CommGroupWithZero
        (WithZero (Multiplicative ℤ)))

/-- Package a standard `ℤᵐ⁰`-valued complete discrete valuation with finite
residue field as a local field.-/
def ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    LocalField.{u, 0} K where
  toCompleteDVF :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      instValueGroup := coherentWithZeroMultiplicativeIntGroup
      valuation := v
      instCompleteDiscrete := inferInstance }
  residueFinite := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance

/-- The ramification index `e = v_K(p)` of a standard mixed-characteristic
local field, obtained from the exponent of the value of its residue
characteristic `p`.-/
def ramificationIndexOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K] : ℕ :=
  Int.toNat
    (-WithZero.log
      (v ((ofWithZeroValuation v).residueCharacteristic : K)))

end LocalField
end LocalFieldTheory.DiscreteValuationField
