/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.BasicFactors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinate equations for basic-factor choices

This module derives the three coordinate and total-count equations satisfied by
a choice of the basic factors in `X + Y + XY`.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- Basic-factor sequences with the three label counts forced by `q` and the
target exponent vector `e`.-/
noncomputable def formalLogOnePlusProductArgumentBasicFactorLabelCountChoices
    (q : ℕ) (e : Fin 2 →₀ ℕ) :
    Finset (ℕ →₀ (Fin 2 →₀ ℕ)) :=
  (formalLogOnePlusProductArgumentBasicFactorProductChoices q).filter
    (fun l =>
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 =
          q - e (1 : Fin 2) ∧
        formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 =
          q - e (0 : Fin 2) ∧
          formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 =
            e (0 : Fin 2) + e (1 : Fin 2) - q)

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
