/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ChoicePositions
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.PowerSeriesComposition
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ProductArgument
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.BasicFactors
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ChoiceCountSystem
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ExplicitChoiceCounts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Choice-count combinatorics for the formal logarithm product

This module completes the formal logarithm core by identifying the basic-factor
choices with pairs of finite position sets and evaluating their cardinality.
The formal-series identities and the underlying position calculus live in
`FormalCoreBase`.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- Defines `formalLogOnePlusProductArgumentMixedLeftChoices`.-/
noncomputable def formalLogOnePlusProductArgumentMixedLeftChoices
    (q a b : ℕ) : Finset (Σ _ : Finset ℕ, Finset ℕ) :=
  ((Finset.range q).powersetCard (a + b - q)).sigma fun M =>
    ((Finset.range q \ M).powersetCard (q - b))

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
