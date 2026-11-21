/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.PointwiseSupportProcessTightness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Existence of a continuous-process law from tightness and finite projections

Let `T` be a compact second-countable metric space.  A tight sequence of laws
on `C(T, ℝ)` whose finite evaluation projections converge to prescribed
scalar laws has a unique weak limit.  Every prescribed scalar law is the
corresponding projection of that limit.

The existence argument is Prokhorov's theorem followed by extraction of a
convergent subsequence.  Continuity of push-forward by a continuous linear
functional identifies the projections of the subsequential limit.  Finally,
`ProbabilityMeasure.tendsto_of_tight_of_finiteEvaluationProjections` upgrades
the subsequential convergence to convergence of the whole sequence.

The explicit topological assumptions are:

* `T` is metric, compact, and second-countable;
* `C(T, ℝ)` carries its Borel measurable space.

They imply that `C(T, ℝ)` is Polish and that its probability-measure space
is metrizable (hence first-countable), which is what permits sequential
extraction from the compact closure supplied by Prokhorov.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ProbabilityTheory

noncomputable section

namespace RandomSetTheory

variable (T : Type*) [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
variable [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]

end RandomSetTheory
