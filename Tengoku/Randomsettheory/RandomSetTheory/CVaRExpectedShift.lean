/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.CVaRDenseSupremum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From centered CVaR to a tail above an expectation bound

Empirical-process inequalities naturally control `S - E S`, while final
applications usually have only a deterministic upper bound `E0` on `E S`.
This file packages the elementary shift needed to pass from one form to the
other on an atomless probability space.
-/

open MeasureTheory Set
open scoped ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- A centered CVaR bound and a deterministic upper bound on the mean imply
the corresponding upper-tail bound for the uncentered statistic.
@isnad1 id=le.7h6v.s7.cad587eae3f0 from=translated src=- shape=7bfc9ff7 vocab=cda40b10
-/
theorem measureReal_add_lt_le_of_mean_le_of_centered_cvar
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    (hmu : RandomSetTheory.IsAtomlessMeasure mu)
    (S : Omega -> Real) (hSmeas : Measurable S) (hS : Integrable S mu)
    {E C alpha : Real}
    (hmean : (∫ omega, S omega ∂mu) <= E)
    (halpha0 : 0 < alpha) (halpha1 : alpha <= 1)
    (hcvar : conditionalValueAtRisk alpha
      (fun omega => S omega - ∫ z, S z ∂mu) mu <= C) :
    mu.real {omega | E + C < S omega} <= alpha := by
  have hcenteredMeas : Measurable
      (fun omega => S omega - ∫ z, S z ∂mu) :=
    hSmeas.sub measurable_const
  have hcenteredInt : Integrable
      (fun omega => S omega - ∫ z, S z ∂mu) mu :=
    hS.sub (integrable_const _)
  have htail := measureReal_lt_le_of_conditionalValueAtRisk_le_of_atomless
    hmu hcenteredMeas hcenteredInt halpha0 halpha1 hcvar
  apply (measureReal_mono ?_).trans htail
  intro omega homega
  change E + C < S omega at homega
  change C < S omega - ∫ z, S z ∂mu
  linarith

end ProbabilityTheory
