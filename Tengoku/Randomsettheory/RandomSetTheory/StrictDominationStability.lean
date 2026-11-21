/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Seed.MeasureTheory.Function.ConvergenceInMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stability of strict probabilistic domination

This file records a generic Slutsky-type bridge used by the applications.
Two oracle quantities converge in measure to strictly separated constants;
actual plug-in quantities are allowed deterministic one-sided uniform errors
which vanish.  The probability that the actual strict order fails then tends
to zero.

The assumptions contain neither the desired event nor its probability, so the
result can be safely used to separate an i.i.d. LLN from a later plug-in or
remainder estimate.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]
  {probabilityMeasure : Measure Omega}

/-- Strict domination survives deterministic uniform perturbations tending
to zero.
@isnad1 id=tendsto.7h10v.s8.36a84b32fd0a from=translated src=- shape=0d67a029 vocab=fd795296
-/
theorem tendsto_measure_failure_strictDomination_of_uniformApproximation
    {oracleCurvature oracleSignal actualCurvature actualSignal :
      Nat → Omega → Real}
    {curvatureError signalError : Nat → Real}
    {curvatureLimit signalLimit : Real}
    (hgap : curvatureLimit < signalLimit)
    (horacleCurvature : TendstoInMeasure probabilityMeasure oracleCurvature
      atTop (fun _ ↦ curvatureLimit))
    (horacleSignal : TendstoInMeasure probabilityMeasure oracleSignal
      atTop (fun _ ↦ signalLimit))
    (hcurvatureError : Tendsto curvatureError atTop (nhds 0))
    (hsignalError : Tendsto signalError atTop (nhds 0))
    (hactualCurvature : ∀ n omega,
      actualCurvature n omega ≤ oracleCurvature n omega + curvatureError n)
    (hactualSignal : ∀ n omega,
      oracleSignal n omega ≤ actualSignal n omega + signalError n) :
    Tendsto (fun n ↦ probabilityMeasure {omega |
      actualSignal n omega ≤ actualCurvature n omega})
      atTop (nhds 0) := by
  let delta : Real := (signalLimit - curvatureLimit) / 5
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hcurvatureBad : Tendsto (fun n ↦ probabilityMeasure {omega |
      delta ≤ dist (oracleCurvature n omega) curvatureLimit})
      atTop (nhds 0) := by
    simpa using
      (tendstoInMeasure_iff_dist.mp horacleCurvature delta hdelta)
  have hsignalBad : Tendsto (fun n ↦ probabilityMeasure {omega |
      delta ≤ dist (oracleSignal n omega) signalLimit})
      atTop (nhds 0) := by
    simpa using (tendstoInMeasure_iff_dist.mp horacleSignal delta hdelta)
  have hbad : Tendsto (fun n ↦
      probabilityMeasure {omega |
        delta ≤ dist (oracleCurvature n omega) curvatureLimit} +
      probabilityMeasure {omega |
        delta ≤ dist (oracleSignal n omega) signalLimit})
      atTop (nhds 0) := by
    simpa only [add_zero] using hcurvatureBad.add hsignalBad
  have herrors : ∀ᶠ n in atTop,
      curvatureError n < delta ∧ signalError n < delta := by
    filter_upwards [
      (tendsto_order.mp hcurvatureError).2 delta hdelta,
      (tendsto_order.mp hsignalError).2 delta hdelta] with n hnC hnS
    exact ⟨hnC, hnS⟩
  have hupper : ∀ᶠ n in atTop,
      probabilityMeasure {omega |
          actualSignal n omega ≤ actualCurvature n omega} ≤
        probabilityMeasure {omega |
          delta ≤ dist (oracleCurvature n omega) curvatureLimit} +
        probabilityMeasure {omega |
          delta ≤ dist (oracleSignal n omega) signalLimit} := by
    filter_upwards [herrors] with n hn
    rcases hn with ⟨hnC, hnS⟩
    have hsubset :
        {omega | actualSignal n omega ≤ actualCurvature n omega} ⊆
          {omega | delta ≤ dist (oracleCurvature n omega) curvatureLimit} ∪
          {omega | delta ≤ dist (oracleSignal n omega) signalLimit} := by
      intro omega hfailure
      change actualSignal n omega ≤ actualCurvature n omega at hfailure
      by_contra hnot
      simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hnot
      simp only [Real.dist_eq] at hnot
      obtain ⟨hcurvatureLower, hcurvatureUpper⟩ := abs_lt.mp hnot.1
      obtain ⟨hsignalLower, hsignalUpper⟩ := abs_lt.mp hnot.2
      have hactualCurvature' := hactualCurvature n omega
      have hactualSignal' := hactualSignal n omega
      dsimp [delta] at hcurvatureLower hcurvatureUpper hsignalLower hsignalUpper hnC hnS
      linarith
    exact (measure_mono hsubset).trans (measure_union_le _ _)
  rw [tendsto_order]
  constructor
  · intro lower hlower
    exact False.elim (not_lt_of_ge (bot_le : (0 : ENNReal) ≤ lower) hlower)
  · intro upper hupperPos
    have hbadUpper := (tendsto_order.mp hbad).2 upper hupperPos
    filter_upwards [hupper, hbadUpper] with n hn hnBad
    exact lt_of_le_of_lt hn hnBad

end ProbabilityTheory
