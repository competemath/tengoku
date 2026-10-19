/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
module

public import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.TensorBasis
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.CoefficientLimitRigidity
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.OrthogonalCoercivity
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.OrthogonalReduction.OrthogonalReduction
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Combinatorics.Matroid.Init
import Tengoku.Seed.Data.Nat.Factorial.DoubleFactorial
import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.LpNorm
import Tengoku.Seed.Tactic.NormNum.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # PhaseStability -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace DimdPolyLEAN

/-!
# Phase-stable polynomial recovery

This file adds the phase-optimized layer on top of the existing orthogonal
coercivity theorem.  The proof works inside the concrete polynomial subspace
of `L²(gammaD d)`, so the public statement remains about finite coefficient
arrays.
-/

/-- The Gaussian `L²` modulus defect between two finite Hermite-Fock polynomials. -/
def modulusDefect {d : Nat} (kappa : MultiIndex d)
    (F Q : Pkappa d kappa) : ℝ :=
  Real.sqrt <| ∫ z, (‖evalPkappa kappa Q z‖ - ‖evalPkappa kappa F z‖) ^ 2 ∂ gammaD d

/-- The coefficient distance after applying a chosen global phase to `Q`. -/
def phasedCoeffDistance {d : Nat} {kappa : MultiIndex d} (F Q : Pkappa d kappa)
    (phase : ℂ) : ℝ :=
  ‖phase • Q - F‖

theorem pkappaInner_smul_left
    {d : Nat} {kappa : MultiIndex d} (c : ℂ)
    (Q F : Pkappa d kappa) :
    pkappaInner (c • Q) F = c * pkappaInner Q F := by
  by_cases hc : c = 0
  · subst c
    simp [pkappaInner]
  · unfold pkappaInner
    rw [Finsupp.sum, Finsupp.sum, Finsupp.support_smul_eq hc, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    simp [Finsupp.smul_apply, mul_assoc]

theorem exists_phase_positivePhaseGauge
    {d : Nat} {kappa : MultiIndex d} (F Q : Pkappa d kappa) :
    ∃ phase : ℂ, ‖phase‖ = 1 ∧ positivePhaseGauge F (phase • Q) := by
  let β : ℂ := pkappaInner Q F
  rcases Complex.exists_norm_eq_mul_self β with ⟨phase, hphase, hphaseβ⟩
  refine ⟨phase, hphase, ?_⟩
  have hinner : pkappaInner (phase • Q) F = ((‖β‖ : ℝ) : ℂ) := by
    rw [pkappaInner_smul_left, hphaseβ]
  constructor
  · rw [hinner]
    simp
  · rw [hinner]
    simp

private theorem defect_phase_sub_eq_modulusDefect
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F Q : Pkappa d kappa) {phase : ℂ} (hphase : ‖phase‖ = 1) :
    defect F (phase • Q - F) = modulusDefect kappa F Q := by
  unfold defect modulusDefect
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  have heval : evalPkappa kappa (F + (phase • Q - F)) z = phase * evalPkappa kappa Q z := by
    have h1 := congrFun (evalPkappa_smul hd kappa phase Q) z
    simp_all
  rw [heval, norm_mul, hphase, one_mul]

/-- Rewriting the perturbation defect as the two-signal modulus defect. -/
theorem defect_sub_eq_modulusDefect
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F Q : Pkappa d kappa) :
    defect F (Q - F) = modulusDefect kappa F Q := by
  have h :=
    defect_phase_sub_eq_modulusDefect (d := d) hd kappa F Q (phase := 1) (by simp)
  simpa using h

theorem modulusDefect_phase_smul
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F Q : Pkappa d kappa) {phase : ℂ} (hphase : ‖phase‖ = 1) :
    modulusDefect kappa F (phase • Q) = modulusDefect kappa F Q := by
  rw [← defect_sub_eq_modulusDefect hd kappa F (phase • Q),
    defect_phase_sub_eq_modulusDefect hd kappa F Q hphase]

end DimdPolyLEAN
