/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
module

public import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Definitions
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.ExactModulusRecovery
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.FiniteBaseAnnulusEstimate
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.TrueLevelBasis
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.ProductAnnulusLocalization
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.TensorBasis
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Basic
import Tengoku.Seed.Combinatorics.Matroid.Init
import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.LpNorm
import Tengoku.Seed.Tactic.NormNum.Parity
import Tengoku.Seed.Topology.MetricSpace.Sequences

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # CoefficientLimitRigidity -/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace DimdPolyLEAN

/-!
# CoefficientLimitRigidity

Compactness bridge scaffold whose only public downstream output is a finite
coefficient-threshold theorem.
-/

private def coefficientControlSet_wip
    {d : Nat} {kappa : MultiIndex d} (E : Finset (Idx d)) (F : Pkappa d kappa) :
    Finset (Idx d) :=
  E ∪ F.support

private def orthogonalToSkappa_wip
    {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa) (U : Skappa d kappa) : Prop :=
  Finset.sum F.support
    (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha)) = 0

private def skappaOfCoeffBound_wip
    {d : Nat} (kappa : MultiIndex d) (u : Idx d -> ℂ)
    (hpartial :
      ∀ E : Finset (Idx d), Finset.sum E (fun alpha => ‖u alpha‖ ^ 2) <= 1) :
    Skappa d kappa :=
  { coeff := u
    summable_norm_sq := by exact summable_of_sum_le (fun alpha => sq_nonneg (‖u alpha‖)) hpartial }

private def defectFunctionPkappa_coeff_wip
    {d : Nat} (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    Cd d -> ℝ :=
  fun z => |‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖|

private def skappaAffinePkappa_wip
    {d : Nat} (kappa : MultiIndex d)
    (F : Pkappa d kappa) (U : Skappa d kappa) (a b : ℂ) :
    Skappa d kappa where
  coeff := fun alpha => a * coeffPkappa F alpha + b * coeffSkappa U alpha
  summable_norm_sq := by
    classical
    let f : Idx d -> ℝ := fun alpha => ‖a * coeffPkappa F alpha‖ ^ 2
    let g : Idx d -> ℝ := fun alpha => ‖b * coeffSkappa U alpha‖ ^ 2
    have hf : Summable f := by
      dsimp [f, coeffPkappa]
      refine summable_of_hasFiniteSupport ?_
      refine Set.Finite.subset F.support.finite_toSet ?_
      intro alpha hnonzero
      simp_all
    have hg : Summable g := by
      have hg_eq :
          g = fun alpha => (‖b‖ ^ 2) * (‖coeffSkappa U alpha‖ ^ 2) := by
        funext alpha
        dsimp [g]
        rw [norm_mul, mul_pow]
      rw [hg_eq]
      exact U.summable_norm_sq.mul_left (‖b‖ ^ 2)
    have hsum : Summable (fun alpha => 2 * f alpha + 2 * g alpha) :=
      (hf.mul_left 2).add (hg.mul_left 2)
    refine hsum.of_nonneg_of_le (fun alpha => sq_nonneg _) ?_
    intro alpha
    dsimp [f, g]
    let x : ℂ := a * coeffPkappa F alpha
    let y : ℂ := b * coeffSkappa U alpha
    have hnorm : ‖x + y‖ <= ‖x‖ + ‖y‖ := norm_add_le x y
    have hsq :
        ‖x + y‖ ^ 2 <= (‖x‖ + ‖y‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
    have hquad : (‖x‖ + ‖y‖) ^ 2 <= 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
    have hfinal := le_trans hsq hquad
    simpa [x, y] using hfinal

end DimdPolyLEAN
