/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceComponents
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalEquationRepresentation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalSources
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalLinearSources
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalForceSource
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMeasurability

/-! # Quantitative bounds for the actual gradient-slot source

The five terms of the localized equation are estimated from the improved
velocity norm, the initial gradient norm, the supplied pressure-gradient
norm, and the original force smallness. The formula includes the pressure
gradient in the order-two slot. No potential or Hölder estimate is assumed.
-/

@[expose] public section

section

/-! # The past-time convective heat source

The improved velocity exponent and initial gradient exponent give the
convective source estimate by scalar Morrey Hölder and the finite-sum
triangle inequality. Only the cutoff's nonpositive-time values are used.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3

noncomputable section
namespace CKN.Core.Endgame

end CKN.Core.Endgame
end

end

open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Core.Step3

noncomputable section
namespace CKN.Core.Endgame

/-- The numerical bound for a component of the final order-two source. -/
def causalGradientMorreyBound (q ε₀ C : ℝ) (KU KD KP : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal C * (volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KU) +
    ENNReal.ofReal C * (volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KU) +
    3 * KU * KD + forceSourceMorreyBound q ε₀ + KP

/-- Finite input bounds give a finite numerical source bound. -/
theorem causalGradientMorreyBound_lt_top
    (q ε₀ C : ℝ) {KU KD KP : ℝ≥0∞} (hq : 5 / 2 < q)
    (hKU : KU < ⊤) (hKD : KD < ⊤) (hKP : KP < ⊤) :
    causalGradientMorreyBound q ε₀ C KU KD KP < ⊤ := by
  have hvol : volume (parabolicCylinder (0 : Vec3) 0 1) ^ (5 / 6 - 1 / 3 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      Integration.volume_parabolicCylinder_lt_top.ne
  have hforce := forceSourceMorreyBound_lt_top q ε₀ hq
  unfold causalGradientMorreyBound
  finiteness

private theorem norm_neg {P τ : ℝ} (f : ParabolicPoint → ℝ) :
    morreyNorm P τ (fun z => -f z) = morreyNorm P τ f := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg]

private theorem norm_sub_le {P τ : ℝ} (hP : 1 ≤ P)
    {f g : ParabolicPoint → ℝ} (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) :
    morreyNorm P τ (fun z => f z - g z) ≤ morreyNorm P τ f + morreyNorm P τ g := by
  have h := morrey_norm_add_le (τ := τ) hP hf hg.neg
  change morreyNorm P τ (fun z => f z + -g z) ≤
    morreyNorm P τ f + morreyNorm P τ (fun z => -g z) at h
  rw [norm_neg] at h
  simpa only [sub_eq_add_neg] using h

end CKN.Core.Endgame
