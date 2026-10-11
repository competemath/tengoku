/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.BootstrapBounds
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Causality
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradient

/-! # Quantitative bootstrap from past-time sources

The global bootstrap is applied to the truncated potential itself. Its
agreement with velocity is needed only on the target cylinder. Consequently
no bound or representation for the truncated velocity at future times is used.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

noncomputable section
namespace CKN.Core.Endgame

/-- A global literal representation of the localized velocity supplies
the restricted representation required by the causal bootstrap. -/
theorem localizedVelocity_heat_representation_on_plateau
    {φ : ParabolicPoint → ℝ} {u F : ParabolicPoint → Vec3}
    {H : Fin 3 → ParabolicPoint → Vec3} {S : Set ParabolicPoint}
    (hS : MeasurableSet S) (hφ : ∀ z ∈ S, φ z = 1)
    (hrep : localizedVelocity φ u =ᵐ[volume] vectorHeatPotential F H) :
    u =ᵐ[volume.restrict S] vectorHeatPotential F H := by
  filter_upwards [hrep.filter_mono (ae_mono Measure.restrict_le_self), ae_restrict_mem hS]
    with z hz hzS
  simpa only [localizedVelocity, hφ z hzS, one_smul] using hz

end CKN.Core.Endgame
