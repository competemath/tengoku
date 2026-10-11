/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.BootstrapPotential
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.PotentialMeasurability
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.AdamsAEMeasurable
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientMorrey

/-! # Morrey improvement from actual localized sources

The potential comparison uses almost-everywhere finiteness. Measurability
of the potential and finiteness of the explicit Adams constants are derived,
rather than supplied as extra inputs.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4

noncomputable section

namespace CKN.Core.Endgame

end CKN.Core.Endgame
