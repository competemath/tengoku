/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CutoffDerivatives
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CutoffMorrey
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMeasurability
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceComponents
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyData
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.LocalizedEquationGradientMeasurability
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.MorreyVecMem
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

/-!
# Source Morrey Gradient Package

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-!
# Gradient-slot localized source package

The local Morrey source bounds for the pressure-gradient heat representation.
-/

end CKN.Core.Step4
