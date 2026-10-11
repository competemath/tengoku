/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.PotentialMeasurability
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski

/-! # Adams estimates for almost-everywhere measurable sources

A measurable representative preserves the source Morrey norm and the Riesz
potential at every evaluation point. Thus the scalar Adams estimate does not
require pointwise measurability of the original source.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Endgame

end CKN.Core.Endgame
