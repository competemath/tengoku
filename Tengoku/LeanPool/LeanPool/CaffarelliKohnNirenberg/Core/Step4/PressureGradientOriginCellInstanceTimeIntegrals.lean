/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsBridge
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Indicator
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedOriginTransfer
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsShellTime

/-!
# Time integrals on clipped origin cells

The time integrals in `prop:bootstrap` use the spatial intersection of a cell
with the origin carrier and the corresponding intersection of backward time
windows. Tonelli identifies these integrals with the carrier-restricted
space-time mass without extending any data outside the carrier.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

end CKN.Core.Step4
