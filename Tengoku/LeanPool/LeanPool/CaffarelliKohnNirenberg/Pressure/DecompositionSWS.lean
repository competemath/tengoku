/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SupportRestrict
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionIdentity
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionSWSBasic

/-!
# Decomposition SWS

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

end CKN
