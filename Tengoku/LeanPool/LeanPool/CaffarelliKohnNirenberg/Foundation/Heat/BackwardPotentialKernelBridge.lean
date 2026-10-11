/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.BackwardPotentialIdentity
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Integrability
public import Tengoku

/-!
# Backward Potential Kernel Bridge

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology Convolution

open MeasureTheory MeasureTheory.Measure Set Filter

noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

end CKN.Foundation.Heat
