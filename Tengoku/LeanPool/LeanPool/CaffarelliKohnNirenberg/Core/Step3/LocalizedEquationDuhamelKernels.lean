/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step3.DuhamelAdjoint
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Localized Equation Duhamel Kernels

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section

namespace CKN.Core.Step3

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential

end CKN.Core.Step3
