/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.SubordinatedAssembly

/-!
# Subordinated End

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Core.HeatPotential
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

/-!
# Explicit subordinated heat potentials

The paper writes the pressure part as a degree-one multiplier applied to the
forward heat kernel.  The explicit dictionary used here is

* `∂ₖ W₊` is `heatPotentialSpatialKernel k`;
* `σ(D) W₊` is represented by
  `subordinatedHeatPotentialKernel j l m`, whose value is
  `-∫ s in Ioi t, ∂ₘ∂ⱼ∂ₗ W(x,s)`.

Thus the coordinate branch is the kernel already used by `heatPotential`,
while the pressure branch is a finite collection of the explicit kernels
`K^m_jl`.  The multiplier symbol itself is not used as an additional
assumption.
-/

end CKN.Core.HeatPotential
