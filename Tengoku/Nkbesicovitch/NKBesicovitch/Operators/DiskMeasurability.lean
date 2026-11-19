/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.DiskRotation
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.Semicontinuity
public import Tengoku.Nkbesicovitch.NKBesicovitch.Grassmannian.Topology
public import Tengoku.Seed.Topology.Maps.Proper.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurability of disk maxima

For lower semicontinuous inputs, Fatou applies after rotating each disk
back to a fixed intrinsic unit ball. Proper descent through the orbit
map proves joint lower semicontinuity for parameterized input families.
This covers both smooth inputs and indicators of open sets.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NKBesicovitch

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] {n k : ℕ}

end NKBesicovitch
