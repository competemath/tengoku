/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.PlateMeasurability
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.PlateRotation
public import Tengoku.Nkbesicovitch.NKBesicovitch.Geometry.Plates
public import Tengoku.Seed.Topology.Maps.Proper.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Plate maxima of continuous families

Pulling a rotated plate back to a fixed plate gives lower semicontinuity
jointly in the input parameter and the rotation. The proper orbit map
then descends this property to the Grassmannian. Taking the supremum
over centers preserves lower semicontinuity.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] {n k : ℕ}

end NKBesicovitch
