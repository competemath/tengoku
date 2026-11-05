/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Correspondence.FiniteCover
import Tengoku.Seed.RingTheory.Artinian.Module
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Tensor components of selected correspondence chains

Finite branch fields over the common middle function field select a
minimal-prime tensor component. Its quotient is the actual chain field,
even when the middle function field is not algebraically closed.
-/

namespace AclGeom

open IntermediateField
open scoped TensorProduct

end AclGeom
