/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Tengoku.LeanPool.LeanPool.PLAcceleratedNesterovLean.Core.NesterovSeqGen
import Tengoku.LeanPool.LeanPool.PLAcceleratedNesterovLean.Convergence.CurvAbsorb.Algebraic
import Tengoku.LeanPool.LeanPool.PLAcceleratedNesterovLean.Convergence.StateContraction.AuxVarRecursion

/-!
# Curvature Absorption Assembly

Standalone proof that the curvature + projector-freezing perturbation is absorbable.
Extracted from the main theorem to keep its proof term small (avoids kernel slowdown).

The key idea: Dπ is continuous at m⋆, so for small enough R,
all perturbation terms are O(ε₁ · Ln) with ε₁ = sup ‖Dπ-P‖ → 0.
-/

@[expose] public section

open scoped NNReal
noncomputable section

namespace PLAcceleratedNesterovLean

variable {d : ℕ}
-- Notation for ℝ^d
local notation "E" => EuclideanSpace ℝ (Fin d)

end PLAcceleratedNesterovLean
