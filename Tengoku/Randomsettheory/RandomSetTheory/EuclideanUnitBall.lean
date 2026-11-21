/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Seed.Analysis.Normed.Group.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Euclidean unit ball as an index type

This small module provides the common index type used by the Euclidean
chaining constructions.  Keeping the definition below the individual
chaining modules prevents duplicate declarations and avoids making one
chaining argument depend on another merely to share its index type.
-/

noncomputable section

namespace RandomSetTheory

/-- The closed unit ball, used as the index type of Euclidean chaining.-/
abbrev EuclideanUnitBall (E : Type*) [NormedAddCommGroup E] :=
  {x : E // ‖x‖ ≤ 1}

instance {E : Type*} [NormedAddCommGroup E] :
    Nonempty (EuclideanUnitBall E) :=
  ⟨⟨0, by simp⟩⟩

@[simp] theorem euclideanUnitBall_dist_mk
    {E : Type*} [NormedAddCommGroup E]
    (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    dist (⟨x, hx⟩ : EuclideanUnitBall E) ⟨y, hy⟩ = dist x y := rfl

end RandomSetTheory
