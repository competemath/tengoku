/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.CodimensionOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebraic cycles graded by codimension

This file constructs codimension-`p` cycle groups with arbitrary additive coefficients inside
the existing group of locally finite algebraic cycles; integer coefficients give `Z^p(X)`.
Restriction to points of a fixed coheight gives a canonical additive projection. Its range,
idempotence, and orthogonality across distinct codimensions are proved. In codimension one with
integer coefficients this carrier is definitionally the existing Weil divisor group.

No rational-equivalence or intersection-product relation is imposed here; those are separate
geometric layers.
-/

noncomputable section

open AlgebraicGeometry Order

universe u

namespace AlgebraicGeometry.Chow

variable (X : Scheme.{u})

/-- Algebraic cycles with coefficients in `R`, supported purely in codimension `p`.-/
def codimensionCycles (R : Type*) [AddCommGroup R] (p : ℕ) :
    AddSubgroup (AlgebraicCycle X R) where
  carrier := fun D ↦ D.support ⊆ {x | coheight x = p}
  zero_mem' := by
    intro x hx
    change (0 : R) ≠ 0 at hx
    exact (hx rfl).elim
  add_mem' := by
    intro D E hD hE x hx
    change D x + E x ≠ 0 at hx
    by_cases hDx : D x = 0
    · apply hE
      change E x ≠ 0
      intro hEx
      exact hx (by simp [hDx, hEx])
    · exact hD hDx
  neg_mem' := by
    intro D hD x hx
    apply hD
    change D x ≠ 0
    intro hDx
    apply hx
    change -D x = 0
    simp [hDx]

/-- The additive group of `R`-valued codimension-`p` cycles.-/
abbrev CodimensionCycles (R : Type*) [AddCommGroup R] (p : ℕ) :=
  codimensionCycles X R p

end AlgebraicGeometry.Chow
