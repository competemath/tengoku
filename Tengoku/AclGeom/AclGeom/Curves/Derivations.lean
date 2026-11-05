/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Curves.GlobalResidue
import Tengoku.Seed.RingTheory.Derivation.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Regular derivations of one-variable function fields

Everywhere-regular derivations are the function-field incarnation of
global vector fields on the nonsingular projective curve.  Residue
differentials and their greatest levels bound such derivations locally;
the negative degree of the tangent divisor then forces rigidity in
genus at least two, and after one prescribed zero in genus one.

This module is part of the formalization of the
Evans–Hrushovski–Gismatullin reconstruction theorem; the source of truth
is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P6).
-/

namespace AclGeom

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- The local `k`-subspace of elements whose order at `P` is at least
`r`, together with zero.-/
noncomputable def Place.orderSubmodule (P : Place k F) (r : ℤ) :
    Submodule k F where
  carrier := {x | x = 0 ∨ r ≤ P.ord x}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro x y hx hy
    rcases eq_or_ne x 0 with rfl | hx0
    · simpa using hy
    rcases eq_or_ne y 0 with rfl | hy0
    · simpa using hx
    rcases eq_or_ne (x + y) 0 with hxy | hxy
    · exact Or.inl hxy
    refine Or.inr ?_
    have hmin := P.min_ord_le_ord_add hx0 hy0 hxy
    have hx' := hx.resolve_left hx0
    have hy' := hy.resolve_left hy0
    omega
  smul_mem' := by
    intro c x hx
    rcases eq_or_ne c 0 with rfl | hc0
    · exact Or.inl (zero_smul k x)
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Or.inl (smul_zero c)
    refine Or.inr ?_
    rw [Algebra.smul_def,
      P.ord_mul ((map_ne_zero (algebraMap k F)).2 hc0) hx0,
      P.ord_algebraMap hc0, zero_add]
    exact hx.resolve_left hx0

/-- A derivation is regular at `P` when it preserves the valuation
ring.-/
def DerivationIsRegularAt (D : Derivation k F F)
    (P : Place k F) : Prop :=
  ∀ x ∈ P.toSubmodule, D x ∈ P.toSubmodule

/-- A derivation is regular everywhere when it preserves every
valuation ring.-/
def DerivationIsRegular (D : Derivation k F F) : Prop :=
  ∀ P : Place k F, DerivationIsRegularAt D P

/-- A regular vector field vanishes at `P` when the image of its
valuation ring lies in the maximal ideal (order at least one).-/
def DerivationVanishesAt (D : Derivation k F F)
    (P : Place k F) : Prop :=
  ∀ x ∈ P.toSubmodule, D x ∈ P.orderSubmodule 1

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The derivative of a scalar multiple of a power, with the natural
coefficient expressed in the base field.
@isnad1 id=eq.0h6v.s8.801eea4e1e02 from=translated src=- shape=164060f9 vocab=2609d8ef
-/
theorem derivation_smul_pow (D : Derivation k F F) (c : k) (x : F)
    (n : ℕ) :
    D (c • x ^ n) = ((n : k) * c) • (x ^ (n - 1) * D x) := by
  rw [Derivation.map_smul, Derivation.leibniz_pow]
  simp only [Algebra.smul_def]
  change algebraMap k F c * ((n : F) * (x ^ (n - 1) * D x)) =
    algebraMap k F ((n : k) * c) * (x ^ (n - 1) * D x)
  rw [map_mul, map_natCast]
  ring

end

end AclGeom
