/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Algebra.Category.Grp.ForgetCorepresentable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Naturality of `AddCommGrpCat.uliftZMultiplesAddEquiv`

Mathlib's `uliftZMultiplesAddEquiv G : (of (ULift ℤ) ⟶ G) ≃+ G` is evaluation at `1`, so it
commutes with postcomposition. Mathlib states the equivalence but not this naturality, which
the degree-zero comparison between `Ext` and sheaf cohomology uses.
-/

universe u

open CategoryTheory

namespace AddCommGrpCat

/-- `uliftZMultiplesAddEquiv` is evaluation at `1`, so it is natural in the target.
@isnad1 id=eq.0h4v.s9.92970a97c7f3 from=translated src=- shape=8573368e vocab=191af326
-/
lemma uliftZMultiplesAddEquiv_comp {G H : AddCommGrpCat.{u}} (φ : of (ULift.{u} ℤ) ⟶ G)
    (g : G ⟶ H) :
    uliftZMultiplesAddEquiv H (φ ≫ g) = g (uliftZMultiplesAddEquiv G φ) := rfl

end AddCommGrpCat
