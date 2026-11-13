/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Tengoku.Seed.Algebra.Category.ModuleCat.Ext.HasExt
import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Tengoku.Seed.Algebra.Homology.ShortComplex.ShortExact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Short exact sequences of modules

This module gives a splitting criterion for short exact sequences of module objects in terms of
degree-one extensions.
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace RepresentationTheory.CategoryTheory.Abelian.ModuleCat.ShortExact

variable {R : Type u} [Ring R] [Small.{v} R]

/-- Under the stated exactness and degree-one extension uniqueness hypotheses, the middle module object is isomorphic to the biproduct of the endpoints.
@isnad1 id=nonempty.3h6v.s7.0e52f51f3d20 from=translated src=- shape=904e0306 vocab=132280d7
-/
theorem nonempty_iso_biprod_of_shortExact_of_extOne_subsingleton
    {A B C : ModuleCat.{v} R} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0)
    (hSES : (ShortComplex.mk f g w).ShortExact)
    (hExt : Subsingleton (Abelian.Ext C A 1)) :
    Nonempty (B ≅ A ⊞ C) := by
  haveI := hExt
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hSES A
    (Abelian.Ext.mk₀ (𝟙 A)) (show (1 : ℕ) + 0 = 1 from rfl) (Subsingleton.elim _ 0)
  have hfr : f ≫ Abelian.Ext.homEquiv₀ x₂ = 𝟙 A := by
    apply (Abelian.Ext.mk₀_bijective A A).injective
    rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_homEquiv₀_apply]
    exact hx₂
  exact ⟨(ShortComplex.Splitting.ofExactOfRetraction _ hSES.exact
    (Abelian.Ext.homEquiv₀ x₂) hfr hSES.epi_g).isoBinaryBiproduct⟩

end RepresentationTheory.CategoryTheory.Abelian.ModuleCat.ShortExact
