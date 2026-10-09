/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Tengoku.Seed.Algebra.Category.ModuleCat.Presheaf.Limits

/-!
# Epimorphisms and monomorphisms in the category of presheaves of modules

In this file, we give characterizations of epimorphisms and monomorphisms
in the category of presheaves of modules.

-/

public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

/--
@isnad1 id=epi.1h5v.s10.5c904c8cc6db from=seed src=0 shape=25a1a1c2 vocab=841c7b2e
-/
lemma epi_of_surjective (hf : ∀ ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X)) : Epi f where
  left_cancellation g₁ g₂ hg := by
    ext X m₂
    obtain ⟨m₁, rfl⟩ := hf m₂
    exact ConcreteCategory.congr_hom ((evaluation R X ⋙ forget _).congr_map hg) m₁

/--
@isnad1 id=mono.1h5v.s10.043809cf2d18 from=seed src=0 shape=25a1a1c2 vocab=e31c4085
-/
lemma mono_of_injective (hf : ∀ ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X)) : Mono f where
  right_cancellation {M} g₁ g₂ hg := by
    ext X m
    exact hf (ConcreteCategory.congr_hom ((evaluation R X ⋙ forget _).congr_map hg) m)

variable (f)

instance [Epi f] (X : Cᵒᵖ) : Epi (f.app X) :=
  inferInstanceAs (Epi ((evaluation R X).map f))

instance [Mono f] (X : Cᵒᵖ) : Mono (f.app X) :=
  inferInstanceAs (Mono ((evaluation R X).map f))

/--
@isnad1 id=surjecti.0h6v.s10.f21e1bdd6074 from=seed src=0 shape=52c1538e vocab=841c7b2e
-/
lemma surjective_of_epi [Epi f] (X : Cᵒᵖ) :
    Function.Surjective (f.app X) := by
  rw [← ModuleCat.epi_iff_surjective]
  infer_instance

/--
@isnad1 id=injectiv.0h6v.s10.358a21e513b8 from=seed src=0 shape=52c1538e vocab=e31c4085
-/
lemma injective_of_mono [Mono f] (X : Cᵒᵖ) :
    Function.Injective (f.app X) := by
  rw [← ModuleCat.mono_iff_injective]
  infer_instance

/--
@isnad1 id=iff.0h5v.s10.f7d0ed96e478 from=seed src=0 shape=c5d602f2 vocab=841c7b2e
-/
lemma epi_iff_surjective :
    Epi f ↔ ∀ ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X) :=
  ⟨fun _ ↦ surjective_of_epi f, epi_of_surjective⟩

/--
@isnad1 id=iff.0h5v.s10.dc516e245ec3 from=seed src=0 shape=c5d602f2 vocab=e31c4085
-/
lemma mono_iff_surjective :
    Mono f ↔ ∀ ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X) :=
  ⟨fun _ ↦ injective_of_mono f, mono_of_injective⟩

end PresheafOfModules
