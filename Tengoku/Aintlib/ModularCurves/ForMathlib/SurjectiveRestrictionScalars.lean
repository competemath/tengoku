import Tengoku.Seed.Algebra.Category.ModuleCat.ChangeOfRings
import Tengoku.Seed.CategoryTheory.Adjunction.FullyFaithful

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Restriction of scalars along surjective homomorphisms

This file records full faithfulness of restriction of scalars along a surjective ring
homomorphism and the resulting counit isomorphism for extension of scalars.
-/

universe u v w

open CategoryTheory

namespace ModuleCat

variable {R : Type u} {S : Type v}

/-- Restriction of scalars along a surjective ring homomorphism is fully faithful.-/
noncomputable def restrictScalarsFullyFaithfulOfSurjective
    [Ring R] [Ring S] (f : R →+* S) (hf : Function.Surjective f) :
    (restrictScalars.{w} f).FullyFaithful where
  preimage g := ofHom ⟨g.hom.toAddHom, by
    intro s x
    obtain ⟨r, rfl⟩ := hf s
    exact g.hom.map_smul r x⟩
  map_preimage g := by
    ext x
    rfl
  preimage_map g := by
    ext x
    rfl

/-- The extension--restriction counit along a surjective ring homomorphism is invertible.
@isnad1 id=isiso.1h4v.s8.9989a0da777d from=translated src=- shape=06bd3d9e vocab=f9c4ba85
-/
theorem isIso_extendRestrictScalars_counit_app_of_surjective
    [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (M : ModuleCat.{max w v} S) :
    IsIso ((extendRestrictScalarsAdj.{w} f).counit.app M) := by
  let h : (restrictScalars.{max w v} f).FullyFaithful :=
    restrictScalarsFullyFaithfulOfSurjective f hf
  letI : (restrictScalars.{max w v} f).Full := h.full
  letI : (restrictScalars.{max w v} f).Faithful := h.faithful
  infer_instance

end ModuleCat
