import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_RelationModule
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_RelationModuleRes
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_RepCokernel
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_RepImage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open CategoryTheory

noncomputable section

namespace Rep

section generalK

universe u

variable {k G : Type u} [CommRing k] [Group G]

def preHom {A A' : Rep.{u} k G} (f : A ⟶ A') (E : Rep.{u} k G) : (ihom A').obj E ⟶ (ihom A).obj E :=
  Rep.ofHom ⟨LinearMap.lcomp k E f.hom.toLinearMap, fun g => LinearMap.ext fun x => by
    change (((ihom A').obj E).ρ g x) ∘ₗ f.hom.toLinearMap = ((ihom A).obj E).ρ g (x ∘ₗ f.hom.toLinearMap)
    erw [Rep.ihom_obj_ρ_apply, Rep.ihom_obj_ρ_apply]
    apply LinearMap.ext
    intro a
    simp only [LinearMap.coe_comp, Function.comp_apply, Representation.IntertwiningMap.toLinearMap_apply]
    rw [Rep.hom_comm_apply]⟩

/--
@isnad1 id=eq.0h7v.s12.0223fc66b5d2 from=translated src=- shape=99aa0554 vocab=015e009f
-/
theorem preHom_hom_apply {A A' : Rep.{u} k G} (f : A ⟶ A') (E : Rep.{u} k G) (x : (ihom A').obj E) :
    (preHom f E).hom x = (show A' →ₗ[k] E from x) ∘ₗ f.hom.toLinearMap := rfl

/--
@isnad1 id=eq.0h8v.s9.5d59a66a8af1 from=translated src=- shape=3ddd3cc7 vocab=000d7177
-/
theorem preHom_comp {A A' A'' : Rep.{u} k G} (f : A ⟶ A') (f' : A' ⟶ A'') (E : Rep.{u} k G) :
    preHom f' E ≫ preHom f E = preHom (f ≫ f') E :=
  Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)

end generalK

section Int

variable {G : Type} [Group G] (B E : Rep ℤ G)

abbrev preCover : (ihom B).obj E ⟶ (ihom (Rep.free ℤ G B)).obj E := preHom (Rep.freeCover B) E

abbrev preι : (ihom (Rep.free ℤ G B)).obj E ⟶ (ihom (Rep.relationModuleInt B)).obj E := preHom (Rep.relationModuleInt.ι B) E

abbrev defectQ : Rep ℤ G := GroupCohomology.RepImage.obj (preι B E)

abbrev defectX : Rep ℤ G := GroupCohomology.RepCokernel.obj (preι B E)

abbrev homSeq₂ : ShortComplex (Rep ℤ G) := GroupCohomology.RepImage.seq (preι B E)

end Int

section Infl

variable {G G' : Type} [Group G] [Group G'] (π : G' →* G) (B E : Rep ℤ G) (E' : Rep ℤ G') (φ : Rep.res π E ⟶ E')

end Infl

end Rep

end
