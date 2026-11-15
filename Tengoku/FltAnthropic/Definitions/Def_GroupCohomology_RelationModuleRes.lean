import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_RelationModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G G' : Type u} [CommRing k] [Group G] [Group G'] (π : G' →* G)

def freeResMap (B : Rep.{u} k G) : Rep.free k G' B ⟶ Rep.res π (Rep.free k G B) :=
  Rep.freeLift k G' (Rep.res π (Rep.free k G B)) (fun b : B => (Finsupp.single b (MonoidAlgebra.single (1 : G) (1 : k)) : Rep.free k G B))

/--
@isnad1 id=eq.0h5v.s9.c1e84ef9eba0 from=translated src=- shape=76e73e5c vocab=8240f93c
-/
theorem freeResMap_comp_resFunctor_map_freeCover (B : Rep.{u} k G) :
    freeResMap π B ≫ (Rep.resFunctor π).map (freeCover B) = freeCover (Rep.res π B) :=
  Rep.free_ext k G' _ _ _ (fun b => by simp [freeResMap, freeCover, Rep.resMap])

/--
@isnad1 id=eq.0h6v.s11.b30486bce108 from=translated src=- shape=1df8e389 vocab=21228f8e
-/
theorem freeCover_freeResMap_apply (B : Rep.{u} k G) (x : Rep.free k G' B) :
    (freeCover B).hom ((freeResMap π B).hom x) = (freeCover (Rep.res π B)).hom x := by
  have h := congrArg (fun φ => φ.hom x) (freeResMap_comp_resFunctor_map_freeCover π B)
  simpa [Rep.resMap] using h

def relationModule.resMap (B : Rep.{u} k G) : relationModule (Rep.res π B) ⟶ Rep.res π (relationModule B) :=
  Rep.ofHom ⟨LinearMap.codRestrict _ ((freeResMap π B).hom.toLinearMap ∘ₗ (Submodule.subtype _)) (fun x => by
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        Representation.IntertwiningMap.toLinearMap_apply]
      rw [freeCover_freeResMap_apply]
      exact x.2),
    fun g => LinearMap.ext fun x => Subtype.ext (Rep.hom_comm_apply (freeResMap π B) g (x : Rep.free k G' B))⟩

/--
@isnad1 id=eq.0h6v.s12.ca720dc583c3 from=translated src=- shape=15b296d8 vocab=f42664dc
-/
theorem relationModule.resMap_hom_apply_coe (B : Rep.{u} k G) (x : relationModule (Rep.res π B)) :
    ((relationModule.resMap π B).hom x : Rep.free k G B) = (freeResMap π B).hom (x : Rep.free k G' B) := rfl

section Int

variable {H H' : Type} [Group H] [Group H'] (ϖ : H' →* H)

def relationModuleInt.resMap (B : Rep ℤ H) : relationModuleInt (Rep.res ϖ B) ⟶ Rep.res ϖ (relationModuleInt B) :=
  Rep.ofHom ⟨((relationModule.resMap ϖ B).hom.toLinearMap.toAddMonoidHom).toIntLinearMap,
    fun g => LinearMap.ext fun x =>
      (Rep.hom_comm_apply (relationModule.resMap ϖ B) g (show relationModule (Rep.res ϖ B) from x))⟩

/--
@isnad1 id=eq.0h5v.s10.001a5168b01b from=translated src=- shape=cee4ddec vocab=f232d6e1
-/
theorem relationModuleInt.resMap_hom_apply (B : Rep ℤ H) (x : relationModuleInt (Rep.res ϖ B)) :
    (relationModuleInt.resMap ϖ B).hom x =
      (show Rep.res ϖ (relationModuleInt B) from
        (relationModule.resMap ϖ B).hom (show relationModule (Rep.res ϖ B) from x)) := rfl

end Int

end Rep

end
