import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

def freeCover (B : Rep.{u} k G) : Rep.free k G B ⟶ B :=
  Rep.freeLift k G B (fun b : B => b)

abbrev relationModule (B : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (Representation.subrepresentation (Rep.free k G B).ρ (LinearMap.ker (freeCover B).hom.toLinearMap) fun g x hx => by
    simp only [Submodule.mem_comap, LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply] at hx ⊢
    rw [Rep.hom_comm_apply, hx, map_zero])

def relationModule.ι (B : Rep.{u} k G) : relationModule B ⟶ Rep.free k G B :=
  Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

/--
@isnad1 id=eq.0h4v.s10.3a560e7be504 from=translated src=- shape=cb499917 vocab=d1ba2af0
-/
theorem relationModule.ι_hom_apply (B : Rep.{u} k G) (x : relationModule B) :
    (relationModule.ι B).hom x = (x : Rep.free k G B) := rfl

/--
@isnad1 id=eq.0h4v.s10.e5d4aed03ede from=translated src=- shape=9e3ba8f9 vocab=0998dad5
-/
theorem freeCover_hom_apply_ι (B : Rep.{u} k G) (x : relationModule B) :
    (freeCover B).hom ((relationModule.ι B).hom x) = 0 := x.2

abbrev relationSeq (B : Rep.{u} k G) : ShortComplex (Rep.{u} k G) where
  X₁ := relationModule B
  X₂ := Rep.free k G B
  X₃ := B
  f := relationModule.ι B
  g := freeCover B
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => x.2))

/--
@isnad1 id=eq.0h3v.s8.7393e1e93c13 from=translated src=- shape=e58d5f98 vocab=d6dec1e9
-/
theorem relationSeq_f (B : Rep.{u} k G) : (relationSeq B).f = relationModule.ι B := rfl
/--
@isnad1 id=eq.0h3v.s8.6841fde280d6 from=translated src=- shape=e58d5f98 vocab=91c8b8f8
-/
theorem relationSeq_g (B : Rep.{u} k G) : (relationSeq B).g = freeCover B := rfl

section Int

variable {G : Type} [Group G]

def relationCarrier (B : Rep ℤ G) : Type := relationModule B

instance relationCarrier.instAddCommGroup (B : Rep ℤ G) : AddCommGroup (relationCarrier B) :=
  inferInstanceAs (AddCommGroup (relationModule B))

def relationRepInt (B : Rep ℤ G) : Representation ℤ G (relationCarrier B) where
  toFun g := (((relationModule B).ρ g).toAddMonoidHom).toIntLinearMap
  map_one' := by
    apply LinearMap.ext
    intro x
    change ((relationModule B).ρ 1) x = x
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change ((relationModule B).ρ (g * h)) x = ((relationModule B).ρ g) (((relationModule B).ρ h) x)
    rw [map_mul]
    rfl

/--
@isnad1 id=eq.0h4v.s10.399cd3f45905 from=translated src=- shape=991a1bb3 vocab=ffe4b323
-/
theorem relationRepInt_apply (B : Rep ℤ G) (g : G) (x : relationCarrier B) :
    relationRepInt B g x = ((relationModule B).ρ g : relationModule B → relationModule B) x := rfl

abbrev relationModuleInt (B : Rep ℤ G) : Rep ℤ G := Rep.of (relationRepInt B)

def relationModuleInt.ι (B : Rep ℤ G) : relationModuleInt B ⟶ Rep.free ℤ G B :=
  Rep.ofHom ⟨((relationModule.ι B).hom.toLinearMap.toAddMonoidHom).toIntLinearMap, fun _ => rfl⟩

/--
@isnad1 id=eq.0h3v.s10.95e0a0651501 from=translated src=- shape=61b04d51 vocab=37631521
-/
theorem relationModuleInt.ι_hom_apply (B : Rep ℤ G) (x : relationModuleInt B) :
    (relationModuleInt.ι B).hom x = (relationModule.ι B).hom (show relationModule B from x) := rfl

/--
@isnad1 id=eq.0h2v.s7.fda820295c77 from=translated src=- shape=1cae97f9 vocab=6a0fd984
-/
theorem relationModuleInt_ι_comp_freeCover (B : Rep ℤ G) : relationModuleInt.ι B ≫ freeCover B = 0 :=
  Rep.hom_ext (DFunLike.ext _ _ fun x => freeCover_hom_apply_ι B (show relationModule B from x))

abbrev relationSeqInt (B : Rep ℤ G) : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (relationModuleInt.ι B) (freeCover B) (relationModuleInt_ι_comp_freeCover B)

end Int

end Rep

end
