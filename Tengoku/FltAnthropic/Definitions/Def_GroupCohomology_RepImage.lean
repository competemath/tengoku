import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_RepCokernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open CategoryTheory

namespace GroupCohomology.RepImage

universe u

variable {k G : Type u} [CommRing k] [Group G] {X Y : Rep.{u} k G} (f : X ⟶ Y)

noncomputable abbrev obj : Rep.{u} k G :=
  Rep.of (Representation.subrepresentation Y.ρ (LinearMap.range f.hom.toLinearMap) fun g => by
    rintro _ ⟨x, rfl⟩
    exact ⟨X.ρ g x, Rep.hom_comm_apply f g x⟩)

noncomputable def ι : obj f ⟶ Y := Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

noncomputable def toImage : X ⟶ obj f :=
  Rep.ofHom ⟨LinearMap.rangeRestrict f.hom.toLinearMap, fun g => LinearMap.ext fun x => Subtype.ext (Rep.hom_comm_apply f g x)⟩

/--
@isnad1 id=eq.0h6v.s10.97c01798addd from=translated src=- shape=e2264c34 vocab=657d49d0
-/
theorem toImage_hom_apply_coe (x : X) : ((toImage f).hom x : Y) = f.hom x := rfl

noncomputable def map {X' Y' : Rep.{u} k G} (f' : X' ⟶ Y') (α : X ⟶ X') (β : Y ⟶ Y') (w : f ≫ β = α ≫ f') : obj f ⟶ obj f' :=
  Rep.ofHom ⟨LinearMap.codRestrict _ (β.hom.toLinearMap ∘ₗ Submodule.subtype _) (by
      rintro ⟨_, x, rfl⟩
      refine ⟨α.hom x, ?_⟩
      change f'.hom (α.hom x) = β.hom (f.hom x)
      have := congrArg (fun φ : X ⟶ Y' => φ.hom x) w
      exact this.symm),
    fun g => LinearMap.ext fun y => Subtype.ext (Rep.hom_comm_apply β g (y : Y))⟩

/--
@isnad1 id=eq.1h11v.s11.52625e0d2786 from=translated src=- shape=41966646 vocab=68524ec9
-/
theorem map_hom_apply_coe {X' Y' : Rep.{u} k G} (f' : X' ⟶ Y') (α : X ⟶ X') (β : Y ⟶ Y') (w : f ≫ β = α ≫ f') (y : obj f) :
    ((map f f' α β w).hom y : Y') = β.hom (y : Y) := rfl

noncomputable def seq : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (ι f) (GroupCohomology.RepCokernel.π f)
    (Rep.hom_ext (DFunLike.ext _ _ fun y => (GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff f _).2 y.2))

end GroupCohomology.RepImage
