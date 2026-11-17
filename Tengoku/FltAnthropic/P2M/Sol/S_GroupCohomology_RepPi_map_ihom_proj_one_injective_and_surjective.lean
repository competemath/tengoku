import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_RepPi
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_RelationModule
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_RelationModuleRes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GroupCohomology_RepPi_map_ihom_proj_one_injective_and_surjective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GroupCohomology_RepPi_map_ihom_proj_one_injective_and_surjective

set_option autoImplicit false
open CategoryTheory

namespace ShapiroJ2
open groupCohomology

universe u
variable {k G : Type u} [CommRing k] [Group G] {ι : Type u} (X : ι → Rep.{u} k G) (R : Rep.{u} k G)

local notation "J" => GroupCohomology.RepPi.obj X

abbrev lin {Y : Rep.{u} k G} (f : (ihom R).obj Y) : R →ₗ[k] Y := f

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h7v.s13.385fbb2b6d76 from=translated src=- shape=acd274da vocab=afce3d4b
-/
lemma ihom_ρ_apply {Y : Rep.{u} k G} (g : G) (f : (ihom R).obj Y) (r : R) :
    lin R (((ihom R).obj Y).ρ g f) r = Y.ρ g (lin R f (R.ρ g⁻¹ r)) := rfl

abbrev piLin (f : ∀ i, (ihom R).obj (X i)) : (ihom R).obj J :=
  show R →ₗ[k] ((i : ι) → X i) from LinearMap.pi fun i => lin R (f i)

/--
@isnad1 id=eq.0h7v.s12.a089969c4ca5 from=translated src=- shape=063cf3ba vocab=8d82be9a
-/
lemma proj_piLin (f : ∀ i, (ihom R).obj (X i)) (i : ι) :
    ((ihom R).map (GroupCohomology.RepPi.proj X i)).hom (piLin X R f) = f i := by
  apply LinearMap.ext
  intro r
  rfl

/--
@isnad1 id=eq.0h7v.s14.6740cc2caaf3 from=translated src=- shape=a513eb8e vocab=b5a73df9
-/
lemma ρ_piLin (g : G) (f : ∀ i, (ihom R).obj (X i)) :
    ((ihom R).obj J).ρ g (piLin X R f) = piLin X R (fun i => ((ihom R).obj (X i)).ρ g (f i)) := by
  apply LinearMap.ext
  intro r
  funext i
  rw [ihom_ρ_apply]
  change (X i).ρ g (lin R (piLin X R f) (R.ρ g⁻¹ r) i) = lin R (((ihom R).obj (X i)).ρ g (f i)) r
  rw [ihom_ρ_apply]
  rfl

noncomputable def piCocycle (z : ∀ i, cocycles₁ ((ihom R).obj (X i))) : cocycles₁ ((ihom R).obj J) :=
  ⟨fun g => piLin X R (fun i => z i g), (mem_cocycles₁_iff _).2 fun g h => by
    rw [ρ_piLin]
    apply LinearMap.ext; intro r; funext i
    change lin R (z i (g * h)) r = lin R (((ihom R).obj (X i)).ρ g (z i h)) r + lin R (z i g) r
    rw [(mem_cocycles₁_iff (z i)).1 (z i).2 g h]
    rfl⟩

/--
@isnad1 id=eq.0h7v.s16.a8633b44c0fe from=translated src=- shape=4f9dec25 vocab=ba02be9a
-/
lemma mapCocycles₁_proj_piCocycle (z : ∀ i, cocycles₁ ((ihom R).obj (X i))) (i : ι) :
    mapCocycles₁ (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) (piCocycle X R z) = z i := by
  apply Subtype.ext
  funext g
  rw [cocycles₁.val_eq_coe, coe_mapCocycles₁]
  change ((ihom R).map (GroupCohomology.RepPi.proj X i)).hom (piLin X R (fun i => z i g)) = _
  rw [proj_piLin]
  rfl

/--
@isnad1 id=ex.0h6v.s12.6c931309a9e9 from=translated src=- shape=75af359f vocab=72eeb473
-/
theorem surj (y : ∀ i, groupCohomology ((ihom R).obj (X i)) 1) :
    ∃ x : groupCohomology ((ihom R).obj J) 1,
      ∀ i, (map (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) 1).hom x = y i := by
  have hs : ∀ i, ∃ z : cocycles₁ ((ihom R).obj (X i)), H1π _ z = y i := fun i =>
    (ModuleCat.epi_iff_surjective (H1π ((ihom R).obj (X i)))).1 inferInstance (y i)
  choose z hz using hs
  refine ⟨H1π _ (piCocycle X R z), fun i => ?_⟩
  have := H1π_comp_map_apply (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) (piCocycle X R z)
  rw [mapCocycles₁_proj_piCocycle, hz] at this
  exact this

/--
@isnad1 id=eq.1h6v.s12.95eb54f9e5df from=translated src=- shape=855075f2 vocab=72eeb473
-/
theorem inj (x : groupCohomology ((ihom R).obj J) 1)
    (hx : ∀ i, (map (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) 1).hom x = 0) : x = 0 := by
  induction x using H1_induction_on with | @h z =>
  have hc : ∀ i, ∃ y : (ihom R).obj (X i), (d₀₁ _).hom y =
      ⇑(mapCocycles₁ (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) z) := fun i => by
    have e := H1π_comp_map_apply (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) z
    have h : H1π _ (mapCocycles₁ (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) z) = 0 :=
      e.symm.trans (hx i)
    rw [H1π_eq_zero_iff] at h
    exact h
  choose y hy using hc
  rw [H1π_eq_zero_iff]
  refine ⟨piLin X R y, ?_⟩
  funext g
  erw [d₀₁_hom_apply]
  rw [ρ_piLin]
  change piLin X R (fun i => ((ihom R).obj (X i)).ρ g (y i)) - piLin X R y = lin R (z g)
  apply LinearMap.ext; intro r; funext i
  have h1 := congrFun (hy i) g
  erw [d₀₁_hom_apply, coe_mapCocycles₁] at h1
  have h2 := congrArg (fun f => lin R f r) h1
  exact h2

end ShapiroJ2

/--
@isnad1 id=and.0h4v.s13.b1d16f70949f from=translated src=- shape=cb4a6846 vocab=cac20cb4
-/
theorem solution
    {G : Type} [Group G] {ι : Type} [Finite ι] (X : ι → Rep ℤ G) (R : Rep ℤ G) :
    (∀ x : groupCohomology ((ihom R).obj (GroupCohomology.RepPi.obj X)) 1,
        (∀ i, (groupCohomology.map (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) 1).hom x = 0) → x = 0) ∧
    (∀ y : ∀ i, groupCohomology ((ihom R).obj (X i)) 1,
        ∃ x : groupCohomology ((ihom R).obj (GroupCohomology.RepPi.obj X)) 1,
          ∀ i, (groupCohomology.map (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) 1).hom x = y i) :=
  ⟨ShapiroJ2.inj X R, ShapiroJ2.surj X R⟩
