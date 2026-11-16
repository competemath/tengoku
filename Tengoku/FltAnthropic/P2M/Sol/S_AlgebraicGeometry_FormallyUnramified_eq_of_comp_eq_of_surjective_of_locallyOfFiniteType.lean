import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_surjective_of_locallyOfFiniteType.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_surjective_of_locallyOfFiniteType

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace UnramifiedLiftUnique

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/--
@isnad1 id=eq.2h8v.s7.35b987f75289 from=translated src=- shape=b8f4c0f7 vocab=5daf7fff
-/
theorem comp_lift_eq_comp_diagonal {T T₀ : Scheme.{u}} (u u' : T ⟶ X) (hf : u ≫ f = u' ≫ f)
    (j : T₀ ⟶ T) (hj : j ≫ u = j ≫ u') :
    j ≫ pullback.lift u u' hf = (j ≫ u) ≫ pullback.diagonal f := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id, hj]

theorem eq_of_comp_eq {T T₀ : Scheme.{u}} [FormallyUnramified f] [LocallyOfFiniteType f]
    (j : T₀ ⟶ T) [Surjective j] (u u' : T ⟶ X) (hf : u ≫ f = u' ≫ f) (hj : j ≫ u = j ≫ u') :
    u = u' := by
  set v : T ⟶ pullback f f := pullback.lift u u' hf with hv
  have hrange : Set.range v.base ⊆ Set.range (pullback.diagonal f).base := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t₀, rfl⟩ := j.surjective t
    refine ⟨u.base (j.base t₀), ?_⟩
    have h := comp_lift_eq_comp_diagonal u u' hf j hj
    have h' := congrArg (fun φ : T₀ ⟶ pullback f f => φ.base t₀) h
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at h'
    exact h'.symm
  set l : T ⟶ X := IsOpenImmersion.lift (pullback.diagonal f) v hrange with hl
  have hlv : l ≫ pullback.diagonal f = v := IsOpenImmersion.lift_fac _ _ hrange
  have h1 : u = l := by
    calc u = v ≫ pullback.fst f f := by rw [hv, pullback.lift_fst]
      _ = (l ≫ pullback.diagonal f) ≫ pullback.fst f f := by rw [hlv]
      _ = l := by simp
  have h2 : u' = l := by
    calc u' = v ≫ pullback.snd f f := by rw [hv, pullback.lift_snd]
      _ = (l ≫ pullback.diagonal f) ≫ pullback.snd f f := by rw [hlv]
      _ = l := by simp
  rw [h1, h2]

end UnramifiedLiftUnique

/--
@isnad1 id=eq.2h8v.s7.3deac813c930 from=translated src=- shape=f5e079ce vocab=11bad857
-/
theorem solution
    {X Y T T₀ : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (j : T₀ ⟶ T) [Surjective j] (u u' : T ⟶ X) (hf : u ≫ f = u' ≫ f) (hj : j ≫ u = j ≫ u') :
    u = u' :=
  UnramifiedLiftUnique.eq_of_comp_eq j u u' hf hj
