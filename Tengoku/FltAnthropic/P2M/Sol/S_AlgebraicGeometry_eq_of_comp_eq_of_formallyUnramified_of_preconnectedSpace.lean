import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace P2mUnramifiedRigidity

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/--
@isnad1 id=isopen.0h3v.s8.2398d0fc2602 from=translated src=- shape=9b0dd15d vocab=2d0d9714
-/
theorem isOpen_range_diagonal [FormallyUnramified g] [LocallyOfFiniteType g] :
    IsOpen (Set.range (pullback.diagonal g).base) :=
  (pullback.diagonal g).isOpenEmbedding.isOpen_range

/--
@isnad1 id=isclosed.0h3v.s8.0b970f1a8988 from=translated src=- shape=323ea337 vocab=9a0a96a7
-/
theorem isClosed_range_diagonal [IsSeparated g] :
    IsClosed (Set.range (pullback.diagonal g).base) := by
  haveI : IsClosedImmersion (pullback.diagonal g) := IsSeparated.isClosedImmersion_diagonal
  exact (pullback.diagonal g).isClosedEmbedding.isClosed_range

variable {g}

/--
@isnad1 id=eq.2h8v.s7.35b987f75289 from=translated src=- shape=b8f4c0f7 vocab=5daf7fff
-/
theorem comp_lift_eq_comp_diagonal {T Z : Scheme.{u}} (u₁ u₂ : T ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
    (p : Z ⟶ T) (hp : p ≫ u₁ = p ≫ u₂) :
    p ≫ pullback.lift u₁ u₂ hg = (p ≫ u₁) ≫ pullback.diagonal g := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
      Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
      Category.comp_id, hp]

theorem eq_of_comp_eq {T Z : Scheme.{u}} [FormallyUnramified g] [LocallyOfFiniteType g]
    [IsSeparated g] [PreconnectedSpace T]
    (u₁ u₂ : T ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
    (p : Z ⟶ T) [Nonempty Z] (hp : p ≫ u₁ = p ≫ u₂) : u₁ = u₂ := by
  set v : T ⟶ pullback g g := pullback.lift u₁ u₂ hg with hv
  set W : Set T := v.base ⁻¹' Set.range (pullback.diagonal g).base with hW
  have hWclopen : IsClopen W :=
    ⟨(isClosed_range_diagonal g).preimage v.base.hom.continuous,
      (isOpen_range_diagonal g).preimage v.base.hom.continuous⟩
  have hWne : W.Nonempty := by
    obtain ⟨z⟩ := ‹Nonempty Z›
    refine ⟨p.base z, ?_⟩
    show v.base (p.base z) ∈ Set.range (pullback.diagonal g).base
    refine ⟨u₁.base (p.base z), ?_⟩
    have h := comp_lift_eq_comp_diagonal u₁ u₂ hg p hp
    have h' := congrArg (fun φ : Z ⟶ pullback g g => φ.base z) h
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at h'
    exact h'.symm
  have hWuniv : W = Set.univ := by
    rcases isClopen_iff.mp hWclopen with h | h
    · exact absurd h hWne.ne_empty
    · exact h
  have hrange : Set.range v.base ⊆ Set.range (pullback.diagonal g).base := by
    rintro _ ⟨t, rfl⟩
    have ht : t ∈ W := by rw [hWuniv]; exact Set.mem_univ t
    exact ht
  set l : T ⟶ X := IsOpenImmersion.lift (pullback.diagonal g) v hrange with hl
  have hlv : l ≫ pullback.diagonal g = v := IsOpenImmersion.lift_fac _ _ hrange
  have h1 : u₁ = l := by
    calc u₁ = v ≫ pullback.fst g g := by rw [hv, pullback.lift_fst]
      _ = (l ≫ pullback.diagonal g) ≫ pullback.fst g g := by rw [hlv]
      _ = l := by simp
  have h2 : u₂ = l := by
    calc u₂ = v ≫ pullback.snd g g := by rw [hv, pullback.lift_snd]
      _ = (l ≫ pullback.diagonal g) ≫ pullback.snd g g := by rw [hlv]
      _ = l := by simp
  rw [h1, h2]

end P2mUnramifiedRigidity

/--
@isnad1 id=eq.2h8v.s7.0b3c72a4bce0 from=translated src=- shape=68518071 vocab=16de8f4a
-/
theorem solution
    {X Y T Z : Scheme.{u}} (g : X ⟶ Y) [FormallyUnramified g] [LocallyOfFiniteType g]
    [IsSeparated g] [PreconnectedSpace T]
    (u₁ u₂ : T ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
    (p : Z ⟶ T) [Nonempty Z] (hp : p ≫ u₁ = p ≫ u₂) :
    u₁ = u₂ :=
  P2mUnramifiedRigidity.eq_of_comp_eq u₁ u₂ hg p hp
