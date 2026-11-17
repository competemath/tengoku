import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_existsUnique_exists_comp_eq_of_isLocalHom_of_forall_ne.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_existsUnique_exists_comp_eq_of_isLocalHom_of_forall_ne

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=existsun.2h7v.s10.3c46a7770e5b from=translated src=- shape=3503fcc3 vocab=3c890fe6
-/
theorem solution
    {R A' : Type u} [CommRing R] [IsLocalRing R] [CommRing A'] [IsLocalRing A']
    (φ : R →+* A') [IsLocalHom φ]
    {N : Scheme.{u}} (g : N ⟶ Spec (CommRingCat.of R))
    (𝒰 : Scheme.OpenCover.{v} N)
    (hne : ∀ i k : 𝒰.I₀, i ≠ k → ∀ n ∈ Set.range (𝒰.f i).base ∩ Set.range (𝒰.f k).base,
      g.base n ≠ IsLocalRing.closedPoint R)
    (s : Spec (CommRingCat.of A') ⟶ N) (hs : s ≫ g = Spec.map (CommRingCat.ofHom φ)) :
    ∃! i : 𝒰.I₀, ∃ s' : Spec (CommRingCat.of A') ⟶ 𝒰.X i, s' ≫ 𝒰.f i = s := by
  classical

  set x₀ : ↥(Spec (CommRingCat.of A')) := IsLocalRing.closedPoint A' with hx₀
  set n : ↥N := s.base x₀ with hn
  have hgn : g.base n = IsLocalRing.closedPoint R := by
    have h1 : g.base n = (s ≫ g).base x₀ := rfl
    rw [h1, hs]
    exact IsLocalRing.comap_closedPoint φ

  have hrange : ∀ i : 𝒰.I₀, n ∈ Set.range (𝒰.f i).base → Set.range s.base ⊆ Set.range (𝒰.f i).base := by
    intro i hi
    rintro _ ⟨x, rfl⟩
    have hx : x ⤳ x₀ := IsLocalRing.specializes_closedPoint x
    exact (hx.map s.base.hom.continuous).mem_open (IsOpenImmersion.isOpen_range (𝒰.f i)) hi

  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq n
  have hni : n ∈ Set.range (𝒰.f i).base := ⟨y, hy⟩
  refine ⟨i, ⟨IsOpenImmersion.lift (𝒰.f i) s (hrange i hni), IsOpenImmersion.lift_fac _ _ _⟩, ?_⟩

  rintro k ⟨s', hs'⟩
  by_contra hki
  have hnk : n ∈ Set.range (𝒰.f k).base := ⟨s'.base x₀, by rw [hn, ← hs']; rfl⟩
  exact hne k i hki n ⟨hnk, hni⟩ hgn

