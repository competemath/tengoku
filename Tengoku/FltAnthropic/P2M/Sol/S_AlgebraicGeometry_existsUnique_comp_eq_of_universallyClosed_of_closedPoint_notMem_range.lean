import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_existsUnique_comp_eq_of_universallyClosed_of_closedPoint_notMem_range.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_existsUnique_comp_eq_of_universallyClosed_of_closedPoint_notMem_range

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry

/--
@isnad1 id=existsun.2h9v.s9.c5f94a69b97f from=translated src=- shape=0728a28c vocab=682a3b0d
-/
theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X Xf X' T : Scheme.{u}} (g : X ⟶ Spec (.of R))
    (i : Xf ⟶ X) [IsOpenImmersion i] (j : X' ⟶ X)
    (hcover : Set.range i ∪ Set.range j = Set.univ)
    (hempty : IsLocalRing.closedPoint R ∉ Set.range (j ≫ g))
    (f : T ⟶ X) [UniversallyClosed (f ≫ g)] :
    ∃! f' : T ⟶ Xf, f' ≫ i = f := by
  have hicl : IsClosed (Set.range i)ᶜ := by
    rw [isClosed_compl_iff, ← Scheme.Hom.coe_opensRange]
    exact i.opensRange.isOpen
  have hrange : Set.range f ⊆ Set.range i := by
    by_contra hne
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := Set.not_subset.mp hne

    have hZ : IsClosed (f ⁻¹' (Set.range i)ᶜ) := hicl.preimage f.continuous
    have himg : IsClosed ((f ≫ g) '' (f ⁻¹' (Set.range i)ᶜ)) := (f ≫ g).isClosedMap _ hZ
    have hmem : IsLocalRing.closedPoint R ∈ (f ≫ g) '' (f ⁻¹' (Set.range i)ᶜ) :=
      (IsLocalRing.specializes_closedPoint ((f ≫ g) t)).mem_closed himg ⟨t, ht, rfl⟩
    obtain ⟨z, hz, hzc⟩ := hmem
    have hzj : f z ∈ Set.range j :=
      ((hcover.symm ▸ Set.mem_univ (f z) : f z ∈ Set.range i ∪ Set.range j)).resolve_left hz
    obtain ⟨x', hx'⟩ := hzj
    exact hempty ⟨x', by rw [Scheme.Hom.comp_apply, hx', ← Scheme.Hom.comp_apply, hzc]⟩
  refine ⟨IsOpenImmersion.lift i f hrange, IsOpenImmersion.lift_fac i f hrange, fun f' hf' ↦ ?_⟩
  rw [← cancel_mono i, hf', IsOpenImmersion.lift_fac]
