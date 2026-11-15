import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R₀ L : Type} [CommRing R₀] [CommRing L] (φ : R₀ →+* L) (hφ : Function.Injective φ)
    (W : Set ↥(Spec (CommRingCat.of R₀))) (hW : IsClopen W)
    (hWL : Set.range (Spec.map (CommRingCat.ofHom φ)).base ⊆ W) : W = Set.univ := by
  have hdense : DenseRange (Spec.map (CommRingCat.ofHom φ)).base :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2
      (by rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)
  apply Set.eq_univ_of_univ_subset
  rw [← hdense.closure_range]
  exact (hW.1.closure_subset_iff).2 hWL
