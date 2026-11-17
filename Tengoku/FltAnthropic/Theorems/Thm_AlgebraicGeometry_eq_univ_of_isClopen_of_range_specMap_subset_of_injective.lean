import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.eq_univ_of_isClopen_of_range_specMap_subset_of_injective
    {R₀ L : Type} [CommRing R₀] [CommRing L] (φ : R₀ →+* L) (hφ : Function.Injective φ)
    (W : Set ↥(Spec (CommRingCat.of R₀))) (hW : IsClopen W)
    (hWL : Set.range (Spec.map (CommRingCat.ofHom φ)).base ⊆ W) : W = Set.univ := by exact @_root_.P2MW.S_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective.solution R₀ L _ _ φ hφ W hW hWL
