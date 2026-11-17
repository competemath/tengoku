import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HenselianLocalRing_of_isAdicComplete_maximalIdeal.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HenselianLocalRing_of_isAdicComplete_maximalIdeal

set_option autoImplicit false

universe u

/--
@isnad1 id=henselia.0h1v.s5.edcef868018c from=translated src=- shape=87ff805b vocab=70266713
-/
theorem solution (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : HenselianLocalRing R := by
  refine { is_henselian := fun f hf a₀ h₁ h₂ => ?_ }
  exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))
