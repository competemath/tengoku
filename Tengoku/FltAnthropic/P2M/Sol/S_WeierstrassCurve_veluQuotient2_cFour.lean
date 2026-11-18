import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_VeluOrderTwo

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_WeierstrassCurve_veluQuotient2_cFour.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_WeierstrassCurve_veluQuotient2_cFour

open WeierstrassCurve in
theorem solution {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x₀ y₀ : R) :
    (W.veluQuotient2 x₀ y₀).c₄ = W.c₄ + 240 * W.veluGx x₀ y₀ := by
  have hb₄ : (W.veluQuotient2 x₀ y₀).b₄ = W.b₄ - 10 * W.veluGx x₀ y₀ := by
    simp only [b₄, veluQuotient2_a₁, veluQuotient2_a₃, veluQuotient2_a₄]; ring
  simp only [c₄, veluQuotient2_b₂, hb₄]; ring
