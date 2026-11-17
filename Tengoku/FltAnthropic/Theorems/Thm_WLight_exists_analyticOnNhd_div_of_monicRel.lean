import Tengoku.Seed.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Tengoku.Seed.NumberTheory.ModularForms.Discriminant
import Tengoku.Seed.Geometry.Manifold.Notation
import Tengoku.FltAnthropic.P2M.Sol.S_WLight_exists_analyticOnNhd_div_of_monicRel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WLight_exists_analyticOnNhd_div_of_monicRel.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.exists_analyticOnNhd_div_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {U : Set 𝕜} (hU : IsOpen U) (hUc : IsPreconnected U)
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ}
    (hF : AnalyticOnNhd 𝕜 F U) (hG : AnalyticOnNhd 𝕜 G U) (hG0 : ∃ z ∈ U, G z ≠ 0)
    (hc : ∀ k < n, AnalyticOnNhd 𝕜 (c k) U)
    (hrel : Set.EqOn (F ^ n + ∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) 0 U) :
    ∃ H : 𝕜 → 𝕜, AnalyticOnNhd 𝕜 H U ∧ Set.EqOn F (G * H) U := by exact @_root_.P2MW.S_WLight_exists_analyticOnNhd_div_of_monicRel.solution 𝕜 _ U hU hUc F G c n hF hG hG0 hc hrel
