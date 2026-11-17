import Tengoku.Seed.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Tengoku.Seed.NumberTheory.ModularForms.Discriminant
import Tengoku.Seed.Geometry.Manifold.Notation
import Tengoku.FltAnthropic.P2M.Sol.S_WLight_exists_mdifferentiable_div_of_monicRel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WLight_exists_mdifferentiable_div_of_monicRel.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

/--
@isnad1 id=ex.5h4v.s9.2eb944b07c5d from=translated src=- shape=99d27d5c vocab=e6d384e4
-/
theorem WLight.exists_mdifferentiable_div_of_monicRel {a b : ℍ → ℂ} {c : ℕ → ℍ → ℂ} {d : ℕ}
    (hahol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a) (hbhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b)
    (hb0 : b ≠ 0) (hc : ∀ k < d, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c k))
    (hrel : a ^ d + ∑ k ∈ Finset.range d, c k * b ^ (d - k) * a ^ k = 0) :
    ∃ F : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ F * b = a := by exact @_root_.P2MW.S_WLight_exists_mdifferentiable_div_of_monicRel.solution a b c d hahol hbhol hb0 hc hrel
