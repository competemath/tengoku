import Tengoku.Seed.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Tengoku.Seed.NumberTheory.ModularForms.QExpansion
import Tengoku.Seed.NumberTheory.ModularForms.Discriminant
import Tengoku.Seed.Geometry.Manifold.Notation
import Tengoku.Seed.FieldTheory.IntermediateField.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_WLight_isBoundedAtImInfty_iff_qExpansion_coeff_lt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WLight_isBoundedAtImInfty_iff_qExpansion_coeff_lt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

/--
@isnad1 id=iff.3h3v.s8.6d70d7110adf from=translated src=- shape=be90a6cc vocab=91f4000a
-/
theorem WLight.isBoundedAtImInfty_iff_qExpansion_coeff_lt (N : ℕ) [NeZero N] {F : ℍ → ℂ} {M : ℕ}
    (hFhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) N)
    (hFbd : IsBoundedAtImInfty (F * ModularForm.discriminant ^ M)) :
    IsBoundedAtImInfty F ↔
      ∀ n < N * M,
        (UpperHalfPlane.qExpansion N (F * ModularForm.discriminant ^ M)).coeff n = 0 := by exact @_root_.P2MW.S_WLight_isBoundedAtImInfty_iff_qExpansion_coeff_lt.solution N _ F M hFhol hFper hFbd
