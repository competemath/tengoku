import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_Lp_finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_Lp_finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {𝕜 : Type*} [RCLike 𝕜]
    (V : Submodule 𝕜 (Lp 𝕜 2 μ)) (C : ℝ)
    (hV : ∀ φ ∈ V, ∀ᵐ x ∂μ, ‖(φ : X → 𝕜) x‖ ≤ C * ‖φ‖) :
    FiniteDimensional 𝕜 V ∧ (Module.finrank 𝕜 V : ℝ) ≤ C ^ 2 * (μ Set.univ).toReal := by exact @_root_.P2MW.S_MeasureTheory_Lp_finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm.solution X _ μ _ 𝕜 _ V C hV
