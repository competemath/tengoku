import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=and.3h5v.s8.5df4686409d5 from=translated src=- shape=336929ca vocab=617fa596
-/
theorem MeasureTheory.hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) (E : Ω → ℤ) (hE : Measurable E)
    (G : Ω → ℂ) {r : ℝ} (hr : 0 < r)
    (hG : Integrable (fun ω => G ω * (r : ℂ) ^ E ω) ρ) :
    HasSum (fun n : ℤ => (∫ ω in E ⁻¹' {n}, ‖G ω‖ ∂ρ) * r ^ n) (∫ ω, ‖G ω‖ * r ^ E ω ∂ρ) ∧
    (Summable fun n : ℤ => ‖∫ ω in E ⁻¹' {n}, G ω ∂ρ‖ * r ^ n) ∧
    ∀ Y : ℂ, ‖Y‖ = r →
      Integrable (fun ω => G ω * Y ^ E ω) ρ ∧
      HasSum (fun n : ℤ => (∫ ω in E ⁻¹' {n}, G ω ∂ρ) * Y ^ n) (∫ ω, G ω * Y ^ E ω ∂ρ) := by exact @_root_.P2MW.S_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow.solution Ω _ ρ E hE G r hr hG
