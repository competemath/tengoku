import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LocalParametrix_exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LocalParametrix_exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Topology

/--
@isnad1 id=ex.9h7v.s10.615b961a8833 from=translated src=- shape=43956ba5 vocab=6a95eabb
-/
theorem LocalParametrix.exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (D : (E → ℂ) → (E → ℂ))
    (hD_add : ∀ F G : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      ContDiff ℝ (⊤ : ℕ∞) G → HasCompactSupport G → D (F + G) = D F + D G)
    (hD_cont : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → Continuous (D F))
    (hD_supp : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport (D F) ⊆ tsupport F)
    (hD_tr : ∀ g : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ∃ h : E → ℂ, Continuous h ∧ tsupport h ⊆ tsupport g ∧
        ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
          ∫ x, D F x * g x ∂μ = ∫ x, F x * h x ∂μ)
    (x₀ : E) (u w : E → ℂ) (hu : Continuous u) (hw : Continuous w)
    (hu' : ContDiffOn ℝ (⊤ : ℕ∞) u {x₀}ᶜ)
    (hid : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      F x₀ = (∫ x, D F x * u x ∂μ) + ∫ x, F x * w x ∂μ)
    (V : Set E) (hV : V ∈ 𝓝 x₀) :
    ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ V ∧ tsupport g₂ ⊆ V ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, D F x * g₁ x ∂μ) + ∫ x, F x * g₂ x ∂μ := by exact @_root_.P2MW.S_LocalParametrix_exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton.solution E _ _ _ _ _ μ _ D hD_add hD_cont hD_supp hD_tr x₀ u w hu hw hu' hid V hV
