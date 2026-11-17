import Tengoku.Seed.Topology.LocallyConstant.Basic
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Set
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_isLocallyConstant_integral_subgroup_mul_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K₀ : Subgroup G) (hK₀ : IsCompact (K₀ : Set G)) (hK₀' : IsOpen (K₀ : Set G))
    (T : Subgroup G) (hT : IsClosed (T : Set G)) (hcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure]
    (Ω : Set G) (hΩ : IsCompact Ω) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ IsLocallyConstant w ∧ HasCompactSupport w ∧
      ∀ x : G, (∃ t ∈ T, ∃ d ∈ Ω, x = t * d) → ∫ t : T, w (t * x) ∂τ = 1 := by exact @_root_.P2MW.S_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one.solution G _ _ _ K₀ hK₀ hK₀' T hT hcomm _ _ τ _ Ω hΩ
