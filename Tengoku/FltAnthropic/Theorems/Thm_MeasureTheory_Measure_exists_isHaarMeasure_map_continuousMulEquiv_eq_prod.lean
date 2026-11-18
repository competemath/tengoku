import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_Measure_exists_isHaarMeasure_map_continuousMulEquiv_eq_prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_Measure_exists_isHaarMeasure_map_continuousMulEquiv_eq_prod.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u₁ u₂ u₃

/--
@isnad1 id=ex.0h6v.s8.14ff32d2f4a2 from=translated src=- shape=abd891d7 vocab=41727ff5
-/
theorem MeasureTheory.Measure.exists_isHaarMeasure_map_continuousMulEquiv_eq_prod
    {G : Type u₁} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {G₁ : Type u₂} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
      [SigmaCompactSpace G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    {G₂ : Type u₃} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [SigmaCompactSpace G₂]
      [MeasurableSpace G₂] [BorelSpace G₂]
    (μ : Measure G) [μ.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (e : G ≃ₜ* G₁ × G₂) :
    ∃ μ₂ : Measure G₂, μ₂.IsHaarMeasure ∧ (μ.IsMulRightInvariant → μ₂.IsMulRightInvariant) ∧
      μ.map e = μ₁.prod μ₂ := by exact @_root_.P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_map_continuousMulEquiv_eq_prod.solution G _ _ _ _ _ G₁ _ _ _ _ _ _ _ G₂ _ _ _ _ _ _ μ _ μ₁ _ e
