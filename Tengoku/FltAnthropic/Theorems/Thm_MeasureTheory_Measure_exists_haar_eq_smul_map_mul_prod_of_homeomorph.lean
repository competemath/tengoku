import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_Measure_exists_haar_eq_smul_map_mul_prod_of_homeomorph

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_Measure_exists_haar_eq_smul_map_mul_prod_of_homeomorph.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

/--
@isnad1 id=ex.1h7v.s10.81faacb2db0e from=translated src=- shape=e688103f vocab=c47a3659
-/
theorem MeasureTheory.Measure.exists_haar_eq_smul_map_mul_prod_of_homeomorph
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T S : Subgroup G) [MeasurableSpace T] [BorelSpace T] [MeasurableSpace S] [BorelSpace S]
    (e : T × S ≃ₜ G) (he : ∀ p : T × S, e p = (p.1 : G) * (p.2 : G))
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (τ : Measure T) [τ.IsHaarMeasure]
    (ν : Measure S) [IsFiniteMeasureOnCompacts ν] [ν.IsMulRightInvariant] [ν.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • Measure.map e (τ.prod ν) := by exact @_root_.P2MW.S_MeasureTheory_Measure_exists_haar_eq_smul_map_mul_prod_of_homeomorph.solution G _ _ _ _ _ _ _ _ T S _ _ _ _ e he μ _ _ τ _ ν _ _ _
