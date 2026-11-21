import Tengoku.Seed.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_mixedEmbedding_trace_mixedEmbedding

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_mixedEmbedding_trace_mixedEmbedding.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open NumberField NumberField.mixedEmbedding
open scoped Classical
/--
@isnad1 id=eq.0h2v.s10.72301e1a6f98 from=translated src=- shape=f225a747 vocab=70edd9bb
-/
theorem NumberField.mixedEmbedding.trace_mixedEmbedding
    (K : Type*) [Field K] [NumberField K] (x : K) :
    Algebra.trace ℝ (mixedSpace K) (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by exact @_root_.P2MW.S_NumberField_mixedEmbedding_trace_mixedEmbedding.solution K _ _ x
