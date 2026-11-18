import Tengoku.Seed.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Tengoku.Seed.RingTheory.Complex
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_mixedEmbedding_trace_mixedSpace_apply

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_mixedEmbedding_trace_mixedSpace_apply.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding

open scoped Classical in

/--
@isnad1 id=eq.0h2v.s10.a48e9bcc5ee9 from=translated src=- shape=32bf3953 vocab=2f0b12f1
-/
theorem NumberField.mixedEmbedding.trace_mixedSpace_apply
    (K : Type) [Field K] [NumberField K] (z : mixedSpace K) :
    Algebra.trace ℝ (mixedSpace K) z =
      (∑ w : {w : InfinitePlace K // w.IsReal}, z.1 w) +
        ∑ w : {w : InfinitePlace K // w.IsComplex}, 2 * (z.2 w).re := by exact @_root_.P2MW.S_NumberField_mixedEmbedding_trace_mixedSpace_apply.solution K _ _ z
