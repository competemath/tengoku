import Tengoku.Seed.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_mixedEmbedding_trace_mixedEmbedding.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_mixedEmbedding_trace_mixedEmbedding

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding Module
open scoped Classical

/--
@isnad1 id=eq.0h2v.s10.72301e1a6f98 from=translated src=- shape=f225a747 vocab=70edd9bb
-/
theorem solution
    (K : Type*) [Field K] [NumberField K] (x : K) :
    Algebra.trace ℝ (mixedSpace K) (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by
  rw [Algebra.trace_eq_matrix_trace (latticeBasis K) (mixedEmbedding K x),
    Algebra.trace_eq_matrix_trace (integralBasis K) x, Matrix.trace, Matrix.trace, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, latticeBasis_apply, ← map_mul, latticeBasis_repr_apply]
