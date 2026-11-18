import Tengoku.Seed.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Tengoku.Seed.RingTheory.Complex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_mixedEmbedding_trace_mixedSpace_apply.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_mixedEmbedding_trace_mixedSpace_apply

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding

namespace Ws1
namespace K5b2

/--
@isnad1 id=eq.0h3v.s8.9d666fa8fed5 from=translated src=- shape=db681f76 vocab=f80b11d0
-/
theorem trace_pi_self (k : Type*) [Field k] (ι : Type*) [Fintype ι] [DecidableEq ι] (z : ι → k) :
    Algebra.trace k (ι → k) z = ∑ i, z i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun k ι), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_repr, Pi.basisFun_apply, Pi.mul_apply,
    Pi.single_eq_same, mul_one]

end Ws1.K5b2

open scoped Classical in

/--
@isnad1 id=eq.0h2v.s10.a48e9bcc5ee9 from=translated src=- shape=32bf3953 vocab=2f0b12f1
-/
theorem solution
    (K : Type) [Field K] [NumberField K] (z : mixedSpace K) :
    Algebra.trace ℝ (mixedSpace K) z =
      (∑ w : {w : InfinitePlace K // w.IsReal}, z.1 w) +
        ∑ w : {w : InfinitePlace K // w.IsComplex}, 2 * (z.2 w).re := by
  classical
  rw [Algebra.trace_prod_apply, Ws1.K5b2.trace_pi_self]
  congr 1
  rw [← Algebra.trace_trace (S := ℂ), Ws1.K5b2.trace_pi_self, Algebra.trace_complex_apply, Complex.re_sum,
    Finset.mul_sum]
