/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Tnlean.TNLean.Algebra.FinCyclicInduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Path sums for ordered products of matrices

This file expands an ordered product of finitely many square matrices as a sum
over index paths: the matrix-vector product of the ordered product is the sum
over paths starting at the row index (`ofFn_prod_mulVec_apply`), and the trace
of the ordered product of a nonempty family is the sum over cyclic paths, in
which each factor connects a site to its cyclic successor
(`trace_ofFn_prod_eq_sum_cyclic`).  The cyclic form is the transfer-matrix
identity behind closed-chain contractions of matrix product operators.
-/

open scoped BigOperators

namespace Matrix

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

/-- Summing over the tuples of length `L + 1` is summing over the first entry
and then over the remaining tuple.
@isnad1 id=eq.0h4v.s7.1d7a93c0241d from=translated src=- shape=5dfad4c2 vocab=ea5e76be
-/
lemma sum_fin_cons {L : ℕ} (F : (Fin (L + 1) → ι) → R) :
    ∑ t, F t = ∑ c, ∑ t : Fin L → ι, F (Fin.cons c t) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => ι) (fun x => F (Fin.cons x.1 x.2)) F
    (fun _ => rfl), Fintype.sum_prod_type]

-- `Matrix`'s identity, and hence `List.prod` including the empty product,
-- requires decidable equality.
variable [DecidableEq ι]

/-- **Open path expansion.**  Applying the ordered product of the matrices
`M 0, …, M (L - 1)` to a vector `v` and reading the entry at `a` sums, over all
paths `t` of length `L` starting at `a`, the product of the matrix entries along
the path times `v` at the endpoint.
@isnad1 id=eq.0h6v.s7.e5169e311980 from=translated src=- shape=5d1fc950 vocab=a9ed7f14
-/
theorem ofFn_prod_mulVec_apply :
    ∀ (L : ℕ) (M : Fin L → Matrix ι ι R) (v : ι → R) (a : ι),
      (List.ofFn M).prod.mulVec v a =
        ∑ t : Fin L → ι,
          (∏ i : Fin L, M i ((Fin.cons a t : Fin (L + 1) → ι) i.castSucc)
            ((Fin.cons a t : Fin (L + 1) → ι) i.succ)) *
            v ((Fin.cons a t : Fin (L + 1) → ι) (Fin.last L))
  | 0, M, v, a => by
      simp [List.ofFn_zero]
  | L + 1, M, v, a => by
      rw [List.ofFn_succ, List.prod_cons, ← Matrix.mulVec_mulVec]
      change (∑ c, M 0 a c * (List.ofFn fun i => M i.succ).prod.mulVec v c) = _
      rw [sum_fin_cons]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [ofFn_prod_mulVec_apply L, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Fin.prod_univ_succ, ← Fin.succ_last]
      simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]
      ring

/-- **Cyclic path expansion.**  The trace of the ordered product of a nonempty
family of matrices is the sum, over all assignments of an index to each site of
the cycle, of the product of the entries connecting each site to its cyclic
successor.
@isnad1 id=eq.0h4v.s8.e24a715d1712 from=translated src=- shape=8a07ec59 vocab=598f8a06
-/
theorem trace_ofFn_prod_eq_sum_cyclic (L : ℕ) (M : Fin (L + 1) → Matrix ι ι R) :
    (List.ofFn M).prod.trace =
      ∑ t : Fin (L + 1) → ι, ∏ n, M n (t n) (t (finRotate (L + 1) n)) := by
  rw [List.ofFn_succ', List.prod_concat, Matrix.trace, sum_fin_cons]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := ofFn_prod_mulVec_apply L (fun i => M i.castSucc) (fun c => M (Fin.last L) c a) a
  change (∑ c, _ * _) = _ at h
  rw [Matrix.diag_apply, Matrix.mul_apply, h]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.finRotate_succ_castSucc, finRotate_last, Fin.cons_zero]

end Matrix
