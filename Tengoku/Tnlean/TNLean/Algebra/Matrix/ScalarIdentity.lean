/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Seed.Analysis.Matrix.Order
import Tengoku.Seed.LinearAlgebra.Matrix.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar identity matrices

This file records positivity and trace formulas for scalar multiples of identity matrices.
-/

namespace Matrix

namespace PosSemidef

/-- A nonnegative scalar multiple of the identity matrix is positive semidefinite.
@isnad1 id=possemid.1h4v.s7.c4c8d8a7670c from=translated src=- shape=ba09ed82 vocab=43661077
-/
theorem smul_one {n α R : Type*} [DecidableEq n] [Ring R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [CommSemiring α] [PartialOrder α] [StarRing α] [StarOrderedRing α]
    [Algebra α R] [StarModule α R] [PosSMulMono α R] {a : α} (ha : 0 ≤ a) :
    (a • (1 : Matrix n n R)).PosSemidef :=
  PosSemidef.one.smul ha

end PosSemidef

namespace PosDef

/-- A positive scalar multiple of the identity matrix is positive definite.
@isnad1 id=posdef.1h4v.s8.13114f433f26 from=translated src=- shape=d1eee23e vocab=97cafc7c
-/
theorem smul_one {n α R : Type*} [DecidableEq n] [Ring R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [NoZeroDivisors R] [CommSemiring α] [PartialOrder α] [StarRing α]
    [StarOrderedRing α] [Algebra α R] [StarModule α R] [PosSMulStrictMono α R] {a : α}
    (ha : 0 < a) : (a • (1 : Matrix n n R)).PosDef :=
  PosDef.one.smul ha

end PosDef

/-- The trace of a scalar multiple of the identity is the scalar multiple of the dimension.
@isnad1 id=eq.0h4v.s7.0868269f725a from=translated src=- shape=14b28d79 vocab=6911c05a
-/
theorem trace_smul_one {n α R : Type*} [Fintype n] [DecidableEq n] [AddCommMonoidWithOne R]
    [DistribSMul α R] (a : α) :
    trace (a • (1 : Matrix n n R)) = a • (Fintype.card n : R) := by
  rw [trace_smul, trace_one]

end Matrix
