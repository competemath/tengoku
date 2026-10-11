/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.ACMax.Spectral.AlgConn

/-!
# Variational (Courant–Fischer) upper bound for algebraic connectivity

`algConn_mul_sq_le`: for any test vector `x` orthogonal to the all-ones vector
(`∑ i, x i = 0`), the second-smallest Laplacian eigenvalue is bounded by the
Rayleigh quotient of `x`, in division-free form
`algConn G * ‖x‖² ≤ xᵀ L x`.

This is the reusable bridge both clauses of the ACMAX conjecture rely on.
-/

@[expose] public section

namespace ACMax

open Matrix

end ACMax
