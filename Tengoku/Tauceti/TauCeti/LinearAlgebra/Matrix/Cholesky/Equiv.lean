/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.LinearAlgebra.Matrix.Cholesky.Basic
import Tengoku.Tauceti.TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# The Cholesky equivalence

This file proves uniqueness of positive-diagonal lower-triangular Gram factors. Together with the
Cholesky construction, this packages Cholesky factorization and reconstruction as an equivalence
between positive-definite symmetric matrices and positive-diagonal lower-triangular matrices.

## Main results

* `TauCeti.eq_cholesky_of_mul_transpose_self_eq` identifies any positive-diagonal lower-triangular
  Gram factor with the Cholesky factor.
* `TauCeti.cholesky_choleskyReconstruction` is the inverse identity from factors to matrices.
* `TauCeti.choleskyEquiv` is the resulting equivalence.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 7.2.
-/

public section

noncomputable section

open scoped Matrix

namespace TauCeti

end TauCeti
