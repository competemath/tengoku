/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Seed.LinearAlgebra.Vandermonde

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR Vandermonde matrix

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.1.

For `x_1, …, x_r` in a commutative ring `R` (BPR works over a field, but
the definition makes sense in any `CommRing`), the **Vandermonde matrix**
`V(x_1, …, x_r)` is the `r × r` matrix with entry `x_{j+1}^i` in row `i`
and column `j` (0-indexed: `i, j ∈ {0, …, r-1}`). The **Vandermonde
determinant** is its determinant.

This is the transpose of Mathlib's `Matrix.vandermonde`, which uses
`v i ^ j` (element-by-row). Since `det M = det Mᵀ`, the two
determinants agree.
-/
namespace Tengoku.Azurite end Tengoku.Azurite open Tengoku.Azurite
namespace Azurite.BPR.Chapter4

open Matrix

variable {R : Type*} [CommRing R]

/-- **BPR Vandermonde matrix** (unnumbered definition, §4.1). The
    `r × r` matrix with entry `x_j ^ i` in row `i`, column `j`
    (0-indexed). In BPR's notation this is `V(x_1, …, x_r)` with
    `x_{j+1}^i` at row `i`, column `j` (1-indexing the elements).-/
def vandermondeMat {r : ℕ} (x : Fin r → R) : Matrix (Fin r) (Fin r) R :=
  Matrix.of fun i j => x j ^ i.val

/-- The Vandermonde matrix in BPR's convention equals the transpose of
    Mathlib's `Matrix.vandermonde`.
@isnad1 id=eq.0h3v.s5.27987d2c948f from=translated src=- shape=7f03adac vocab=96bb427f
-/
lemma vandermondeMat_eq_transpose {r : ℕ} (x : Fin r → R) :
    vandermondeMat x = (Matrix.vandermonde x).transpose := by
  ext i j
  simp [vandermondeMat, Matrix.vandermonde_apply, Matrix.transpose_apply]

/-- **BPR Vandermonde determinant** (unnumbered definition, §4.1). The
    determinant of `vandermondeMat x`.-/
def vandermondeDet {r : ℕ} (x : Fin r → R) : R :=
  (vandermondeMat x).det

/-- The Vandermonde determinant in BPR's convention equals Mathlib's.
@isnad1 id=eq.0h3v.s5.63bce72ec9c2 from=translated src=- shape=7f771a29 vocab=ae244f5f
-/
lemma vandermondeDet_eq_mathlib {r : ℕ} (x : Fin r → R) :
    vandermondeDet x = (Matrix.vandermonde x).det := by
  rw [vandermondeDet, vandermondeMat_eq_transpose, Matrix.det_transpose]

end Azurite.BPR.Chapter4
-- Tengoku: root names of this library moved to Tengoku.Azurite so they do not collide with other libraries (generated)
