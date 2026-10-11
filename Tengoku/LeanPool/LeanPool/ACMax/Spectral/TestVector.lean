/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.ACMax.Spectral.AlgConn
public import Tengoku.LeanPool.LeanPool.ACMax.Spectral.RayleighUpper

/-!
# Universal test-vector interface

`algConn_le_two_of_testvector`: any nonzero vector `x` orthogonal to the all-ones
vector whose Laplacian quadratic form is at most `2 ‖x‖²` certifies `algConn G ≤ 2`.

This is the direct corollary of the Courant–Fischer bridge `algConn_mul_sq_le` that
every concrete upper-bound certificate in the `Cuts/` chapter factors through: the
balanced, weighted and signed cuts, the induced-`2K₂` bound and the good-`C₄`/`K_{2,3}`
certificates all build an explicit `x ⊥ 𝟙` and discharge the Rayleigh inequality here.
-/

@[expose] public section

namespace ACMax

open Matrix

end ACMax
