/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Tengoku

/-!
# LeanPool.SardMoreira.NormedSpace
-/

@[expose] public section

namespace NNReal

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/--
@isnad1 id=eq.0h3v.s6.5c59bdb0c5b1 from=translated src=- shape=36da5b6e vocab=9357f28d
-/
protected theorem norm_smul (a : ℝ≥0) (x : E) : ‖a • x‖ = a * ‖x‖ := by
  simp [NNReal.smul_def, norm_smul]

/--
@isnad1 id=eq.0h3v.s6.a0d6b279d4c0 from=translated src=- shape=aaccb339 vocab=b9b080a8
-/
protected theorem nnnorm_smul (a : ℝ≥0) (x : E) : ‖a • x‖₊ = a * ‖x‖₊ := by
  simp [NNReal.smul_def, nnnorm_smul]

/--
@isnad1 id=eq.0h3v.s7.01df00d7932c from=translated src=- shape=8179c89b vocab=3e3b3bde
-/
protected theorem enorm_smul (a : ℝ≥0) (x : E) : ‖a • x‖ₑ = a * ‖x‖ₑ := by
  simp [enorm_eq_nnnorm, NNReal.nnnorm_smul]

/--
@isnad1 id=eq.0h4v.s7.ccb9d387b2b8 from=translated src=- shape=7c4b21d2 vocab=5b756a03
-/
protected theorem dist_smul (a : ℝ≥0) (x y : E) : dist (a • x) (a • y) = a * dist x y := by
  simp [NNReal.smul_def, dist_smul₀]

/--
@isnad1 id=eq.0h4v.s7.b9042d326431 from=translated src=- shape=a44180f7 vocab=ee909719
-/
protected theorem nndist_smul (a : ℝ≥0) (x y : E) : nndist (a • x) (a • y) = a * nndist x y := by
  simp [NNReal.smul_def, nndist_smul₀]

/--
@isnad1 id=eq.0h4v.s7.b18a4bc11671 from=translated src=- shape=a99d7590 vocab=6c82bf12
-/
protected theorem edist_smul (a : ℝ≥0) (x y : E) : edist (a • x) (a • y) = a * edist x y := by
  simp only [edist_nndist, NNReal.nndist_smul, ENNReal.coe_mul]

end NNReal
