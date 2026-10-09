/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Complex.Basic
public import Tengoku.Seed.Analysis.Normed.Operator.NormedSpace
public import Tengoku.Seed.LinearAlgebra.Complex.Determinant

/-! # The basic continuous linear maps associated to `ℂ`

The continuous linear maps `Complex.reCLM` (real part), `Complex.imCLM` (imaginary part),
`Complex.conjCLE` (conjugation), and `Complex.ofRealCLM` (inclusion of `ℝ`) were introduced in
`Analysis.Complex.Basic`. This file contains a few calculations requiring more imports:
the operator norm and (for `Complex.conjCLE`) the determinant.
-/

public section

open ContinuousLinearMap

namespace Complex

/-- The determinant of `conjLIE`, as a linear map.
@isnad1 id=eq.0h0v.s10.bbb237f529f2 from=seed src=0 shape=f46a8b8c vocab=734f8afb
-/
@[simp]
theorem det_conjLIE : LinearMap.det (conjLIE.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = -1 :=
  det_conjAe

/-- The determinant of `conjLIE`, as a linear equiv.
@isnad1 id=eq.0h0v.s10.79dcb501daf1 from=seed src=0 shape=3163414c vocab=a5cabed6
-/
@[simp]
theorem linearEquiv_det_conjLIE : LinearEquiv.det conjLIE.toLinearEquiv = -1 :=
  linearEquiv_det_conjAe

/--
@isnad1 id=eq.0h0v.s7.f8815def2303 from=seed src=0 shape=1acad81b vocab=a5fadfde
-/
@[simp]
theorem reCLM_norm : ‖reCLM‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖reCLM 1‖ := by simp
      _ ≤ ‖reCLM‖ := unit_le_opNorm _ _ (by simp)

/--
@isnad1 id=eq.0h0v.s9.faa0df216459 from=seed src=0 shape=486bc665 vocab=abf49219
-/
@[simp]
theorem reCLM_enorm : ‖reCLM‖ₑ = 1 := by simp [← ofReal_norm]

/--
@isnad1 id=eq.0h0v.s8.d8a67451e52f from=seed src=0 shape=486bc665 vocab=7dd4d755
-/
@[simp]
theorem reCLM_nnnorm : ‖reCLM‖₊ = 1 :=
  Subtype.ext reCLM_norm

/--
@isnad1 id=eq.0h0v.s7.4aed8719e165 from=seed src=0 shape=1acad81b vocab=1d43a097
-/
@[simp]
theorem imCLM_norm : ‖imCLM‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖imCLM I‖ := by simp
      _ ≤ ‖imCLM‖ := unit_le_opNorm _ _ (by simp)

/--
@isnad1 id=eq.0h0v.s9.9ced0d4fc806 from=seed src=0 shape=486bc665 vocab=627ae9bd
-/
@[simp]
theorem imCLM_enorm : ‖imCLM‖ₑ = 1 := by simp [← ofReal_norm]

/--
@isnad1 id=eq.0h0v.s8.901acb35dae2 from=seed src=0 shape=486bc665 vocab=840aa672
-/
@[simp]
theorem imCLM_nnnorm : ‖imCLM‖₊ = 1 :=
  Subtype.ext imCLM_norm

/--
@isnad1 id=eq.0h0v.s8.951e64e54859 from=seed src=0 shape=4b040ba8 vocab=444b085f
-/
@[simp]
theorem conjCLE_norm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖ = 1 :=
  conjLIE.toLinearIsometry.norm_toContinuousLinearMap

/--
@isnad1 id=eq.0h0v.s10.227fd6a2b9bc from=seed src=0 shape=45f84a29 vocab=1d0e5cba
-/
@[simp]
theorem conjCLE_enorm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖ₑ = 1 := by simp [← ofReal_norm]

/--
@isnad1 id=eq.0h0v.s8.49cc3d4e6f92 from=seed src=0 shape=45f84a29 vocab=cefb55b5
-/
@[simp]
theorem conjCLE_nnorm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖₊ = 1 :=
  Subtype.ext conjCLE_norm

/--
@isnad1 id=eq.0h0v.s7.9c06f1beeaf5 from=seed src=0 shape=ed3d5df8 vocab=652b34fc
-/
@[simp]
theorem ofRealCLM_norm : ‖ofRealCLM‖ = 1 :=
  ofRealLI.norm_toContinuousLinearMap

/--
@isnad1 id=eq.0h0v.s9.c99301c3af12 from=seed src=0 shape=144a2c8e vocab=e3f0cb65
-/
@[simp]
theorem ofRealCLM_enorm : ‖ofRealCLM‖ₑ = 1 := by simp [← ofReal_norm]

/--
@isnad1 id=eq.0h0v.s8.cc711396854d from=seed src=0 shape=144a2c8e vocab=b9ccd0e5
-/
@[simp]
theorem ofRealCLM_nnnorm : ‖ofRealCLM‖₊ = 1 :=
  Subtype.ext <| ofRealCLM_norm

end Complex
