/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Derivative computations for the Phi function
-/
module

public import Tengoku.LeanPool.LeanPool.KaltonRoberts.Defs
public import Tengoku

/-!
# Derivative computations for the Phi function

First and second derivative computations for the entropy expressions defining
the Phi functions.
-/

@[expose] public section

namespace KaltonRoberts

open Real

/-! ## First derivatives of hEntropy components -/

/-! ## Second derivatives -/

theorem hasDerivAt_binEntropy_deriv (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => Real.log (1 - x) - Real.log x) (-1/(1-x) - 1/x) x := by
  convert
    HasDerivAt.fun_sub
      (HasDerivAt.log (hasDerivAt_id' x |> HasDerivAt.const_sub 1)
        (by linarith : (1 - x) ≠ 0))
      (Real.hasDerivAt_log hx.ne') using 1
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

theorem hasDerivAt_h_entropy_second_deriv (θ x : ℝ) (hx : 0 < x) (hxθ : x < θ) :
    HasDerivAt (fun x => Real.log (θ - x) - Real.log x) (-1/(θ-x) - 1/x) x := by
  convert
    HasDerivAt.fun_sub
      (HasDerivAt.log (hasDerivAt_id' x |> HasDerivAt.const_sub θ)
        (by linarith : (θ - x) ≠ 0))
      (Real.hasDerivAt_log hx.ne') using 1
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/-! ## Derivative of Phi -/

/-
The first derivative of Phi at a point `x` in `(0, θ)` with `θ < 1`.
-/

/-! ## Generic ConvexOn for Phi -/

/-
ConvexOn for Phi on an interval [δ, α], given an explicit hypothesis
that the second-derivative formula `Phi'' r θ x` is nonneg on `[δ, α]`.
-/

end KaltonRoberts
