/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Tengoku

/-!
# Shared Trigonometric Identities

Exact values of `cos` and `sin` at `2π/3`.
-/

open Complex

/--
@isnad1 id=eq.0h0v.s5.a74525230631 from=translated src=- shape=4a6433fb vocab=7cca8a66
-/
theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  ring

/--
@isnad1 id=eq.0h0v.s5.121fde849775 from=translated src=- shape=44273b4f vocab=1eba1935
-/
theorem sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.sin_pi_sub]
  exact Real.sin_pi_div_three
