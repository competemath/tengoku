/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/LT.lean — elementary facts about the parameter L_T := ½ l(T) + iπ/4  (Defs.LT),
collected in a single home for use by Coeff.lean and Coeff/Reexpansion.lean.  Canonical names are unprimed.
-/
import Tengoku.FormalMath.Zeta23.XiPrime.Defs

noncomputable section

namespace Zeta23
namespace XiPrime

/--
@isnad1 id=eq.0h1v.s4.73e8e37ec152 from=translated src=- shape=827237b9 vocab=02e7e9e8
-/
lemma re_LT (T : ℝ) : (LT T).re = l T / 2 := by simp [LT]

/--
@isnad1 id=eq.0h1v.s4.a428fee3a78f from=translated src=- shape=bd0ca07d vocab=9eade3e0
-/
lemma im_LT (T : ℝ) : (LT T).im = Real.pi / 4 := by simp [LT]

/--
@isnad1 id=le.0h1v.s4.571e28f4299a from=translated src=- shape=8d54dde6 vocab=4f31837d
-/
lemma abs_im_LT_le (T : ℝ) : |(LT T).im| ≤ 1 := by
  rw [im_LT, abs_of_nonneg (by positivity)]
  linarith [Real.pi_le_four]

/--
@isnad1 id=le.0h1v.s4.3174f19093c5 from=translated src=- shape=4b70b14a vocab=d00248ef
-/
lemma norm_LT_ge (T : ℝ) : l T / 2 ≤ ‖LT T‖ := by
  calc l T / 2 ≤ |(LT T).re| := by rw [re_LT]; exact le_abs_self _
    _ ≤ ‖LT T‖ := Complex.abs_re_le_norm _

/--
@isnad1 id=ne.1h1v.s4.1cba3b524eb4 from=translated src=- shape=8990e82f vocab=6eb226c1
-/
lemma LT_ne_zero {T : ℝ} (hl : 0 < l T) : LT T ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [re_LT, Complex.zero_re] at this
  linarith

/--
@isnad1 id=ne.2h2v.s5.855b9b7c05e6 from=translated src=- shape=02931d73 vocab=bf9ea2da
-/
lemma LT_add_ne_zero {T δ : ℝ} (hl : 0 < l T) (hδ : 0 ≤ δ) : LT T + (δ : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [Complex.add_re, re_LT, Complex.ofReal_re, Complex.zero_re] at this
  linarith

end XiPrime
end Zeta23
