/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku

/-!
 # Extra lemmas on RCLike

 This file contains extra lemmas on `RCLike`.
-/

@[expose] public section

namespace RCLike

variable {𝕜 : Type _} [RCLike 𝕜]

open scoped ComplexOrder

alias le_def := le_iff_re_im
alias lt_def := lt_iff_re_im
alias nonneg_def := nonneg_iff
alias pos_def := pos_iff
alias nonpos_def := nonpos_iff
alias neg_def := neg_iff

theorem nonneg_def' {x : 𝕜} : 0 ≤ x ↔ (re x : 𝕜) = x ∧ 0 ≤ re x := by
  rw [nonneg_def, ← conj_eq_iff_re, conj_eq_iff_im, and_comm]

theorem real_le_real {x y : ℝ} : (x : 𝕜) ≤ (y : 𝕜) ↔ x ≤ y := by
  rw [le_def]; simp_rw [ofReal_re, ofReal_im, and_true]

theorem real_lt_real {x y : ℝ} : (x : 𝕜) < (y : 𝕜) ↔ x < y := by simp [@lt_def 𝕜]

theorem zero_le_real {x : ℝ} : 0 ≤ (x : 𝕜) ↔ 0 ≤ x := by
  simp_rw [@nonneg_def 𝕜, ofReal_im, and_true, ofReal_re]

theorem zero_lt_real {x : ℝ} : 0 < (x : 𝕜) ↔ 0 < x := by
  simp_rw [@pos_def 𝕜, ofReal_im, and_true, ofReal_re]

end RCLike
