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

/--
@isnad1 id=iff.0h3v.s8.f167486348a2 from=translated src=- shape=075c13fa vocab=f75763ce
-/
alias le_def := le_iff_re_im
/--
@isnad1 id=iff.0h3v.s8.9ddaad5bbff7 from=translated src=- shape=41ba3319 vocab=cc7740fc
-/
alias lt_def := lt_iff_re_im
/--
@isnad1 id=iff.0h2v.s8.b0b69d974e44 from=translated src=- shape=7d1a83b3 vocab=29bdd725
-/
alias nonneg_def := nonneg_iff
/--
@isnad1 id=iff.0h2v.s8.9bcd98a97040 from=translated src=- shape=7d1a83b3 vocab=cc7740fc
-/
alias pos_def := pos_iff
/--
@isnad1 id=iff.0h2v.s8.06a2ffc15e55 from=translated src=- shape=315c3178 vocab=29bdd725
-/
alias nonpos_def := nonpos_iff
/--
@isnad1 id=iff.0h2v.s8.d352e7f77680 from=translated src=- shape=315c3178 vocab=cc7740fc
-/
alias neg_def := neg_iff

/--
@isnad1 id=iff.0h2v.s8.60683fcdb186 from=translated src=- shape=60ffe68e vocab=0efbf435
-/
theorem nonneg_def' {x : 𝕜} : 0 ≤ x ↔ (re x : 𝕜) = x ∧ 0 ≤ re x := by
  rw [nonneg_def, ← conj_eq_iff_re, conj_eq_iff_im, and_comm]

/--
@isnad1 id=iff.0h3v.s5.dda6006cc007 from=translated src=- shape=5115f309 vocab=37ac2e9f
-/
theorem real_le_real {x y : ℝ} : (x : 𝕜) ≤ (y : 𝕜) ↔ x ≤ y := by
  rw [le_def]; simp_rw [ofReal_re, ofReal_im, and_true]

/--
@isnad1 id=iff.0h3v.s5.c836232034d2 from=translated src=- shape=5115f309 vocab=63171f9a
-/
theorem real_lt_real {x y : ℝ} : (x : 𝕜) < (y : 𝕜) ↔ x < y := by simp [@lt_def 𝕜]

/--
@isnad1 id=iff.0h2v.s5.ef80f6910a1b from=translated src=- shape=381e07ff vocab=37ac2e9f
-/
theorem zero_le_real {x : ℝ} : 0 ≤ (x : 𝕜) ↔ 0 ≤ x := by
  simp_rw [@nonneg_def 𝕜, ofReal_im, and_true, ofReal_re]

/--
@isnad1 id=iff.0h2v.s5.30011e450b39 from=translated src=- shape=381e07ff vocab=63171f9a
-/
theorem zero_lt_real {x : ℝ} : 0 < (x : 𝕜) ↔ 0 < x := by
  simp_rw [@pos_def 𝕜, ofReal_im, and_true, ofReal_re]

end RCLike
