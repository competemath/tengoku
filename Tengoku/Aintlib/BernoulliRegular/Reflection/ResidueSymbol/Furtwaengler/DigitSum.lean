/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Seed.Data.Nat.Digits.Defs
public import Tengoku.Seed.Data.Nat.Digits.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base-`ℓ` digit sum (Layer 1, REF-18c2c4)

The base-`ℓ` digit sum `s_ℓ(a) = Σ digit_i` where `a = Σ digit_i · ℓ^i`.
This is the right-hand side of the **digit-sum Stickelberger congruence**

  `g(χ^a, ψ) ≡ −u_a · π^{s_ℓ(a)} (mod Q^{s_ℓ(a)+1})`

(REF-18c2c4 corrected target). This file collects elementary properties
of `digitSum` used downstream by the Stickelberger congruence and the
Jacobi-sum carry formula.

This is **Layer 1** in the architecture from the AI-reviewer's
recommendation: pure finite-field/integer combinatorics, no cyclotomic
fields. The later Stickelberger congruence files consume these
combinatorial results.

## References

* Conrad, *Jacobi sums and Stickelberger's congruence*.
* Katre, *Stickelberger ideal and Gauss sums* (arXiv math/0303226).
-/

@[expose] public section

namespace BernoulliRegular

namespace Furtwaengler

/-- Base-`ℓ` digit sum of `a`, i.e. `s_ℓ(a) = Σ digit_i` where
`a = Σ digit_i · ℓ^i`. Wraps `Nat.digits ℓ a` summation for legibility.-/
def digitSum (ℓ a : ℕ) : ℕ := (Nat.digits ℓ a).sum

/--
@isnad1 id=eq.0h1v.s4.43f760ce6de1 from=translated src=- shape=1d838610 vocab=c51e5661
-/
@[simp] theorem digitSum_zero (ℓ : ℕ) : digitSum ℓ 0 = 0 := by
  simp [digitSum]

/-- `digitSum ℓ a ≤ a`: the digit sum never exceeds the number itself.
@isnad1 id=le.0h2v.s3.231390df1b4a from=translated src=- shape=bf83e09e vocab=5f2290ca
-/
theorem digitSum_le_self (ℓ a : ℕ) : digitSum ℓ a ≤ a := by
  simp only [digitSum]
  exact Nat.digit_sum_le ℓ a

/-- For `a < ℓ` and `2 ≤ ℓ`, the only digit is `a` itself, so
`digitSum ℓ a = a`.
@isnad1 id=eq.2h2v.s4.ce79577e8bfb from=translated src=- shape=9474e4c0 vocab=2f10ec36
-/
theorem digitSum_eq_self_of_lt {ℓ a : ℕ} (hℓ : 2 ≤ ℓ) (ha : a < ℓ) :
    digitSum ℓ a = a := by
  simp only [digitSum]
  rcases a with _ | a
  · simp
  · rw [Nat.digits_def' hℓ (Nat.succ_pos a)]
    have hlt : a + 1 < ℓ := ha
    rw [Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt]
    simp

end Furtwaengler

end BernoulliRegular
