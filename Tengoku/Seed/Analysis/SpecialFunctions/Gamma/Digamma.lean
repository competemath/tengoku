/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Meromorphic.Complex
public import Tengoku.Seed.NumberTheory.Harmonic.GammaDeriv


/-!
# The digamma function

This file defines the digamma function as the logarithmic derivative of the Gamma function and
proves some basic properties.

## Main definitions

* `Complex.digamma`: The digamma function of a complex variable.

## Main statements

* `Complex.digamma_apply_add_one`: The digamma function satisfies the functional equation
  `digamma (s + 1) = digamma s + s⁻¹`.
* `Complex.meromorphic_digamma`: The digamma function is meromorphic.

## TODO

* Prove Gauss' integral representation of the digamma function.
-/

@[expose] public section

namespace Complex

/-- The digamma function, defined as the logarithmic derivative of the Gamma function. -/
noncomputable def digamma : ℂ → ℂ := logDeriv Gamma

/--
@isnad1 id=eq.0h0v.s4.fe8030b7fc30 from=seed src=0 shape=0cc26a1b vocab=c1a80fa1
-/
theorem digamma_def : digamma = logDeriv Gamma := rfl

/--
@isnad1 id=eq.0h0v.s3.f0293cb5560f from=seed src=0 shape=3c26ae4f vocab=800389d7
-/
@[simp]
theorem digamma_zero : digamma 0 = 0 :=
  logDeriv_eq_zero_of_not_differentiableAt Gamma 0 not_differentiableAt_Gamma_zero

/--
@isnad1 id=eq.0h0v.s3.54dec5da4303 from=seed src=0 shape=6d15d208 vocab=82a92126
-/
theorem digamma_one : digamma 1 = - Real.eulerMascheroniConstant := by
  rw [digamma_def, logDeriv_apply, hasDerivAt_Gamma_one.deriv, Gamma_one, div_one]

/--
@isnad1 id=eq.0h0v.s5.b1c59d596314 from=seed src=0 shape=f88a34da vocab=800dd22c
-/
theorem digamma_one_half : digamma (1 / 2) = - 2 * log 2 - Real.eulerMascheroniConstant := by
  rw [digamma_def, logDeriv_apply, hasDerivAt_Gamma_one_half.deriv, add_comm, Gamma_one_half_eq,
    neg_mul, ← mul_neg, neg_add', Real.sqrt_eq_rpow, ofReal_cpow Real.pi_nonneg]
  simp

/--
@isnad1 id=eq.1h1v.s5.65e1bb335b3c from=seed src=0 shape=38e8beab vocab=f7d1e6b1
-/
theorem digamma_apply_add_one (s : ℂ) (hs : ∀ m : ℕ, s ≠ - m) :
    digamma (s + 1) = digamma s + s⁻¹ := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  rw [digamma_def, logDeriv_apply, logDeriv_apply, deriv_Gamma_add_one s hs0, Gamma_add_one s hs0,
    add_div, div_mul_cancel_right₀ (Gamma_ne_zero hs), mul_div_mul_left _ _ hs0, add_comm]

/--
@isnad1 id=meromorp.0h0v.s4.12b020ead03d from=seed src=0 shape=e3d48bcb vocab=3e675494
-/
@[fun_prop]
theorem meromorphic_digamma : Meromorphic digamma :=
  Meromorphic.Gamma.logDeriv

end Complex
