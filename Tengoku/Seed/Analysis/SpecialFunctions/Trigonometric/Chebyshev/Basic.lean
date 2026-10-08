/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Complex.Trigonometric
public import Tengoku.Seed.LinearAlgebra.Complex.Module
public import Tengoku.Seed.RingTheory.Polynomial.Chebyshev

/-!
# Multiple angle formulas in terms of Chebyshev polynomials

This file gives the trigonometric characterizations of Chebyshev polynomials, for the real
(`Real.cos`) and complex (`Complex.cos`) cosine and the real (`Real.cosh`) and complex
(`Complex.cosh`) hyperbolic cosine.
-/

public section


namespace Polynomial.Chebyshev

open Polynomial

/--
@isnad1 id=eq.0h2v.s5.c8964a2437fb from=seed src=0 shape=0904b1ed vocab=ec74fc43
-/
@[simp, norm_cast]
theorem complex_ofReal_eval_T : ∀ (x : ℝ) n, (((T ℝ n).eval x : ℝ) : ℂ) = (T ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_T ℝ ℂ _ _ _

/--
@isnad1 id=eq.0h2v.s5.2cb2b1376e7b from=seed src=0 shape=0904b1ed vocab=260f3f93
-/
@[simp, norm_cast]
theorem complex_ofReal_eval_U : ∀ (x : ℝ) n, (((U ℝ n).eval x : ℝ) : ℂ) = (U ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_U ℝ ℂ _ _ _

/--
@isnad1 id=eq.0h2v.s5.f7147f6c42af from=seed src=0 shape=0904b1ed vocab=0fbb26a3
-/
@[simp, norm_cast]
theorem complex_ofReal_eval_C : ∀ (x : ℝ) n, (((C ℝ n).eval x : ℝ) : ℂ) = (C ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_C ℝ ℂ _ _ _

/--
@isnad1 id=eq.0h2v.s5.b735a98fcac7 from=seed src=0 shape=0904b1ed vocab=e510a6b0
-/
@[simp, norm_cast]
theorem complex_ofReal_eval_S : ∀ (x : ℝ) n, (((S ℝ n).eval x : ℝ) : ℂ) = (S ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_S ℝ ℂ _ _ _

/-! ### Complex versions -/

section Complex

open Complex

variable (θ : ℂ)

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`.
@isnad1 id=eq.0h2v.s5.a054f1636cb6 from=seed src=0 shape=6e9f132a vocab=47e87ff2
-/
@[simp]
theorem T_complex_cos (n : ℤ) : (T ℂ n).eval (cos θ) = cos (n * θ) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp only [T_add_two, eval_sub, eval_mul, eval_X, eval_ofNat, ih1, ih2, sub_eq_iff_eq_add,
      cos_add_cos]
    push_cast
    ring_nf
  | neg_add_one n ih1 ih2 =>
    simp only [T_sub_one, eval_sub, eval_mul, eval_X, eval_ofNat, ih1, ih2, sub_eq_iff_eq_add',
      cos_add_cos]
    push_cast
    ring_nf

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`.
@isnad1 id=eq.0h2v.s5.8bf9e991b00b from=seed src=0 shape=ba7d15b5 vocab=ff54b15a
-/
@[simp]
theorem U_complex_cos (n : ℤ) : (U ℂ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp [one_add_one_eq_two, sin_two_mul]; ring
  | add_two n ih1 ih2 =>
    simp only [U_add_two, eval_sub, eval_mul, eval_X, eval_ofNat, sub_mul,
      mul_assoc, ih1, ih2, sub_eq_iff_eq_add, sin_add_sin]
    push_cast
    ring_nf
  | neg_add_one n ih1 ih2 =>
    simp only [U_sub_one, eval_sub, eval_mul, eval_X, eval_ofNat, sub_mul,
      mul_assoc, ih1, ih2, sub_eq_iff_eq_add', sin_add_sin]
    push_cast
    ring_nf

/-- The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomial) evaluates on
`2 * cos θ` to the value `2 * cos (n * θ)`.
@isnad1 id=eq.0h2v.s5.1fd5b7ef2fd5 from=seed src=0 shape=8228b176 vocab=351b1044
-/
@[simp]
theorem C_two_mul_complex_cos (n : ℤ) : (C ℂ n).eval (2 * cos θ) = 2 * cos (n * θ) := by
  simp [C_eq_two_mul_T_comp_half_mul_X]

/-- The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci polynomial)
evaluates on `2 * cos θ` to the value `sin ((n + 1) * θ) / sin θ`.
@isnad1 id=eq.0h2v.s6.198413f4d283 from=seed src=0 shape=234130b4 vocab=4d6b64f1
-/
@[simp]
theorem S_two_mul_complex_cos (n : ℤ) : (S ℂ n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ) := by
  simp [S_eq_U_comp_half_mul_X]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cosh θ` to the
value `cosh (n * θ)`.
@isnad1 id=eq.0h2v.s5.6701713b2c51 from=seed src=0 shape=6e9f132a vocab=09e57dd8
-/
@[simp]
theorem T_complex_cosh (n : ℤ) : (T ℂ n).eval (cosh θ) = cosh (n * θ) := calc
  (T ℂ n).eval (cosh θ)
  _ = (T ℂ n).eval (cos (θ * I))        := by rw [cos_mul_I]
  _ = cos (n * (θ * I))                 := T_complex_cos (θ * I) n
  _ = cos (n * θ * I)                   := by rw [mul_assoc]
  _ = cosh (n * θ)                      := cos_mul_I (n * θ)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cosh θ` to the
value `sinh ((n + 1) * θ) / sinh θ`.
@isnad1 id=eq.0h2v.s5.3c65e23fd5b0 from=seed src=0 shape=ba7d15b5 vocab=b328fc87
-/
@[simp]
theorem U_complex_cosh (n : ℤ) : (U ℂ n).eval (cosh θ) * sinh θ = sinh ((n + 1) * θ) := calc
  (U ℂ n).eval (cosh θ) * sinh θ
  _ = (U ℂ n).eval (cos (θ * I)) * sin (θ * I) * (-I)   := by simp [cos_mul_I, sin_mul_I, mul_assoc]
  _ = sin ((n + 1) * (θ * I)) * (-I)                    := by rw [U_complex_cos]
  _ = sin ((n + 1) * θ * I) * (-I)                      := by rw [mul_assoc]
  _ = sinh ((n + 1) * θ)                                := by
    rw [sin_mul_I ((n + 1) * θ), mul_assoc, mul_neg, I_mul_I, neg_neg, mul_one]

/-- The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomial) evaluates on
`2 * cosh θ` to the value `2 * cosh (n * θ)`.
@isnad1 id=eq.0h2v.s5.4104d55ab1ef from=seed src=0 shape=8228b176 vocab=e1aa5ee3
-/
@[simp]
theorem C_two_mul_complex_cosh (n : ℤ) : (C ℂ n).eval (2 * cosh θ) = 2 * cosh (n * θ) := by
  simp [C_eq_two_mul_T_comp_half_mul_X]

/-- The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci polynomial)
evaluates on `2 * cosh θ` to the value `sinh ((n + 1) * θ) / sinh θ`.
@isnad1 id=eq.0h2v.s6.b42152bd12ad from=seed src=0 shape=234130b4 vocab=84218ee0
-/
@[simp]
theorem S_two_mul_complex_cosh (n : ℤ) : (S ℂ n).eval (2 * cosh θ) * sinh θ =
    sinh ((n + 1) * θ) := by
  simp [S_eq_U_comp_half_mul_X]

end Complex

/-! ### Real versions -/

section Real

open Real

variable (θ : ℝ) (n : ℤ)

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`.
@isnad1 id=eq.0h2v.s5.ea888c9496ff from=seed src=0 shape=6e9f132a vocab=2b10d99d
-/
@[simp]
theorem T_real_cos : (T ℝ n).eval (cos θ) = cos (n * θ) := mod_cast T_complex_cos θ n

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`.
@isnad1 id=eq.0h2v.s5.e5fee5236fc2 from=seed src=0 shape=ba7d15b5 vocab=764c6189
-/
@[simp]
theorem U_real_cos : (U ℝ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) :=
  mod_cast U_complex_cos θ n

/-- The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomial) evaluates on
`2 * cos θ` to the value `2 * cos (n * θ)`.
@isnad1 id=eq.0h2v.s5.f5172a0c37df from=seed src=0 shape=8228b176 vocab=2d218e85
-/
@[simp]
theorem C_two_mul_real_cos : (C ℝ n).eval (2 * cos θ) = 2 * cos (n * θ) :=
  mod_cast C_two_mul_complex_cos θ n

/-- The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci polynomial)
evaluates on `2 * cos θ` to the value `sin ((n + 1) * θ) / sin θ`.
@isnad1 id=eq.0h2v.s6.87adf6849d8d from=seed src=0 shape=234130b4 vocab=6913e60c
-/
@[simp]
theorem S_two_mul_real_cos : (S ℝ n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ) :=
  mod_cast S_two_mul_complex_cos θ n

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cosh θ` to the
value `cosh (n * θ)`.
@isnad1 id=eq.0h2v.s5.fa6caa67a2ec from=seed src=0 shape=6e9f132a vocab=fcd4f499
-/
@[simp]
theorem T_real_cosh (n : ℤ) : (T ℝ n).eval (cosh θ) = cosh (n * θ) := mod_cast T_complex_cosh θ n

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cosh θ` to the
value `sinh ((n + 1) * θ) / sinh θ`.
@isnad1 id=eq.0h2v.s5.e7f4b6dd327f from=seed src=0 shape=ba7d15b5 vocab=1d3fc833
-/
@[simp]
theorem U_real_cosh (n : ℤ) : (U ℝ n).eval (cosh θ) * sinh θ = sinh ((n + 1) * θ) :=
  mod_cast U_complex_cosh θ n

/-- The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomial) evaluates on
`2 * cosh θ` to the value `2 * cosh (n * θ)`.
@isnad1 id=eq.0h2v.s5.bb36739112f7 from=seed src=0 shape=8228b176 vocab=c09e642d
-/
@[simp]
theorem C_two_mul_real_cosh (n : ℤ) : (C ℝ n).eval (2 * cosh θ) = 2 * cosh (n * θ) :=
  mod_cast C_two_mul_complex_cosh θ n

/-- The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci polynomial)
evaluates on `2 * cosh θ` to the value `sinh ((n + 1) * θ) / sinh θ`.
@isnad1 id=eq.0h2v.s6.728b8dcdc539 from=seed src=0 shape=234130b4 vocab=92d5feab
-/
@[simp]
theorem S_two_mul_real_cosh (n : ℤ) : (S ℝ n).eval (2 * cosh θ) * sinh θ = sinh ((n + 1) * θ) :=
  mod_cast S_two_mul_complex_cosh θ n

end Real

end Polynomial.Chebyshev
