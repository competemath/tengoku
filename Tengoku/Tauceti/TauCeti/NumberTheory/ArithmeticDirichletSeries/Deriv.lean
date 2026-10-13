/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup

/-!
# Derivatives of ideal-indexed Dirichlet series

Differentiating an ideal term `idealTerm K f s I = f I / N(I) ^ s` in `s` returns the same term
weighted by `-log N(I)`.  Summing over the nonzero integral ideals, the derivative of the
norm-regrouped `L`-series is therefore, up to a sign, the ideal-indexed Dirichlet series of the
*logarithmic weighting* `TauCeti.IdealArithmeticFunction.logMul` of `f`, the pointwise product of
`f` with `log N(I)`.

This file proves that identity, its iterated form, and the resulting expression of the logarithmic
derivative as a quotient of two ideal-indexed sums.  The norm-regrouped derivative, its iterated
form, and the logarithmic-derivative result assume that `s` lies strictly to the right of
`TauCeti.idealAbscissaOfAbsConv K f`, the abscissa of absolute convergence of the ideal-indexed
series; the logarithmic weight can destroy summability on the boundary line itself, which is why
a point of convergence strictly to the left is what the estimates consume.

Two facts do the work.  Regrouping by absolute norm turns `logMul` into Mathlib's `LSeries.logMul`,
because the weight `log N(I)` is constant on a norm fibre
(`TauCeti.normCoeff_logMul`); and a logarithmic weight leaves the ideal-indexed series summable
strictly to the right of any point of absolute convergence
(`TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`).  Mathlib's `LSeries_hasDerivAt`
then supplies the calculus, and `TauCeti.regroupByNorm` converts its conclusion back to a sum over
ideals.

## Main definitions

* `TauCeti.IdealArithmeticFunction.logMul`: the pointwise product of an ideal arithmetic function
  with `log N(I)`, the ideal-indexed counterpart of Mathlib's `LSeries.logMul`.  Its `m`-fold
  iterate weights by `log N(I) ^ m` (`TauCeti.IdealArithmeticFunction.logMul_iterate_apply`).

## Main results

* `TauCeti.hasDerivAt_idealTerm`: the derivative in `s` of an ideal term is the term itself,
  weighted by `-log N(I)`.
* `TauCeti.normCoeff_logMul`: regrouping by absolute norm carries the ideal-indexed logarithmic
  weight to Mathlib's.
* `TauCeti.summable_idealTerm_logMul_of_re_lt_re`: a logarithmic weight preserves absolute
  convergence strictly to the right.
* `TauCeti.IdealArithmeticFunction.hasDerivAt_LSeries_normCoeff` and
  `TauCeti.IdealArithmeticFunction.deriv_LSeries_normCoeff`: the derivative of the regrouped
  `L`-series is `-∑ I, log N(I) f I N(I) ^ (-s)`, summed over the nonzero integral ideals.
* `TauCeti.IdealArithmeticFunction.iteratedDeriv_LSeries_normCoeff`: the `m`-th derivative, with
  the weight `log N(I) ^ m`.
* `TauCeti.IdealArithmeticFunction.logDeriv_LSeries_normCoeff`: the logarithmic derivative as the
  quotient of the two ideal-indexed sums.
* `TauCeti.IdealArithmeticFunction.differentiableOn_LSeries_normCoeff`: absolute convergence of
  an ideal-indexed series throughout an open set makes its norm-regrouped `L`-series holomorphic
  there.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

public section

namespace TauCeti

open Complex

open scoped nonZeroDivisors NumberField

variable (K : Type*) [Field K] [NumberField K]

/-! ### The logarithmic weighting -/

namespace IdealArithmeticFunction

variable {K}

/-- **The logarithmic weighting of an ideal arithmetic function**: the pointwise product of `f`
with `log N(I)`.

It is the ideal-indexed counterpart of Mathlib's `LSeries.logMul`, and it is the coefficient
system that appears, up to a sign, when the ideal-indexed Dirichlet series of `f` is
differentiated in `s`. -/
noncomputable def logMul (f : IdealArithmeticFunction K) : IdealArithmeticFunction K :=
  fun I ↦ log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) * f I

/-- Evaluation of the logarithmic weighting. -/
@[simp]
theorem logMul_apply (f : IdealArithmeticFunction K) (I : (Ideal (𝓞 K))⁰) :
    f.logMul I = log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) * f I :=
  (rfl)

/-- Evaluation of an iterated logarithmic weighting: the weight is the `m`-th power of
`log N(I)`. -/
@[simp]
theorem logMul_iterate_apply (f : IdealArithmeticFunction K) (m : ℕ) (I : (Ideal (𝓞 K))⁰) :
    logMul^[m] f I = log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ m * f I := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', logMul_apply, ih]
      ring

end IdealArithmeticFunction

open IdealArithmeticFunction

/-- The ideal term of a logarithmic weighting is the original term weighted by `log N(I)`. -/
@[simp]
theorem idealTerm_logMul (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    idealTerm K f.logMul s I =
      log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) * idealTerm K f s I := by
  rw [idealTerm_def, idealTerm_def, logMul_apply, mul_div_assoc]

/-- **Regrouping by absolute norm carries the logarithmic weight to Mathlib's.**  The weight
`log N(I)` depends on the ideal only through its absolute norm, so it is constant on a norm fibre
and factors out of the regrouping. -/
@[simp]
theorem normCoeff_logMul (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f.logMul n = LSeries.logMul (⇑(normCoeff K f)) n := by
  have hf : f.logMul = fun I ↦ f I * log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) :=
    funext fun I ↦ mul_comm _ _
  rw [hf, normCoeff_fun_mul_comp_absNorm K f (fun m : ℕ ↦ log (m : ℂ)) n]
  exact mul_comm _ _

/-- Iterating the previous identity: the `m`-fold logarithmic weight is carried to Mathlib's. -/
@[simp]
theorem normCoeff_logMul_iterate (f : IdealArithmeticFunction K) (m n : ℕ) :
    normCoeff K (logMul^[m] f) n = LSeries.logMul^[m] (⇑(normCoeff K f)) n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', normCoeff_logMul]
      simp only [LSeries.logMul, ih]

namespace IdealArithmeticFunction

/-! ### Differentiating the regrouped `L`-series -/

end IdealArithmeticFunction

end TauCeti
