/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Analysis.PositiveDefinite.Basic
public import Tengoku.Tauceti.TauCeti.Analysis.PositiveDefinite.Kernel.Shift

/-!
# Differences of bounded positive-definite functions

On an involutive commutative additive monoid `M`, a *bounded* positive-definite function `F`
dominates each of its translates by a self-adjoint element: if `star s = s`, then

`x ↦ F x - F (x + s)`

is again positive definite. This is the function-level form of
`TauCeti.posSemidef_sub_comp_shift`; self-adjointness of `s` is exactly what makes translation by
`s` a symmetric shift of the kernel `(a, b) ↦ F (a + star b)`.

That difference is the negative of Mathlib's forward difference `Δ_[s] F`, so iterating gives that
the alternating iterated differences `(-1) ^ n Δ_[s]^[n] F` are positive definite too, in operator
form and in the explicit binomial form

`x ↦ ∑ k ≤ n, (-1) ^ k (n choose k) F (x + k • s)`.

Positive definiteness is a statement about quadratic forms, not a pointwise sign; the values
themselves are nonnegative at the "norm points" `a + star a`.

Boundedness is only ever assumed at the "norm points" `a + star a`, the diagonal of the kernel:
Cauchy--Schwarz propagates a bound there to every point of the form `p + star q`. It is essential
and is not a technical artefact: `t ↦ exp t` is positive definite on the involutive monoid
`(ℝ≥0, +)` with the trivial involution, and it *increases*. The statement is
proved by a purely numerical moment-problem estimate on the finite quadratic forms; no topology,
measurability, or representing measure is assumed or produced here.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C: it is the closure property
of the generic `IsPositiveDefinite` predicate that the Berg--Christensen--Ressel representation
(Milestone 2) runs on. The zero-spatial time axis `t ↦ F (t, 0)` of a bounded positive-definite
function on `ℝ≥0 × V` is such a function, for the trivial involution on `ℝ≥0`, and
`TauCeti/Analysis/PositiveDefinite/SemigroupGroup/Time/Difference.lean` reads its complete
monotonicity off the results below. The two-variable statements on `ℝ≥0 × V` itself are *not*
instances of them — the involutive-monoid wrapper carrying the Berg--Christensen--Ressel involution
is private to `TauCeti/Analysis/PositiveDefinite/SemigroupGroup/Basic.lean` — and are proved there
from the Kolmogorov decomposition of the Berg--Christensen--Ressel kernel; only the
forward-difference bookkeeping below is shared.

## Main declarations

* `TauCeti.neg_one_pow_mul_fwdDiff_iter_succ`: one differencing step advances the alternating
  iterated forward difference by one.
* `TauCeti.neg_one_pow_mul_fwdDiff_iter_eq_alternating_sum`: the binomial expansion of the
  alternating iterated forward difference.
* `TauCeti.IsPositiveDefinite.norm_apply_add_star_le`: a bound at the "norm points" `a + star a`
  bounds a positive-definite function at every point `p + star q`.
* `TauCeti.IsPositiveDefinite.sub_shift`: the difference of a bounded positive-definite function
  and its translate by a self-adjoint element is positive definite.
* `TauCeti.IsPositiveDefinite.neg_one_pow_mul_fwdDiff_iter` and
  `TauCeti.IsPositiveDefinite.alternating_sum`: the alternating iterated differences are positive
  definite, in forward-difference and in binomial form.
* `TauCeti.IsPositiveDefinite.sub_shift_add_star_self_nonneg`,
  `TauCeti.IsPositiveDefinite.neg_one_pow_mul_fwdDiff_iter_add_star_self_nonneg` and
  `TauCeti.IsPositiveDefinite.alternating_sum_add_star_self_nonneg`: the resulting nonnegativity at
  the "norm points" `a + star a`.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open scoped ComplexOrder fwdDiff

namespace TauCeti

/-! ## Forward-difference bookkeeping

Pure identities about Mathlib's forward difference operator; no positive definiteness is involved.
-/

section FwdDiff

variable {M : Type*} [AddCommMonoid M]

end FwdDiff

/-! ## Differences of bounded positive-definite functions -/

namespace IsPositiveDefinite

variable {M : Type*} [AddCommMonoid M] [StarAddMonoid M] {F : M → ℂ} {C : ℝ} {s : M}

/-- A positive-definite function bounded at the "norm points" `a + star a` is bounded at every
point of the form `p + star q`, by Cauchy--Schwarz for its kernel. -/
theorem norm_apply_add_star_le (hF : IsPositiveDefinite F)
    (hbdd : ∀ a, ‖F (a + star a)‖ ≤ C) (p q : M) : ‖F (p + star q)‖ ≤ C :=
  hF.posSemidef.norm_le_of_norm_apply_self_le hbdd p q

/-- **A bounded positive-definite function dominates its translate by a self-adjoint element.**
Translation by `s` with `star s = s` is a symmetric shift of the kernel `(a, b) ↦ F (a + star b)`,
so the bounded-kernel estimate `TauCeti.posSemidef_sub_comp_shift` applies; only the diagonal of
that kernel, the values at the "norm points" `a + star a`, has to be bounded. Boundedness cannot be
dropped: `t ↦ exp t` is positive definite on `ℝ≥0` with the trivial involution and increases. -/
theorem sub_shift (hF : IsPositiveDefinite F) (hbdd : ∀ a, ‖F (a + star a)‖ ≤ C)
    (hs : star s = s) : IsPositiveDefinite fun x => F x - F (x + s) := by
  have hkey := posSemidef_sub_comp_shift (K := fun a b : M => F (a + star b))
    (σ := fun a : M => a + s) hF.posSemidef (fun p q => ?_) (fun p => hbdd p)
  · refine IsPositiveDefinite.of_posSemidef ?_
    have heq : (fun a b : M => F (a + star b) - F (a + s + star b)) =
        fun a b : M => F (a + star b) - F (a + star b + s) := by
      funext a b
      rw [add_right_comm]
    rw [heq] at hkey
    exact hkey
  · rw [star_add, hs, add_assoc, add_comm s (star q)]

/-- The difference of a bounded positive-definite function and its translate by a self-adjoint
element is nonnegative at every "norm point" `a + star a`. -/
theorem sub_shift_add_star_self_nonneg (hF : IsPositiveDefinite F)
    (hbdd : ∀ a, ‖F (a + star a)‖ ≤ C) (hs : star s = s) (a : M) :
    0 ≤ F (a + star a) - F (a + star a + s) :=
  (hF.sub_shift hbdd hs).add_star_self_nonneg a

end IsPositiveDefinite

end TauCeti
