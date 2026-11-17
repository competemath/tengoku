/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Analysis.Calculus.Deriv.Comp
import Tengoku.Seed.Analysis.Calculus.Deriv.Mul
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ComplexAnalysis.LogDerivative
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.Definitions
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.FunctionalEquation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pullback chain rule between the z-plane and s-plane

The chain rule `Λ[Ξ](z) = i · Λ[ξ](½ + i·z)` for the critical-line pullback,
plus the differentiability facts it consumes. Converts the z-plane
anti-Herglotz statement into the s-plane left-half-plane sign statement.
-/

namespace OverflowResidueRH

open Complex

/-- **PROVED — inner derivative.** `HasDerivAt (fun z => ½ + I·z) I z`,
the derivative of the critical-shift map is `I` at every point.
@isnad1 id=hasderiv.0h1v.s6.ec542bd8bccc from=translated src=- shape=53eee74a vocab=137297f6
-/
theorem hasDerivAt_critical_shift (z : ℂ) :
    HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) + Complex.I * z) Complex.I z := by
  have h1 : HasDerivAt (fun z : ℂ => z) (1 : ℂ) z := hasDerivAt_id z
  have h2 : HasDerivAt (fun z : ℂ => Complex.I * z) (Complex.I * 1) z :=
    h1.const_mul Complex.I
  have h3 : HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) + Complex.I * z)
                       (0 + Complex.I * 1) z :=
    (hasDerivAt_const z (1 / 2 : ℂ)).add h2
  simpa using h3

/-- ⭐ **PROVED — chain rule for `XiPullback`.** Under differentiability
of `completedXiFunction` at the pullback point,
  `Λ[Ξ](z) = I · Λ[ξ](½ + I·z)`.
The explicit converter that unlocks attacks on the explicit ξ formula.
@isnad1 id=eq.1h1v.s7.891fe09d1cb5 from=translated src=- shape=8c606761 vocab=1ef8b685
-/
theorem XiPullback_logDeriv_chain_rule
    {z : ℂ}
    (hxi_diff : DifferentiableAt ℂ completedXiFunction
                  ((1 / 2 : ℂ) + Complex.I * z)) :
    logDerivativeResponse XiPullback z =
      Complex.I *
        (deriv completedXiFunction ((1 / 2 : ℂ) + Complex.I * z) /
          completedXiFunction ((1 / 2 : ℂ) + Complex.I * z)) := by
  have h_outer : HasDerivAt completedXiFunction
                  (deriv completedXiFunction ((1 / 2 : ℂ) + Complex.I * z))
                  ((1 / 2 : ℂ) + Complex.I * z) := hxi_diff.hasDerivAt
  have h_inner := hasDerivAt_critical_shift z
  have h_chain : HasDerivAt
                  (fun w : ℂ => completedXiFunction ((1 / 2 : ℂ) + Complex.I * w))
                  (deriv completedXiFunction ((1 / 2 : ℂ) + Complex.I * z)
                    * Complex.I) z := by
    have h := h_outer.comp z h_inner
    simpa [Function.comp_def] using h
  unfold logDerivativeResponse XiPullback
  rw [h_chain.deriv]
  ring

/-- **Hypothesis — `completedXiFunction` is differentiable on the open
left half-plane `{s : Re s < ½}`.** Non-trivial to inhabit for the
Γ-based definition (Γ has poles at non-positive integers; the actual `ξ`
is entire), routed through `CompletedXiRegularity`.-/
def CompletedXiDifferentiableOnLeftHalfPlane : Prop :=
  ∀ s : ℂ, s.re < (1 / 2 : ℝ) → DifferentiableAt ℂ completedXiFunction s

/-- ⭐ **PROVED — completed-xi regularity ⟹ left-half-plane
differentiability.**
@isnad1 id=complete.1h0v.s1.08db37ca0cba from=translated src=- shape=1d48f1ac vocab=19a03176
-/
theorem completedXiRegularity_gives_leftHalfDiff
    (H : CompletedXiRegularity) :
    CompletedXiDifferentiableOnLeftHalfPlane :=
  fun s _ => H.differentiable s

/-- ⭐ **PROVED — `XiPullback` is differentiable from `CompletedXiRegularity`.**
The composition of the entire inner map `z ↦ (1/2) + I·z` with the
everywhere-differentiable outer `completedXiFunction`.
@isnad1 id=differen.1h1v.s6.f4e2553178f9 from=translated src=- shape=ac643da3 vocab=90cd584f
-/
theorem XiPullback_differentiableAt_of_completedXiRegularity
    (H : CompletedXiRegularity) (z : ℂ) :
    DifferentiableAt ℂ XiPullback z := by
  unfold XiPullback
  have h_inner : DifferentiableAt ℂ
                  (fun w : ℂ => (1 / 2 : ℂ) + Complex.I * w) z :=
    (differentiableAt_const _).add
      ((differentiableAt_const _).mul differentiableAt_fun_id)
  have h_outer : DifferentiableAt ℂ completedXiFunction
                  ((1 / 2 : ℂ) + Complex.I * z) :=
    H.differentiable _
  exact h_outer.comp z h_inner

/-- ⭐ **PROVED — chain rule for `EntireXiPullback`.**
`Λ[EntireXiPullback](z) = I · Λ[entireRiemannXi](½ + I·z)`. The
Mathlib-grounded analogue; the critical-shift arithmetic is ξ-agnostic.
@isnad1 id=eq.0h1v.s7.9e265a3e673a from=translated src=- shape=ec0b1282 vocab=91aa1eb1
-/
theorem EntireXiPullback_logDeriv_chain_rule (z : ℂ) :
    logDerivativeResponse EntireXiPullback z =
      Complex.I *
        (deriv entireRiemannXi ((1 / 2 : ℂ) + Complex.I * z) /
          entireRiemannXi ((1 / 2 : ℂ) + Complex.I * z)) := by
  have h_outer : HasDerivAt entireRiemannXi
                  (deriv entireRiemannXi ((1 / 2 : ℂ) + Complex.I * z))
                  ((1 / 2 : ℂ) + Complex.I * z) :=
    (entireRiemannXi_differentiableAt _).hasDerivAt
  have h_inner := hasDerivAt_critical_shift z
  have h_chain : HasDerivAt
                  (fun w : ℂ => entireRiemannXi ((1 / 2 : ℂ) + Complex.I * w))
                  (deriv entireRiemannXi ((1 / 2 : ℂ) + Complex.I * z)
                    * Complex.I) z := by
    have h := h_outer.comp z h_inner
    simpa [Function.comp_def] using h
  unfold logDerivativeResponse EntireXiPullback
  rw [h_chain.deriv]
  ring

end OverflowResidueRH
