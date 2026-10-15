/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import Tengoku.LeanPool.LeanPool.PLAcceleratedNesterovLean.Core.Defs
public import Tengoku

/-!
# Lyapunov Contraction Step 1: Descent Lemma and Parameter Identities

## Descent Lemma
For L-smooth f with step x₊ = x - (1/L)∇f(x):
  f(x₊) ≤ f(x) - (1/(2L))‖∇f(x)‖²

## Parameter Identities
With ρ = (1-a)/(1+a) and λ = (1+a)²/(2(1-a)):
  (1+a)ρ = 1-a
  λρ² = (1-a)/2

## Velocity Coefficient Bound
If ε·η ≤ a and 0 ≤ a < 1:
  (1-a)² + ε·η·(1-a) ≤ 1-a
  (1-a)(1+a) ≤ (1+a)² = 2(1-a)λ
-/

@[expose] public section

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped NNReal

/-- Descent lemma: f(x - η·∇f(x)) ≤ f(x) - (η/2)·‖∇f(x)‖² for η = 1/L.
    This is stated abstractly: if f(y) ≤ f(x) + ⟨∇f(x), y-x⟩ + (L/2)‖y-x‖²
    and y = x - (1/L)·∇f(x), then f(y) ≤ f(x) - (1/(2L))·‖∇f(x)‖².
@isnad1 id=le.2h4v.s7.a72fd70822c8 from=translated src=- shape=1d6812b0 vocab=762a6581
-/
theorem descent_lemma (fx fy : ℝ) (grad_sq : ℝ) (L : ℝ)
    (hL : 0 < L)
    (hsmooth : fy ≤ fx - (1 / L) * grad_sq +
      (L / 2) * (1 / L) ^ 2 * grad_sq) :
    fy ≤ fx - 1 / (2 * L) * grad_sq := by
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have key : fx - 1 / L * grad_sq + L / 2 * (1 / L) ^ 2 * grad_sq = fx - 1 / (2 * L) * grad_sq := by
    field_simp
    ring
  linarith

/-- Parameter identity: (1 + a) · ρ = 1 - a when ρ = (1-a)/(1+a).
@isnad1 id=eq.2h2v.s6.fa1b9205462e from=translated src=- shape=4dba6e2a vocab=335f4d48
-/
theorem rho_identity (a ρ : ℝ) (ha : 1 + a ≠ 0)
    (hρ : ρ = (1 - a) / (1 + a)) :
    (1 + a) * ρ = 1 - a := by
  rw [hρ, mul_div_cancel₀ _ ha]

/-- Parameter identity: λ · ρ² = (1-a)/2 when ρ = (1-a)/(1+a) and λ = (1+a)²/(2(1-a)).
@isnad1 id=eq.4h3v.s7.616797bc6ac0 from=translated src=- shape=46878b8b vocab=4d09f77c
-/
theorem lambda_rho_sq (a ρ lam : ℝ) (ha_ne : 1 + a ≠ 0) (ha_pos : 1 - a ≠ 0)
    (hρ : ρ = (1 - a) / (1 + a))
    (hlam : lam = (1 + a) ^ 2 / (2 * (1 - a))) :
    lam * ρ ^ 2 = (1 - a) / 2 := by
  subst hρ; subst hlam; field_simp

/-- Velocity normal coefficient bound: (1-a)² + εη(1-a) ≤ (1-a) when εη ≤ a.
@isnad1 id=le.4h2v.s6.242ccdbabbbf from=translated src=- shape=3699eefd vocab=c0564ed8
-/
theorem velocity_normal_coeff (a εη : ℝ) (_ha : 0 ≤ a) (ha1 : a ≤ 1)
    (_hεη : 0 ≤ εη) (hbound : εη ≤ a) :
    (1 - a) ^ 2 + εη * (1 - a) ≤ 1 - a := by
  nlinarith [sq_nonneg a, sq_nonneg (1 - a)]

/-- Tangential coefficient bound: (1-a)(1+a) ≤ (1+a)².
@isnad1 id=le.1h1v.s6.554967e4b4fc from=translated src=- shape=499d12eb vocab=c0564ed8
-/
theorem tangential_coeff (a : ℝ) (ha : 0 ≤ a) :
    (1 - a) * (1 + a) ≤ (1 + a) ^ 2 := by
  nlinarith [sq_nonneg a]

end PLAcceleratedNesterovLean
