/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import Tengoku.LeanPool.LeanPool.PLAcceleratedNesterovLean.Core.Defs

/-!
# Lyapunov Contraction Step 2: Normal Terms and Perturbation Absorption

## Normal terms completing the square
The normal velocity part reassembles as:
  ((1-a)μ'/2)‖e‖² + (1-a)√μ'⟨P⊥v, e⟩ + ((1-a)/2)‖P⊥v‖²
  = ((1-a)/2)‖P⊥v + √μ' e‖²
  = ((1-a)/2)‖u_n‖²

## Function value collection
f(x') - (1-a)(f(x')-f(x)) - a(f(x')-f⋆) = (1-a)(f(x)-f⋆)

## Passing from w_n to u_{n+1}
Since u_{n+1} = w_n + √μ' ξ_n:
  ½‖u_{n+1}‖² = ½‖w_n‖² + √μ'⟨w_n, ξ_n⟩ + (μ'/2)‖ξ_n‖²
-/

@[expose] public section

noncomputable section

namespace PLAcceleratedNesterovLean

/-- Completing the square: q/2·‖v‖² + q·c·⟨v, e⟩ + q·c²/2·‖e‖² = q/2·‖v + c·e‖².
@isnad1 id=eq.1h5v.s8.8781a1405c94 from=translated src=- shape=beca7b7f vocab=35177f74
-/
theorem complete_square_normal {d : ℕ} (v e : E d) (q c : ℝ) (_hq : 0 ≤ q) :
    q / 2 * ‖v‖ ^ 2 + q * c * @inner ℝ _ _ v e + q * c ^ 2 / 2 * ‖e‖ ^ 2
    = q / 2 * ‖v + c • e‖ ^ 2 := by
  simp only [norm_add_sq_real, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Function value telescope:
    (f' - fstar) - (1-a)(f' - f) - a(f' - fstar) = (1-a)(f - fstar)
    where f' = f(x'_n), f = f(x_n), fstar = f⋆.
@isnad1 id=eq.0h4v.s6.cd3606cbb9c3 from=translated src=- shape=8f674512 vocab=f8bb600d
-/
theorem function_value_collection (f' f fstar a : ℝ) :
    (f' - fstar) - (1 - a) * (f' - f) - a * (f' - fstar) = (1 - a) * (f - fstar) := by
  ring

/-- Perturbation from w to u: ‖w + c·ξ‖² = ‖w‖² + 2c⟨w,ξ⟩ + c²‖ξ‖².
@isnad1 id=eq.0h4v.s8.865189117921 from=translated src=- shape=042dac4e vocab=f9e77286
-/
theorem perturbation_expansion {d : ℕ} (w ξ : E d) (c : ℝ) :
    ‖w + c • ξ‖ ^ 2 = ‖w‖ ^ 2 + 2 * c * @inner ℝ _ _ w ξ + c ^ 2 * ‖ξ‖ ^ 2 := by
  simp only [norm_add_sq_real, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Cauchy-Schwarz application: |⟨w, ξ⟩| ≤ ‖w‖ · ‖ξ‖.
@isnad1 id=le.0h3v.s7.658b29a6313d from=translated src=- shape=6e106b5c vocab=2cfa7cba
-/
theorem inner_abs_le_norm_mul {d : ℕ} (w ξ : E d) :
    |@inner ℝ _ _ w ξ| ≤ ‖w‖ * ‖ξ‖ := by
  exact abs_real_inner_le_norm w ξ

end PLAcceleratedNesterovLean
