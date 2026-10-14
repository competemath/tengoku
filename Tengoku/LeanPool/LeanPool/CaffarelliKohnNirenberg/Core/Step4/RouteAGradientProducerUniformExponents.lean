/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku

/-!
# Route AGradient Producer Uniform Exponents

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

noncomputable section

namespace CKN.Core.Step4

/-- The pressure-gradient Morrey exponent `κ(τ) = (1/τ + 8/25)⁻¹` at the
lower velocity endpoint `τ = 25/3` is `25/11`: the lower end of the range
produced by the one-round improvement.
@isnad1 id=eq.0h0v.s6.2c7545921055 from=translated src=- shape=bc49ab10 vocab=987c6f73
-/
theorem routeA_uniform_kappa_base : (1 / (25 / 3 : ℝ) + 8 / 25)⁻¹ = 25 / 11 := by
  norm_num

/-- The exponent `κ(τ) = (1/τ + 8/25)⁻¹` is nondecreasing on the positive
half-line: a larger velocity exponent `τ` yields a larger pressure-gradient
exponent.
@isnad1 id=le.2h2v.s6.22b3383e86ab from=translated src=- shape=d0f5a23f vocab=7bcc7c03
-/
theorem routeA_uniform_kappa_mono {τ τ' : ℝ} (hτ : 0 < τ) (hττ' : τ ≤ τ') :
    (1 / τ + 8 / 25)⁻¹ ≤ (1 / τ' + 8 / 25)⁻¹ := by
  have hle : 1 / τ' ≤ 1 / τ := one_div_le_one_div_of_le hτ hττ'
  have hτ'pos : 0 < τ' := lt_of_lt_of_le hτ hττ'
  have hpos : 0 < 1 / τ' + 8 / 25 := by positivity
  have hmono : 1 / τ' + 8 / 25 ≤ 1 / τ + 8 / 25 := by linarith only [hle]
  simpa only [one_div] using one_div_le_one_div_of_le hpos hmono

/-- For `q > 5/2` and `τ ≥ 25/3` the capped pressure-gradient exponent
`min κ(τ) q` is at least `6/5`.
@isnad1 id=le.2h2v.s7.d3c83d0d7f4b from=translated src=- shape=663a0b13 vocab=2b311149
-/
theorem routeA_uniform_kappa_min_lower {q τ : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) :
    6 / 5 ≤ min ((1 / τ + 8 / 25)⁻¹) q := by
  apply le_min
  · have h := routeA_uniform_kappa_mono (by norm_num : (0 : ℝ) < 25 / 3) hτ
    rw [routeA_uniform_kappa_base] at h
    linarith only [h]
  · linarith only [hq]

end CKN.Core.Step4
