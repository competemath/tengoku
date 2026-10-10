/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/GammaRBracket.lean — the critical-line Γℝ bracket; proves
`Zeta23.WeilEF.gammaR_bracket`:

  logDeriv Γℝ(1/2+it) + logDeriv Γℝ(1/2−it) = Re ψ(1/4 + it/2) − log π      (t ∈ ℝ),

from Γℝ(s) = π^{−s/2}Γ(s/2) (Mathlib `Complex.Gammaℝ`), logDeriv Γℝ(s) = −(log π)/2 + ψ(s/2)/2
for re s > 0, and the conjugation symmetry ψ(conj z) = conj ψ(z) (from the partial-fraction
series Zeta23.DigammaSeries.hasSum_digamma_series).
-/
import Tengoku
import Tengoku.FormalMath.Zeta23.GammaFacts.Series

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex

/-- conjugation symmetry of the digamma function off the poles. -/
theorem digamma_conj {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Complex.digamma (starRingEnd ℂ z) = starRingEnd ℂ (Complex.digamma z) := by
  have hz' : starRingEnd ℂ z ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    apply hz
    refine ⟨k, ?_⟩
    have := congrArg (starRingEnd ℂ) hk
    simpa using this
  have h1 := Zeta23.DigammaSeries.hasSum_digamma_series hz
  have h2 := Zeta23.DigammaSeries.hasSum_digamma_series hz'
  -- conj of the series for z is the series for conj z
  have h1c : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (starRingEnd ℂ z + n + 1))
      (starRingEnd ℂ (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z)) := by
    have := (Complex.hasSum_conj' ).mpr h1
    refine this.congr_fun fun n => ?_
    simp only [map_sub, map_div₀, map_one, map_add, map_natCast]
  have huniq := h2.unique h1c
  have e : starRingEnd ℂ (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z)
      = starRingEnd ℂ (Complex.digamma z) + (Real.eulerMascheroniConstant : ℂ)
        + 1 / starRingEnd ℂ z := by
    simp only [map_add, map_div₀, map_one, Complex.conj_ofReal]
  rw [e] at huniq
  linear_combination huniq

end WeilEF
end Zeta23
