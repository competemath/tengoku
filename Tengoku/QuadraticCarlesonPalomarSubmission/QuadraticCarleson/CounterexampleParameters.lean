/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.CounterexampleLevelSet

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter MeasureTheory Set

namespace QuadraticCarleson

set_option autoImplicit false

/- The amplitude and logarithmic shift used in the paper's counterexample. -/
noncomputable def paperAmplitude (N : ℕ) : ℝ :=
  Real.log (N : ℝ) / (2 : ℝ) ^ 40

noncomputable def paperExponentShift (N : ℕ) : ℝ :=
  Real.logb 2 (paperAmplitude N)

/--
@isnad1 id=lt.1h1v.s4.1597f213087a from=translated src=- shape=8bdc09dd vocab=8f815610
-/
theorem paperAmplitude_pos_of_one_le {N : ℕ} (hN : 1 ≤ paperAmplitude N) :
    0 < paperAmplitude N := lt_of_lt_of_le zero_lt_one hN

/--
@isnad1 id=eventual.0h0v.s4.193abb036f12 from=translated src=- shape=574b785d vocab=6ebc9aff
-/
theorem eventually_paperAmplitude_ge_one :
    ∀ᶠ N : ℕ in atTop, 1 ≤ paperAmplitude N := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ 40 := by positivity
  have hlog : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ 40 ≤ Real.log (N : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hlog] with N hN
  unfold paperAmplitude
  exact (le_div_iff₀ hden).mpr (by simpa [one_mul] using hN)

/--
@isnad1 id=eventual.0h0v.s4.2f64c72f8bc9 from=translated src=- shape=574b785d vocab=61a4de0e
-/
theorem eventually_paperAmplitude_pos :
    ∀ᶠ N : ℕ in atTop, 0 < paperAmplitude N := by
  filter_upwards [eventually_paperAmplitude_ge_one] with N hN
  exact paperAmplitude_pos_of_one_le hN

/--
@isnad1 id=eq.1h1v.s5.bda3086ae403 from=translated src=- shape=dc0efb61 vocab=2196988c
-/
theorem paperExponentShift_rpow_eq_amplitude {N : ℕ}
    (hN : 0 < paperAmplitude N) :
    (2 : ℝ) ^ paperExponentShift N = paperAmplitude N := by
  unfold paperExponentShift
  exact Real.rpow_logb (by norm_num) (by norm_num) hN

/--
@isnad1 id=le.1h1v.s4.77c2cfaa87cd from=translated src=- shape=f1eeeb7c vocab=123b10ed
-/
theorem paperExponentShift_nonneg_of_amplitude_ge_one {N : ℕ}
    (hN : 1 ≤ paperAmplitude N) :
    0 ≤ paperExponentShift N := by
  unfold paperExponentShift
  exact Real.logb_nonneg (by norm_num) hN

/--
@isnad1 id=eventual.0h0v.s4.48826e817607 from=translated src=- shape=574b785d vocab=29d3716c
-/
theorem eventually_paperExponentShift_nonneg :
    ∀ᶠ N : ℕ in atTop, 0 ≤ paperExponentShift N := by
  filter_upwards [eventually_paperAmplitude_ge_one] with N hN
  exact paperExponentShift_nonneg_of_amplitude_ge_one hN

/--
@isnad1 id=eventual.0h0v.s6.25d80e4d8e0b from=translated src=- shape=01f6adce vocab=40215cb5
-/
theorem eventually_paper_window_start :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ 3 * (N : ℝ) ^ 2 / 5 + paperExponentShift N := by
  filter_upwards [eventually_ge_atTop 2, eventually_paperExponentShift_nonneg]
    with N hN hL
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  nlinarith [sq_nonneg ((N : ℝ) - 2)]

/-- The fixed small constant used for the final counterexample level.-/
noncomputable def negativeEndpointHeightConstant : ℝ := 1 / 8

/--
@isnad1 id=lt.0h0v.s3.7a8638225c58 from=translated src=- shape=ff3a10fc vocab=770ffe0b
-/
theorem negativeEndpointHeightConstant_pos :
    0 < negativeEndpointHeightConstant := by
  unfold negativeEndpointHeightConstant
  norm_num

noncomputable def negativeEndpointCounterexampleHeight (N : ℕ) : ℝ :=
  counterexampleHeight negativeEndpointHeightConstant N

/--
@isnad1 id=eq.0h1v.s5.d94c832acaea from=translated src=- shape=1334a33c vocab=549fe243
-/
theorem negativeEndpointCounterexampleHeight_eq (N : ℕ) :
    negativeEndpointCounterexampleHeight N =
      Real.log (N : ℝ) / (8 * (N : ℝ)) := by
  unfold negativeEndpointCounterexampleHeight counterexampleHeight
  unfold negativeEndpointHeightConstant
  ring

/--
@isnad1 id=eq.0h1v.s5.982b55099698 from=translated src=- shape=639f0b19 vocab=549fe243
-/
theorem negativeEndpointCounterexampleHeight_eq_const_mul (N : ℕ) :
    negativeEndpointCounterexampleHeight N =
      (1 / 8 : ℝ) * (Real.log (N : ℝ) / (N : ℝ)) := by
  unfold negativeEndpointCounterexampleHeight counterexampleHeight
  unfold negativeEndpointHeightConstant
  ring

/--
@isnad1 id=eventual.0h0v.s4.931ef1b787d7 from=translated src=- shape=574b785d vocab=6330265b
-/
theorem eventually_negativeEndpointCounterexampleHeight_pos :
    ∀ᶠ N : ℕ in atTop, 0 < negativeEndpointCounterexampleHeight N := by
  simpa only [negativeEndpointCounterexampleHeight] using
    (eventually_counterexampleHeight_pos negativeEndpointHeightConstant_pos)

end QuadraticCarleson
