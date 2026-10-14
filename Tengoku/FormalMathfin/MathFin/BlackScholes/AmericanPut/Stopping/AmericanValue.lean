/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Stopping.Reward

/-!
# The continuous-time American put value as a supremum over stopping rules

This is a financial definition, not the classical PDE solution predicate.
The nonempty bounded payoff-value set is proved explicitly. Elementary value
bounds, immediate exercise, the terminal payoff, and maturity monotonicity
follow from the actual stopping rules. No PDE identification is asserted.

## Result

Public entry points include `exerciseValues`, `americanPutValue`, `exerciseValues_nonempty`, `expectedReward_le_strike`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The expected discounted put rewards ranging over all rules bounded by the horizon `T`. -/
noncomputable def exerciseValues (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (T : ℝ≥0) : Set ℝ :=
  range (fun θ : BoundedRule 𝓕 T => ∫ ω, putReward W K r q σ S θ.time ω ∂P)

/-- Supremum of `exerciseValues`, the American put value over rules bounded by `T`. -/
noncomputable def americanPutValue (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (T : ℝ≥0) : ℝ :=
  sSup (exerciseValues P 𝓕 W K r q σ S T)

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
  {K r q σ S : ℝ} {T U : ℝ≥0}

omit [IsProbabilityMeasure P] in
/--
@isnad1 id=nonempty.0h10v.s5.cd29a86bd9ac from=translated src=- shape=badb37c1 vocab=f19c2f13
-/
theorem exerciseValues_nonempty : (exerciseValues P 𝓕 W K r q σ S T).Nonempty :=
  range_nonempty _

/--
@isnad1 id=le.4h11v.s7.ad4a679b76cc from=translated src=- shape=a295f6c9 vocab=9cae36d4
-/
theorem expectedReward_le_strike (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (θ : BoundedRule 𝓕 T) :
    (∫ ω, putReward W K r q σ S θ.time ω ∂P) ≤ K := by
  have hh := integral_mono (putReward_integrable (q := q) (σ := σ) hW P hK hr hS θ.measurable_time)
    (integrable_const K) (putReward_le_strike W hK hr hS θ.time)
  simpa only [integral_const,probReal_univ,one_smul] using hh

/--
@isnad1 id=bddabove.4h10v.s6.52fd3c8a2870 from=translated src=- shape=df49973b vocab=76451f94
-/
theorem exerciseValues_bddAbove (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    BddAbove (exerciseValues P 𝓕 W K r q σ S T) := by
  refine ⟨K,?_⟩
  rintro _ ⟨θ,rfl⟩
  exact expectedReward_le_strike hW hK hr hS θ

/--
@isnad1 id=le.4h11v.s7.d001f15b9d66 from=translated src=- shape=92b9930c vocab=e3ae4e87
-/
theorem expectedReward_le_value (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (θ : BoundedRule 𝓕 T) :
    (∫ ω, putReward W K r q σ S θ.time ω ∂P) ≤ americanPutValue P 𝓕 W K r q σ S T :=
  le_csSup (exerciseValues_bddAbove hW hK hr hS) ⟨θ,rfl⟩

/--
@isnad1 id=le.4h10v.s6.142a17191b1e from=translated src=- shape=aaf15bc3 vocab=aeafdfc8
-/
theorem value_le_strike (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) : americanPutValue P 𝓕 W K r q σ S T ≤ K := by
  apply csSup_le exerciseValues_nonempty
  rintro _ ⟨θ,rfl⟩
  exact expectedReward_le_strike hW hK hr hS θ

/--
@isnad1 id=le.4h10v.s6.8c3acc3740b8 from=translated src=- shape=014f152f vocab=aeafdfc8
-/
theorem value_nonneg (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) : 0 ≤ americanPutValue P 𝓕 W K r q σ S T :=
  (integral_nonneg (putReward_nonneg W K r q σ S (BoundedRule.zero 𝓕 T).time)).trans
    (expectedReward_le_value hW hK hr hS (BoundedRule.zero 𝓕 T))

/--
@isnad1 id=eq.1h10v.s7.9b6a64518794 from=translated src=- shape=a5a82655 vocab=8778dcad
-/
theorem expectedReward_zero (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    (∫ ω, putReward W K r q σ S (BoundedRule.zero 𝓕 T).time ω ∂P) = max (K-S) 0 := by
  change (∫ ω, putReward W K r q σ S (fun _ => 0) ω ∂P) = _
  rw [integral_congr_ae (putReward_zero_ae hzero K r q σ S)]
  simp

/--
@isnad1 id=le.5h10v.s7.c30656ed1505 from=translated src=- shape=e037d4e0 vocab=487b6cf5
-/
theorem payoff_le_value (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) : max (K-S) 0 ≤ americanPutValue P 𝓕 W K r q σ S T := by
  rw [← expectedReward_zero (𝓕 := 𝓕) (T := T) hzero]
  exact expectedReward_le_value hW hK hr hS (BoundedRule.zero 𝓕 T)

/--
@isnad1 id=eq.5h9v.s7.06617f23a202 from=translated src=- shape=8b09a639 vocab=487b6cf5
-/
theorem value_at_expiry (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) : americanPutValue P 𝓕 W K r q σ S 0 = max (K-S) 0 := by
  apply le_antisymm _ (payoff_le_value hW hzero hK hr hS)
  apply csSup_le exerciseValues_nonempty
  rintro _ ⟨θ,rfl⟩
  have heq : θ.time = (BoundedRule.zero 𝓕 0).time := funext θ.time_eq_zero
  change (∫ ω, putReward W K r q σ S θ.time ω ∂P) ≤ _
  rw [heq,expectedReward_zero hzero]

/--
@isnad1 id=le.5h11v.s7.21e00000ca2b from=translated src=- shape=f1f48d38 vocab=aeafdfc8
-/
theorem value_mono_horizon (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (hTU : T ≤ U) :
    americanPutValue P 𝓕 W K r q σ S T ≤ americanPutValue P 𝓕 W K r q σ S U := by
  apply csSup_le exerciseValues_nonempty
  rintro _ ⟨θ,rfl⟩
  exact expectedReward_le_value hW hK hr hS (θ.extend hTU)

/-- The deterministic maturity rule is admissible, so the American value
dominates the European payoff expectation without any optimal-stopping theorem.
@isnad1 id=le.4h10v.s7.5e13c09a6ab5 from=translated src=- shape=68a6f97c vocab=695a2241
-/
theorem european_expectation_le_value (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    (∫ ω, putReward W K r q σ S (fun _ => T) ω ∂P) ≤ americanPutValue P 𝓕 W K r q σ S T :=
  expectedReward_le_value hW hK hr hS (BoundedRule.constant 𝓕 T T le_rfl)

end MathFin.BlackScholes.AmericanPut.Stopping
