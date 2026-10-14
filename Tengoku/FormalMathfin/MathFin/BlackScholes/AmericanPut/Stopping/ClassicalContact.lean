/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Stopping.FirstContact
public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Stopping.ClassicalCandidate
public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Boundary.DividendContact

/-!
# The classical-price first-contact rule

The gap between discounted classical value and discounted payoff is continuous,
adapted, nonnegative, and zero at maturity. Its first zero therefore supplies
an explicit admissible contact rule; no optimal-stopping assertion is assumed.

## Result

Public entry points include `classicalCandidate_adapted`, `frozenPutReward`, `frozenPutReward_adapted`, `frozenPutReward_continuous`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set
open MathFin.BlackScholes.AmericanPut.Boundary
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
  {k h K r q σ S : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

/--
@isnad1 id=adapted.2h13v.s6.d84b92e38c1a from=translated src=- shape=472b6c90 vocab=21f78f64
-/
theorem classicalCandidate_adapted (hp : DividendPutSolution k h p b)
    (hW : Adapted 𝓕 W) (T : ℝ≥0) : Adapted 𝓕 (classicalCandidate W K r q σ S p T) := by
  intro t
  let s := min t T
  have htime : 0 ≤ σ^2/2*((T : ℝ)-(s : ℝ)) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast min_le_right t T))
  have hc : Continuous (fun w : ℝ => p (Real.log (S/K)+(r-q-σ^2/2)*(s : ℝ)+σ*w)
      (σ^2/2*((T : ℝ)-(s : ℝ)))) := by
    exact hp.price_continuous.comp_continuous
      (show Continuous (fun w : ℝ => (Real.log (S/K)+(r-q-σ^2/2)*(s : ℝ)+σ*w,
        σ^2/2*((T : ℝ)-(s : ℝ)))) by fun_prop) (fun _ => htime)
  have hm := hc.measurable.comp ((hW s).mono (𝓕.mono (min_le_left t T)) le_rfl)
  exact measurable_const.mul (measurable_const.mul hm)

/-- The put reward for exercise at the deterministic time `min t T`, so it is frozen once `t`
passes maturity. -/
noncomputable def frozenPutReward (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (T t : ℝ≥0) : Ω → ℝ :=
  putReward W K r q σ S (fun _ => min t T)

/--
@isnad1 id=adapted.1h9v.s6.f2c1f051acd3 from=translated src=- shape=c7742d42 vocab=420b45f6
-/
theorem frozenPutReward_adapted (hW : Adapted 𝓕 W) (T : ℝ≥0) :
    Adapted 𝓕 (frozenPutReward W K r q σ S T) := by
  intro t
  have hw : @Measurable Ω ℝ (𝓕 t) _ (W (min t T)) :=
    (hW _).mono (𝓕.mono (min_le_left t T)) le_rfl
  unfold frozenPutReward putReward MathFin.gbmValue
  dsimp only
  fun_prop

omit [MeasurableSpace Ω] in
/--
@isnad1 id=continuo.1h9v.s5.e37af251ab6e from=translated src=- shape=11b92610 vocab=60b10097
-/
theorem frozenPutReward_continuous (hW : ∀ ω, Continuous (fun t => W t ω)) (T : ℝ≥0) (ω : Ω) :
    Continuous (fun t => frozenPutReward W K r q σ S T t ω) := by
  unfold frozenPutReward putReward MathFin.gbmValue
  fun_prop

/-- The gap `classicalCandidate - frozenPutReward` between the discounted classical price and
the discounted payoff. -/
noncomputable def classicalGap (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ)
    (p : ℝ → ℝ → ℝ) (T t : ℝ≥0) (ω : Ω) : ℝ :=
  classicalCandidate W K r q σ S p T t ω - frozenPutReward W K r q σ S T t ω

/--
@isnad1 id=adapted.2h13v.s6.7da20c6fc184 from=translated src=- shape=472b6c90 vocab=e2c38d33
-/
theorem classicalGap_adapted (hp : DividendPutSolution k h p b)
    (hW : Adapted 𝓕 W) (T : ℝ≥0) : Adapted 𝓕 (classicalGap W K r q σ S p T) :=
  fun t => (classicalCandidate_adapted hp hW T t).sub (frozenPutReward_adapted hW T t)

omit [MeasurableSpace Ω] in
/--
@isnad1 id=continuo.2h13v.s6.71f8b4fc2119 from=translated src=- shape=071acee9 vocab=31e204bc
-/
theorem classicalGap_continuous (hp : DividendPutSolution k h p b)
    (hW : ∀ ω, Continuous (fun t => W t ω)) (T : ℝ≥0) (ω : Ω) :
    Continuous (fun t => classicalGap W K r q σ S p T t ω) :=
  (classicalCandidate_continuous hp hW T ω).sub (frozenPutReward_continuous hW T ω)

omit [MeasurableSpace Ω] in
/--
@isnad1 id=le.3h14v.s6.44b062e04d5d from=translated src=- shape=6cbac675 vocab=ccc13720
-/
theorem classicalGap_nonneg (hp : DividendPutSolution k h p b)
    (hK : 0 < K) (hS : 0 < S) (T t : ℝ≥0) (ω : Ω) :
    0 ≤ classicalGap W K r q σ S p T t ω := by
  have hh := classicalCandidate_dominates (r := r) (q := q) (σ := σ) hp W hK hS (min_le_right t T) ω
  simpa [classicalGap,frozenPutReward,classicalCandidate,min_assoc] using sub_nonneg.mpr hh

omit [MeasurableSpace Ω] in
/--
@isnad1 id=eq.3h13v.s6.949e293df920 from=translated src=- shape=40e3ae7b vocab=02734628
-/
theorem classicalGap_terminal (hp : DividendPutSolution k h p b)
    (hK : 0 < K) (hS : 0 < S) (T : ℝ≥0) (ω : Ω) :
    classicalGap W K r q σ S p T T ω = 0 := by
  simp only [classicalGap,classicalCandidate_maturity hp W hK hS,frozenPutReward,min_self,sub_self]

/-- The rule that exercises at the first zero of `classicalGap`, admissible by
`firstContactRule`. -/
noncomputable def classicalContactRule (hp : DividendPutSolution k h p b)
    (hadapt : Adapted 𝓕 W) (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 < K) (hS : 0 < S) (T : ℝ≥0) : BoundedRule 𝓕 T :=
  firstContactRule (Z := classicalGap W K r q σ S p T)
    (classicalGap_adapted hp hadapt T) (classicalGap_continuous hp hpaths T)
    (classicalGap_nonneg hp hK hS T) T (classicalGap_terminal hp hK hS T)

/--
@isnad1 id=other.5h14v.s7.bcfef08100c6 from=translated src=- shape=a5991832 vocab=cf8c158f
-/
theorem classicalContactRule_contact (hp : DividendPutSolution k h p b)
    (hadapt : Adapted 𝓕 W) (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 < K) (hS : 0 < S) (T : ℝ≥0) (ω : Ω) :
    let θ := classicalContactRule (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T
    classicalCandidate W K r q σ S p T (θ.time ω) ω = putReward W K r q σ S θ.time ω := by
  let θ := classicalContactRule (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T
  have hh := (firstContactTime_mem (classicalGap_continuous (r := r) (q := q) (σ := σ) hp hpaths T)
    (classicalGap_terminal hp hK hS T) ω).2
  change classicalGap W K r q σ S p T (θ.time ω) ω = 0 at hh
  have ht := θ.le_horizon ω
  simp only [classicalGap,frozenPutReward,min_eq_left ht,sub_eq_zero] at hh
  exact hh

omit [MeasurableSpace Ω] in
/--
@isnad1 id=iff.5h14v.s7.7df2f880b40d from=translated src=- shape=43bb792b vocab=8342162a
-/
theorem classicalGap_zero_iff (hp : DividendPutSolution k h p b)
    (hK : 0 < K) (hS : 0 < S) (hσ : 0 < σ) {T t : ℝ≥0} (ht : t < T) (ω : Ω) :
    classicalGap W K r q σ S p T t ω = 0 ↔
      classicalLogSpot W K r q σ S t ω ≤ b (σ^2/2*((T : ℝ)-(t : ℝ))) := by
  have htime : 0 < σ^2/2*((T : ℝ)-(t : ℝ)) :=
    mul_pos (by positivity) (sub_pos.mpr (by exact_mod_cast ht))
  simp only [classicalGap,classicalCandidate,frozenPutReward,putReward,min_eq_left ht.le,
    sub_eq_zero]
  rw [← scaled_classical_payoff W hK hS t ω,
    mul_right_inj' (Real.exp_pos _).ne',mul_right_inj' hK.ne',hp.contact_iff htime]

/--
@isnad1 id=and.7h15v.s7.4e9cc994d975 from=translated src=- shape=551027dd vocab=d96bdf12
-/
theorem classicalContactRule_continuation (hp : DividendPutSolution k h p b)
    (hadapt : Adapted 𝓕 W) (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 < K) (hS : 0 < S) (hσ : 0 < σ) {T t : ℝ≥0} (ω : Ω)
    (ht : t < (classicalContactRule (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T).time ω) :
    t < T ∧ b (σ^2/2*((T : ℝ)-(t : ℝ))) < classicalLogSpot W K r q σ S t ω := by
  let θ := classicalContactRule (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T
  have htT : t < T := ht.trans_le (θ.le_horizon ω)
  refine ⟨htT,lt_of_not_ge ?_⟩
  intro hx
  have hz := (classicalGap_zero_iff hp hK hS hσ htT ω).mpr hx
  have hpos := firstContactTime_pos_before
    (classicalGap_continuous (r := r) (q := q) (σ := σ) hp hpaths T)
    (classicalGap_nonneg hp hK hS T) (classicalGap_terminal hp hK hS T) ω ht
  exact (ne_of_gt hpos) hz

/-- The explicit first-contact rule discharges the admissibility and contact
premises of verification. Only the candidate's two stochastic properties are
left here, and neither is silently inferred from the classical PDE.
@isnad1 id=eq.10h14v.s8.c1e27069cb9f from=translated src=- shape=9be8fd60 vocab=85fe5969
-/
theorem classical_price_eq_value_of_contact_verification
    {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ≥0}
    (hp : DividendPutSolution k h p b) (hW : Measurable W.uncurry) (hadapt : Adapted 𝓕 W)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 < K) (hr : 0 ≤ r) (hS : 0 < S)
    (hsuper : Supermartingale (classicalCandidate W K r q σ S p T) 𝓕 P)
    (hmart : Martingale (fun t ω => classicalCandidate W K r q σ S p T
      (min t ((classicalContactRule (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T).time ω)) ω) 𝓕 P) :
    americanPutValue P 𝓕 W K r q σ S T = K*p (Real.log (S/K)) (σ^2/2*(T : ℝ)) :=
  classical_price_eq_value_of_verification hp hW hpaths hzero hK hr hS hsuper
    (classicalContactRule hp hadapt hpaths hK hS T)
    (Filter.Eventually.of_forall (classicalContactRule_contact hp hadapt hpaths hK hS T)) hmart

end MathFin.BlackScholes.AmericanPut.Stopping
