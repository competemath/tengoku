/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Tengoku.Formalslt.FormalSLT.AnytimeValid.AtTopCS
import Tengoku.Formalslt.FormalSLT.AnytimeValid.EProcess
import Tengoku.Formalslt.FormalSLT.AnytimeValid.MixtureCS
import Tengoku.Formalslt.FormalSLT.Concentration.SubGamma.CondExpProduct

/-!
# Betting confidence sequences

This file adds the betting/e-process confidence-sequence construction for a
bounded mean. For a candidate null mean `m` and predictable betting fractions
`lambda_k`, the wealth process is

`K_n(m) = prod_{k < n} (1 + lambda_k * (X_k - m))`.

If each factor is nonnegative, each `lambda_k` is `F_k`-measurable and
nonnegative, and the null conditional-mean condition
`E[X_k | F_k] <= m` holds, then `K_n(m)` is a nonnegative supermartingale.
Ville's inequality gives the countable-time rejection bound
`P(exists n > 0, K_n(m) >= 1 / delta) <= delta`.

The increment process uses `IncrementAdapted F X`, so `X_k` is revealed at
time `k+1`. The betting fraction process uses `StronglyAdapted F lambda`, so
`lambda_k` is predictable.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace FormalSLT.AnytimeValid

noncomputable section

/-- One multiplicative betting factor for candidate mean `m`. -/
def bettingFactor {Ω : Type*} (X lambda : ℕ → Ω → ℝ) (m : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  1 + lambda k ω * (X k ω - m)

/-- Betting wealth `K_n(m) = prod_{k<n} (1 + lambda_k (X_k - m))`. -/
def bettingWealthProcess {Ω : Type*} (X lambda : ℕ → Ω → ℝ) (m : ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range n, bettingFactor X lambda m k ω

/-- Candidate mean `m` is rejected once the betting wealth crosses `1 / delta`. -/
def bettingMeanRejectionEvent {Ω : Type*} (X lambda : ℕ → Ω → ℝ) (m delta : ℝ) :
    Set Ω :=
  {ω | ∃ n : ℕ, 0 < n ∧ (1 / delta) ≤ bettingWealthProcess X lambda m n ω}

/-- Nonnegative betting factors give nonnegative wealth.
@isnad1 id=le.1h4v.s6.31dc7c8e73be from=translated src=- shape=7a90b79e vocab=f27d3174
-/
theorem bettingWealth_nonneg {Ω : Type*} {X lambda : ℕ → Ω → ℝ} {m : ℝ}
    (hfactor_nonneg : ∀ k ω, 0 ≤ bettingFactor X lambda m k ω) :
    0 ≤ bettingWealthProcess X lambda m := by
  intro n ω
  unfold bettingWealthProcess
  exact Finset.prod_nonneg fun k _ => hfactor_nonneg k ω

/-- The betting wealth is adapted when increments are revealed one step late and bets are predictable.
@isnad1 id=strongly.2h6v.s6.571073f1cbb4 from=translated src=- shape=742f38f8 vocab=4fc2cbae
-/
theorem stronglyAdapted_bettingWealthProcess_of_adapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ}
    {X lambda : ℕ → Ω → ℝ} {m : ℝ}
    (hX_adapted : IncrementAdapted ℱ X)
    (hlambda_adapted : StronglyAdapted ℱ lambda) :
    StronglyAdapted ℱ (bettingWealthProcess X lambda m) := by
  intro n
  have hprod : StronglyMeasurable[ℱ n]
      (fun ω => ∏ k ∈ Finset.range n, bettingFactor X lambda m k ω) := by
    apply Finset.stronglyMeasurable_fun_prod
    intro k hk
    rw [Finset.mem_range] at hk
    have hlambda : StronglyMeasurable[ℱ n] (lambda k) :=
      (hlambda_adapted k).mono (ℱ.mono (le_of_lt hk))
    have hX : StronglyMeasurable[ℱ n] (X k) :=
      (hX_adapted k).mono (ℱ.mono (Nat.succ_le_of_lt hk))
    exact stronglyMeasurable_const.add (hlambda.mul (hX.sub stronglyMeasurable_const))
  change StronglyMeasurable[ℱ n]
    (fun ω => ∏ k ∈ Finset.range n, bettingFactor X lambda m k ω)
  exact hprod

/--
The one-step betting factor has conditional expectation at most `1` under the
conditional-mean null. The betting fraction is predictable, bounded, and
nonnegative.
@isnad1 id=eventual.5h9v.s7.810f2192edda from=translated src=- shape=363b629e vocab=e7a1d173
-/
theorem bettingFactor_condExp_le_one_of_condMean
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X lambda : ℕ → Ω → ℝ} {m C : ℝ} (k : ℕ)
    (hlambda_meas : StronglyMeasurable[ℱ k] (lambda k))
    (hlambda_bdd : ∀ᵐ ω ∂μ, |lambda k ω| ≤ C)
    (hlambda_nonneg : ∀ᵐ ω ∂μ, 0 ≤ lambda k ω)
    (hX_int : Integrable (X k) μ)
    (hmean : μ[X k | ℱ k] ≤ᵐ[μ] fun _ => m) :
    μ[bettingFactor X lambda m k | ℱ k] ≤ᵐ[μ] fun _ => (1 : ℝ) := by
  set Y : Ω → ℝ := fun ω => X k ω - m with hY_def
  have hY_int : Integrable Y μ := by
    change Integrable (X k - fun _ => m) μ
    exact hX_int.sub (integrable_const m)
  have hprod_int : Integrable (fun ω => lambda k ω * Y ω) μ := by
    refine hY_int.bdd_mul (c := C)
      ((hlambda_meas.mono (ℱ.le k)).aestronglyMeasurable) ?_
    filter_upwards [hlambda_bdd] with ω hω
    simpa [Real.norm_eq_abs] using hω
  have hconst_int : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const _
  have hsplit :
      μ[bettingFactor X lambda m k | ℱ k]
        =ᵐ[μ]
      μ[(fun _ : Ω => (1 : ℝ)) | ℱ k] + μ[fun ω => lambda k ω * Y ω | ℱ k] :=
    by
      change μ[(fun _ : Ω => (1 : ℝ)) + fun ω => lambda k ω * Y ω | ℱ k]
        =ᵐ[μ]
        μ[(fun _ : Ω => (1 : ℝ)) | ℱ k] + μ[fun ω => lambda k ω * Y ω | ℱ k]
      exact condExp_add hconst_int hprod_int (ℱ k)
  have hpull :
      μ[fun ω => lambda k ω * Y ω | ℱ k]
        =ᵐ[μ] fun ω => lambda k ω * (μ[Y | ℱ k]) ω :=
    FormalSLT.Concentration.SubGamma.condExp_mul_bounded_left
      (ℱ.le k) hlambda_meas hlambda_bdd hY_int
  have hsub :
      μ[Y | ℱ k] =ᵐ[μ] fun ω => (μ[X k | ℱ k]) ω - m := by
    have hraw := condExp_sub hX_int (integrable_const m) (ℱ k)
    have hconst : μ[(fun _ : Ω => m) | ℱ k] = fun _ : Ω => m :=
      condExp_const (ℱ.le k) m
    filter_upwards [hraw] with ω hω
    change μ[X k - (fun _ : Ω => m) | ℱ k] ω = μ[X k | ℱ k] ω - m
    rw [hω]
    simp [hconst]
  have hconst_one : μ[(fun _ : Ω => (1 : ℝ)) | ℱ k] = fun _ : Ω => (1 : ℝ) :=
    condExp_const (ℱ.le k) 1
  filter_upwards [hsplit, hpull, hsub, hmean, hlambda_nonneg] with
    ω hsplitω hpullω hsubω hmeanω hlambdaω
  rw [hsplitω]
  simp only [Pi.add_apply]
  rw [hconst_one, hpullω, hsubω]
  have hdiff : (μ[X k | ℱ k]) ω - m ≤ 0 := sub_nonpos.mpr hmeanω
  have hmul : lambda k ω * ((μ[X k | ℱ k]) ω - m) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlambdaω hdiff
  linarith

/--
The betting wealth is a supermartingale from one-step factor control.

The hypotheses keep the predictable-bet discipline explicit: `X` uses
`IncrementAdapted`, while `lambda` is `StronglyAdapted`. The bounded-current-
wealth hypothesis is the exact condition needed to use mathlib's conditional
pull-out theorem.
@isnad1 id=supermar.7h7v.s8.66c6428fe55c from=translated src=- shape=f92aac13 vocab=0aab07c7
-/
theorem bettingWealth_supermartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X lambda : ℕ → Ω → ℝ} {m : ℝ}
    (hX_adapted : IncrementAdapted ℱ X)
    (hlambda_adapted : StronglyAdapted ℱ lambda)
    (hwealth_int : ∀ n, Integrable (bettingWealthProcess X lambda m n) μ)
    (hfactor_int : ∀ n, Integrable (bettingFactor X lambda m n) μ)
    (hwealth_bdd : ∀ n, ∃ C : ℝ,
      ∀ᵐ ω ∂μ, |bettingWealthProcess X lambda m n ω| ≤ C)
    (hfactor_nonneg : ∀ k ω, 0 ≤ bettingFactor X lambda m k ω)
    (hfactor_step : ∀ k,
      μ[bettingFactor X lambda m k | ℱ k] ≤ᵐ[μ] fun _ => (1 : ℝ)) :
    Supermartingale (bettingWealthProcess X lambda m) ℱ μ := by
  refine supermartingale_nat
    (stronglyAdapted_bettingWealthProcess_of_adapted hX_adapted hlambda_adapted)
    hwealth_int ?_
  intro n
  set Z : Ω → ℝ := bettingWealthProcess X lambda m n with hZ_def
  set Y : Ω → ℝ := bettingFactor X lambda m n with hY_def
  have hfact :
      bettingWealthProcess X lambda m (n + 1) = fun ω => Z ω * Y ω := by
    funext ω
    simp [bettingWealthProcess, bettingFactor, Z, Y, Finset.prod_range_succ, mul_comm]
  have hZ_meas : StronglyMeasurable[ℱ n] Z := by
    simpa [Z] using
      stronglyAdapted_bettingWealthProcess_of_adapted
        (ℱ := ℱ) (X := X) (lambda := lambda) (m := m)
        hX_adapted hlambda_adapted n
  obtain ⟨C, hZ_bdd⟩ := hwealth_bdd n
  have hpull :
      μ[fun ω => Z ω * Y ω | ℱ n] =ᵐ[μ] fun ω => Z ω * (μ[Y | ℱ n]) ω :=
    FormalSLT.Concentration.SubGamma.condExp_mul_bounded_left
      (ℱ.le n) hZ_meas hZ_bdd (by simpa [Y] using hfactor_int n)
  rw [hfact]
  filter_upwards [hpull, hfactor_step n] with ω hpullω hstepω
  rw [hpullω]
  have hZ_nonneg : 0 ≤ Z ω := by
    simpa [Z] using bettingWealth_nonneg (X := X) (lambda := lambda) (m := m)
      hfactor_nonneg n ω
  calc
    Z ω * (μ[Y | ℱ n]) ω ≤ Z ω * 1 :=
      mul_le_mul_of_nonneg_left (by simpa [Y] using hstepω) hZ_nonneg
    _ = bettingWealthProcess X lambda m n ω := by simp [Z]

/-- The betting wealth is an e-process when it is nonnegative and a supermartingale.
@isnad1 id=eprocess.2h7v.s6.b8b0d6b59458 from=translated src=- shape=2fd749ca vocab=beb0e1a1
-/
theorem bettingWealth_eProcess
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}
    {X lambda : ℕ → Ω → ℝ} {m : ℝ}
    (hsup : Supermartingale (bettingWealthProcess X lambda m) ℱ μ)
    (hfactor_nonneg : ∀ k ω, 0 ≤ bettingFactor X lambda m k ω) :
    EProcess μ ℱ (bettingWealthProcess X lambda m) where
  nonneg := bettingWealth_nonneg hfactor_nonneg
  start_one := fun ω => by simp [bettingWealthProcess]
  supermartingale := hsup

namespace BettingNonVacuityWitness

/-- Uniform probability measure on `Bool`. -/
def μBool : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

/-- One Rademacher increment, followed by zero increments. -/
def XBool : ℕ → Bool → ℝ :=
  fun k ω => if k = 0 then (if ω then (1 : ℝ) else -1) else 0

/-- Constant predictable betting fraction `1/4`. -/
def lambdaBool : ℕ → Bool → ℝ :=
  fun _ _ => 1 / 4

/-- The two-level filtration: `F 0 = bot`, `F k = top` for `k >= 1`. -/
def filtBool : Filtration ℕ (⊤ : MeasurableSpace Bool) where
  seq := fun k => if k = 0 then ⊥ else ⊤
  mono' := by
    intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp [hi, hj]
      · simp only [hi, hj]; exact bot_le
    · have hj : j ≠ 0 := by
        rintro rfl
        exact hi (Nat.le_zero.mp hij)
      simp [hi, hj]
  le' := by
    intro i
    by_cases hi : i = 0
    · simp only [hi]; exact bot_le
    · simp [hi]

/--
@isnad1 id=incremen.0h0v.s5.ffef10b95cae from=translated src=- shape=7af4a0a2 vocab=82e9a6b1
-/
theorem XBool_incrementAdapted : IncrementAdapted filtBool XBool := by
  intro k
  have hfilt : filtBool (k + 1) = ⊤ := by simp [filtBool]
  rw [show (StronglyMeasurable[filtBool (k + 1)] (XBool k)) =
      (StronglyMeasurable[⊤] (XBool k)) from by rw [hfilt]]
  exact measurable_from_top.stronglyMeasurable

/--
@isnad1 id=strongly.0h0v.s6.1a291a9bafb9 from=translated src=- shape=6465d66e vocab=70124adb
-/
theorem lambdaBool_stronglyAdapted : StronglyAdapted filtBool lambdaBool := by
  intro k
  exact stronglyMeasurable_const

/--
@isnad1 id=le.0h2v.s4.161777f60dc7 from=translated src=- shape=5d0da768 vocab=ed29ef22
-/
theorem factor_nonneg (k : ℕ) (ω : Bool) :
    0 ≤ bettingFactor XBool lambdaBool 0 k ω := by
  simp only [bettingFactor, lambdaBool, XBool, sub_zero]
  by_cases hk : k = 0
  · subst hk
    cases ω <;> norm_num
  · simp [hk]

/-- The betting witness gains wealth on the positive Rademacher outcome.
@isnad1 id=lt.0h0v.s4.cca2eee1bdfa from=translated src=- shape=86336e4a vocab=d752f6fa
-/
theorem bettingWitness_positive_gain :
    (1 : ℝ) < bettingWealthProcess XBool lambdaBool 0 1 true := by
  simp [bettingWealthProcess, bettingFactor, XBool, lambdaBool]

end BettingNonVacuityWitness

end

end FormalSLT.AnytimeValid
