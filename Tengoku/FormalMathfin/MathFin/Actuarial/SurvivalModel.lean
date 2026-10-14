/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

The definitions and proofs here are our own, following this library's conventions: Mathlib's
`MeasureTheory`/`ProbabilityTheory`, a concrete complementary-CDF survival function, and the
conditional measure `cond`. Yosuke Ito's Isabelle/HOL AFP entry "Actuarial Mathematics"
(https://isa-afp.org/entries/Actuarial_Mathematics.html, BSD License) — in particular its
`Survival_Model` theory — was consulted as a source for the classical result set, and is cited
here with thanks and with the author's kind permission.
-/
module

public import Tengoku

/-!
# The survival model: age-at-death random variable and conditional survival

The probabilistic foundation of life-contingent actuarial mathematics. A life is described by a
random variable `X : Ω → ℝ`, its **age at death**, on a probability space `(Ω, P)`, with `X > 0`
almost surely. Everything else is derived from the **survival function** (complementary CDF)
`S_X(t) = P(X > t)`.

The design is ours (see the file header); the classical statements were cross-checked against
Yosuke Ito's AFP `Survival_Model`, cited as a source.

The future lifetime of a life aged `x` is `T(x) = X − x`, defined on the event `alive x = {X > x}`
that the life reaches age `x`. Its survival function is the conditional probability
`tpₓ = P(X > x + t ∣ X > x)`, which for `t ≥ 0` collapses to the survival ratio
`tpₓ = S_X(x + t) / S_X(x)` — the keystone of the theory.

## Correspondence with the AFP source (cross-reference only)

For readers coming from the AFP entry, our declarations line up with its `Survival_Model` names:
`alive`↔`alive`, `futureLifetime`↔`futr_life`, `survivalFunction`↔`ccdf (distr 𝔐 borel X)`,
`survive`↔`survive` (`$p_{t&x}`), `die`↔`die` (`$q_{t&x}`), `survivalFunction_zero`↔`ccdfX_0_1`,
`survive_zero`↔`ccdfTx_0_1`, `survive_eq_survivalFunction_ratio`↔`ccdfTx_ccdfX`.

## Main results

* `survivalFunction_zero` — `S_X(0) = 1` (`X > 0` a.e.).
* `survivalFunction_antitone`, `survivalFunction_le_one` — the survival function decreases in `[0, 1]`.
* `survive_zero` — `₀pₓ = 1` for a life alive at `x`.
* `survive_eq_survivalFunction_ratio` — `tpₓ = S_X(x+t) / S_X(x)` for `t ≥ 0`, the survival-ratio
  keystone: the conditional-probability definition of `survive` collapses to the ratio.
-/

@[expose] public section

namespace MathFin.SurvivalModel

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- `alive x` — the event that a life reaches age `x`, i.e. `{ω | x < X ω}`. AFP: `alive`. -/
def alive (X : Ω → ℝ) (x : ℝ) : Set Ω := {ω | x < X ω}

/-- The future lifetime `T(x) = X − x` of a life aged `x`. AFP: `futr_life` (`T`). -/
def futureLifetime (X : Ω → ℝ) (x : ℝ) : Ω → ℝ := fun ω ↦ X ω - x

/-- The **survival function** `S_X(t) = P(X > t)` — the complementary CDF of the age at death.
AFP: `ccdf (distr 𝔐 borel X)`. -/
noncomputable def survivalFunction (P : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  (P (alive X t)).toReal

/-- `tpₓ` — the probability `P(X > x + t ∣ X > x)` that a life aged `x` survives a further `t`
years. AFP: `survive` — the ccdf of the future lifetime `T(x)` under the measure conditioned on
`alive x`. -/
noncomputable def survive (P : Measure Ω) (X : Ω → ℝ) (t x : ℝ) : ℝ :=
  ((P[|alive X x]) (alive X (x + t))).toReal

/-- `tqₓ = 1 − tpₓ` — the probability that a life aged `x` dies within `t` years. AFP: `die`. -/
noncomputable def die (P : Measure Ω) (X : Ω → ℝ) (t x : ℝ) : ℝ :=
  1 - survive P X t x

/--
@isnad1 id=measurab.1h3v.s4.191ab1ad7751 from=translated src=- shape=616a32f7 vocab=f4b08209
-/
lemma measurableSet_alive (hX : Measurable X) (x : ℝ) : MeasurableSet (alive X x) :=
  measurableSet_lt measurable_const hX

omit [MeasurableSpace Ω] in
/-- `alive x` shrinks as `x` grows: reaching a later age is a sub-event.
@isnad1 id=le.1h4v.s4.f7edc1384ca3 from=translated src=- shape=45428bcd vocab=fc370469
-/
lemma alive_subset_alive {x y : ℝ} (hxy : x ≤ y) : alive X y ⊆ alive X x :=
  fun _ hω ↦ lt_of_le_of_lt hxy hω

/-- `S_X(0) = 1`: everyone is alive at age `0`, since `X > 0` almost surely. AFP: `ccdfX_0_1`.
@isnad1 id=eq.1h3v.s6.3544b1796b41 from=translated src=- shape=8ee3ed24 vocab=96ee558a
-/
lemma survivalFunction_zero [IsProbabilityMeasure P] (hpos : ∀ᵐ ω ∂P, 0 < X ω) :
    survivalFunction P X 0 = 1 := by
  have hcompl : P (alive X 0)ᶜ = 0 := measure_mono_null (fun _ hω ↦ hω) (ae_iff.mp hpos)
  have h1 : P (alive X 0) = 1 := by
    rw [← measure_univ (μ := P)]
    exact measure_congr (ae_eq_univ.mpr hcompl)
  rw [survivalFunction, h1, ENNReal.toReal_one]

/-- The survival function is bounded by `1`.
@isnad1 id=le.0h4v.s5.07aa5e3e0c95 from=translated src=- shape=10452168 vocab=d3d6990c
-/
lemma survivalFunction_le_one [IsProbabilityMeasure P] (t : ℝ) :
    survivalFunction P X t ≤ 1 := by
  rw [survivalFunction, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one

/-- The survival function is nonnegative.
@isnad1 id=le.0h4v.s4.a12cb3d860da from=translated src=- shape=514496de vocab=945a6891
-/
lemma survivalFunction_nonneg (t : ℝ) : 0 ≤ survivalFunction P X t :=
  ENNReal.toReal_nonneg

/-- The survival function is nonincreasing in age.
@isnad1 id=antitone.0h3v.s4.cca641ace2ed from=translated src=- shape=524a6c0b vocab=7e65571c
-/
lemma survivalFunction_antitone [IsProbabilityMeasure P] : Antitone (survivalFunction P X) := by
  intro x y hxy
  exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (alive_subset_alive hxy))

/-- `₀pₓ = 1`: a life alive at age `x` survives `0` further years with certainty. AFP: `ccdfTx_0_1`.
@isnad1 id=eq.2h4v.s6.94dfe2b5aff9 from=translated src=- shape=7808efcf vocab=efbba1e2
-/
lemma survive_zero [IsProbabilityMeasure P] (hX : Measurable X) (x : ℝ)
    (hx : P (alive X x) ≠ 0) : survive P X 0 x = 1 := by
  rw [survive, add_zero, cond_apply (measurableSet_alive hX x), Set.inter_self,
    ENNReal.inv_mul_cancel hx (measure_ne_top P _), ENNReal.toReal_one]

/-- **The survival ratio** `tpₓ = S_X(x+t) / S_X(x)` for `t ≥ 0` — the survival-ratio keystone (AFP: `ccdfTx_ccdfX`).
Conditioning on survival to age `x`, a further `t` years of survival has probability the ratio of
the two unconditional survival probabilities.
@isnad1 id=eq.2h5v.s6.90eeccecfd14 from=translated src=- shape=56fb9025 vocab=ceecbb7f
-/
lemma survive_eq_survivalFunction_ratio (hX : Measurable X) (x : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    survive P X t x = survivalFunction P X (x + t) / survivalFunction P X x := by
  have hsub : alive X (x + t) ⊆ alive X x := alive_subset_alive (le_add_of_nonneg_right ht)
  rw [survive, survivalFunction, survivalFunction, cond_apply (measurableSet_alive hX x),
    Set.inter_eq_self_of_subset_right hsub, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

/-- `tpₓ + tqₓ = 1` — the survival/death dichotomy.
@isnad1 id=eq.0h5v.s5.a8a0797a2ef1 from=translated src=- shape=20607e56 vocab=66a93789
-/
lemma survive_add_die (t x : ℝ) : survive P X t x + die P X t x = 1 := by
  rw [die]; ring

end MathFin.SurvivalModel
