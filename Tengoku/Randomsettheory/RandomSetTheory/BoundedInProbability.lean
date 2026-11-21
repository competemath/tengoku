/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Seed.MeasureTheory.Function.ConvergenceInDistribution
import Tengoku.Seed.MeasureTheory.Measure.TightNormed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Boundedness in probability

This file defines filter-indexed boundedness in probability for random
variables taking values in a seminormed additive group.  The formulation is
deliberately based on tail events, so it can also be used when the random
quantity is an uncountable supremum whose measurability has not yet been
proved.  The first stability lemma transports the property through an
eventual deterministic norm domination.
-/

open MeasureTheory Set Filter

noncomputable section

namespace RandomSetTheory

/-- A filter-indexed family of random variables is bounded in probability
when its norm has uniformly small tails eventually along the filter.-/
def IsBoundedInProbability
    {Ω ι F : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup F]
    (μ : Measure Ω) (l : Filter ι) (X : ι → Ω → F) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 ≤ M ∧
    ∀ᶠ i in l, μ {ω | M < ‖X i ω‖} ≤ ENNReal.ofReal ε

/-- Boundedness in probability is preserved by an eventual deterministic
norm domination with a fixed nonnegative multiplicative constant.
@isnad1 id=isbounde.3h9v.s6.f6f24295c699 from=translated src=- shape=ba5454cd vocab=3dd69fd8
-/
theorem IsBoundedInProbability.mono_norm
    {Ω ι F G : Type*} [MeasurableSpace Ω]
    [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
    {μ : Measure Ω} {l : Filter ι} {X : ι → Ω → F} {Y : ι → Ω → G}
    (hX : IsBoundedInProbability μ l X) {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ᶠ i in l, ∀ ω, ‖Y i ω‖ ≤ c * ‖X i ω‖) :
    IsBoundedInProbability μ l Y := by
  intro ε hε
  obtain ⟨M, hM, hXM⟩ := hX ε hε
  refine ⟨c * M, mul_nonneg hc hM, ?_⟩
  filter_upwards [hXM, hdom] with i hXi hdomi
  apply hXi.trans'
  apply measure_mono
  intro ω hω
  change c * M < ‖Y i ω‖ at hω
  change M < ‖X i ω‖
  by_cases hc0 : c = 0
  · have hY0 : ‖Y i ω‖ = 0 := by
      apply le_antisymm
      · simpa [hc0] using hdomi ω
      · exact norm_nonneg _
    simp [hc0, hY0] at hω
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    nlinarith [hω, hdomi ω]

/-! ## Weak convergence implies boundedness in probability -/

/-- A family with laws converging weakly to a probability measure is bounded
in probability.  The completeness and second-countability assumptions ensure
that the limiting law is tight.  Portmanteau, applied to the closed norm tail
`{x | M ≤ ‖x‖}`, then transfers a strict tail bound to the approximating
laws.

This law-level statement is useful when the limiting probability measure is
given directly, without choosing a random variable that realizes it.
@isnad1 id=isbounde.2h7v.s7.d71918582c91 from=translated src=- shape=9f6c693a vocab=a625cb8a
-/
theorem isBoundedInProbability_of_tendsto_law
    {Ω ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup E] [CompleteSpace E] [SecondCountableTopology E]
    [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {l : Filter ι} {X : ι → Ω → E} (hX : ∀ i, AEMeasurable (X i) μ)
    (ν : ProbabilityMeasure E)
    (hLaw : Tendsto (β := ProbabilityMeasure E)
      (fun i ↦ (⟨μ.map (X i), Measure.isProbabilityMeasure_map (hX i)⟩ :
        ProbabilityMeasure E)) l (nhds ν)) :
    IsBoundedInProbability μ l X := by
  intro ε hε
  have hν_tight : IsTightMeasureSet {(ν : Measure E)} :=
    isTightMeasureSet_singleton
  have htail : Tendsto
      (fun r : ℝ ↦ (ν : Measure E) {x | r < ‖x‖}) atTop (nhds 0) := by
    simpa using tendsto_measure_norm_gt_of_isTightMeasureSet hν_tight
  have hε_ennreal : (0 : ENNReal) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hsmall : ∀ᶠ r : ℝ in atTop,
      (ν : Measure E) {x | r < ‖x‖} < ENNReal.ofReal ε :=
    htail.eventually_lt_const hε_ennreal
  obtain ⟨r, hr, hν_tail⟩ :=
    ((eventually_ge_atTop (0 : ℝ)).and hsmall).exists
  let M : ℝ := r + 1
  let F : Set E := {x | M ≤ ‖x‖}
  have hM : 0 ≤ M := by
    dsimp [M]
    linarith
  have hF_closed : IsClosed F := by
    exact isClosed_le continuous_const continuous_norm
  have hν_F : (ν : Measure E) F < ENNReal.ofReal ε := by
    apply (measure_mono ?_).trans_lt hν_tail
    intro x hx
    change M ≤ ‖x‖ at hx
    change r < ‖x‖
    dsimp [M] at hx
    linarith
  have hlimsup :
      (l.limsup fun i ↦
        ((⟨μ.map (X i), Measure.isProbabilityMeasure_map (hX i)⟩ :
          ProbabilityMeasure E) : Measure E) F) ≤ (ν : Measure E) F :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hLaw hF_closed
  have heventually : ∀ᶠ i in l,
      ((⟨μ.map (X i), Measure.isProbabilityMeasure_map (hX i)⟩ :
        ProbabilityMeasure E) : Measure E) F < ENNReal.ofReal ε :=
    eventually_lt_of_limsup_lt (hlimsup.trans_lt hν_F)
  refine ⟨M, hM, ?_⟩
  filter_upwards [heventually] with i hi
  change (μ.map (X i)) F < ENNReal.ofReal ε at hi
  rw [Measure.map_apply_of_aemeasurable (hX i) hF_closed.measurableSet] at hi
  apply (measure_mono ?_).trans hi.le
  intro ω hω
  change M < ‖X i ω‖ at hω
  change X i ω ∈ F
  exact hω.le

/-- Convergence in distribution to a normed-space-valued random variable
implies boundedness in probability.
@isnad1 id=isbounde.1h9v.s7.1cf16732debf from=translated src=- shape=c3686c60 vocab=de2e809f
-/
theorem _root_.MeasureTheory.TendstoInDistribution.isBoundedInProbability
    {Ω Ω' ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace E] [NormedAddCommGroup E] [CompleteSpace E]
    [SecondCountableTopology E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {l : Filter ι} {X : ι → Ω → E} {Z : Ω' → E}
    (h : MeasureTheory.TendstoInDistribution X l Z (fun _ ↦ μ) μ') :
    IsBoundedInProbability μ l X := by
  exact isBoundedInProbability_of_tendsto_law h.forall_aemeasurable
    ⟨μ'.map Z, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩ h.tendsto

end RandomSetTheory
