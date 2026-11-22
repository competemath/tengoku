/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Tengoku.Seed.Probability.Process.HittingTime
import Tengoku.Absorptioncutoff.AbsorptionCutoff.Cutoff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Absorption times

The first hitting time of the absorbing state `0` for an abstract discrete-time process,
packaged using Mathlib's `MeasureTheory.hittingAfter`.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- The first time at or after zero when a discrete-time process hits the state `0`,
with value `⊤` if it never does. -/
noncomputable def absorptionTime {Ω β : Type*} [Zero β]
    (X : ℕ → Ω → β) : Ω → WithTop ℕ :=
  hittingAfter X {0} 0

/-- The absorption time of an adapted process is a stopping time.
@isnad1 id=isstoppi.1h6v.s5.d1dccc159c57 from=translated src=- shape=c7f1488b vocab=1bca02bd
-/
lemma Adapted.isStoppingTime_absorptionTime {Ω β : Type*} {m : MeasurableSpace Ω}
    {_ : MeasurableSpace β} [Zero β] [MeasurableSingletonClass β]
    {ℱ : Filtration ℕ m} {X : ℕ → Ω → β} (hX : Adapted ℱ X) :
    IsStoppingTime ℱ (absorptionTime X) := by
  exact hX.isStoppingTime_hittingAfter (measurableSet_singleton 0)

/-- Survival through time `t` means precisely that the process has avoided `0` at every
time `s ≤ t`.
@isnad1 id=iff.0h5v.s5.87580ad768cc from=translated src=- shape=26ed720e vocab=c612b4f3
-/
lemma absorptionTime_gt_iff {Ω β : Type*} [Zero β] {X : ℕ → Ω → β}
    {ω : Ω} {t : ℕ} :
    (t : WithTop ℕ) < absorptionTime X ω ↔ ∀ s ≤ t, X s ω ≠ 0 := by
  rw [← not_le]
  change (¬hittingAfter X {0} 0 ω ≤ (t : WithTop ℕ)) ↔ ∀ s ≤ t, X s ω ≠ 0
  have hle : hittingAfter X {0} 0 ω ≤ (t : WithTop ℕ)
      ↔ ∃ s ≤ t, X s ω = 0 := by
    simpa [Set.mem_Icc] using
      (MeasureTheory.hittingAfter_le_iff (u := X) (s := {0}) (n := 0)
        (i := t) (ω := ω))
  rw [hle]
  simp

/-- A pathwise absorbing state, once reached, persists at every later time.
@isnad1 id=eq.3h6v.s6.c8ccd34b7e4a from=translated src=- shape=d28a1571 vocab=67c372d7
-/
lemma zero_persists {Ω β : Type*} [Zero β] {X : ℕ → Ω → β}
    (habs : ∀ t ω, X t ω = 0 → X (t + 1) ω = 0)
    {ω : Ω} {s t : ℕ} (hst : s ≤ t) (hs : X s ω = 0) :
    X t ω = 0 := by
  induction t generalizing s with
  | zero =>
      have hs0 : s = 0 := Nat.le_zero.mp hst
      simpa [hs0] using hs
  | succ t ih =>
      by_cases hst' : s = t + 1
      · simpa [hst'] using hs
      · have hle : s ≤ t := Nat.le_of_lt_succ (lt_of_le_of_ne hst hst')
        exact habs t ω (ih hle hs)

/-- Pointwise-in-`ω` version of `zero_persists`: absorption need only hold along the
single path `ω`.
@isnad1 id=eq.3h6v.s6.4530e4717a75 from=translated src=- shape=3c72f43f vocab=67c372d7
-/
lemma zero_persists' {Ω β : Type*} [Zero β] {X : ℕ → Ω → β} {ω : Ω}
    (hω : ∀ s, X s ω = 0 → X (s + 1) ω = 0) {s t : ℕ} (hst : s ≤ t) (hs : X s ω = 0) :
    X t ω = 0 := by
  induction t generalizing s with
  | zero =>
      have hs0 : s = 0 := Nat.le_zero.mp hst
      simpa [hs0] using hs
  | succ t ih =>
      by_cases hst' : s = t + 1
      · simpa [hst'] using hs
      · exact hω t (ih (Nat.le_of_lt_succ (lt_of_le_of_ne hst hst')) hs)

/-- For a process absorbed at zero, survival through time `t` is equivalent to being
nonzero at time `t`.
@isnad1 id=iff.1h5v.s6.eac964aeb045 from=translated src=- shape=c0794584 vocab=56f921e7
-/
lemma absorptionTime_gt_iff_value_ne_zero {Ω β : Type*} [Zero β]
    {X : ℕ → Ω → β}
    (habs : ∀ t ω, X t ω = 0 → X (t + 1) ω = 0)
    {ω : Ω} {t : ℕ} :
    (t : WithTop ℕ) < absorptionTime X ω ↔ X t ω ≠ 0 := by
  rw [absorptionTime_gt_iff]
  constructor
  · exact fun h => h t le_rfl
  · intro ht s hst hs
    exact ht (zero_persists habs hst hs)

/-- Under pathwise absorption, the survival probability through time `t` is the mass of
the terminal nonzero event.
@isnad1 id=eq.1h6v.s7.14afff23fb14 from=translated src=- shape=397b0149 vocab=405c7ee8
-/
lemma measure_absorptionTime_gt_eq {Ω β : Type*} [Zero β]
    {_ : MeasurableSpace Ω} {μ : Measure Ω} {X : ℕ → Ω → β}
    (habs : ∀ t ω, X t ω = 0 → X (t + 1) ω = 0) (t : ℕ) :
    μ {ω | (t : WithTop ℕ) < absorptionTime X ω}
      = μ {ω | X t ω ≠ 0} := by
  congr 1
  ext ω
  exact absorptionTime_gt_iff_value_ne_zero habs

/-- Almost-everywhere version of `measure_absorptionTime_gt_eq`: absorption need only hold
`μ`-a.e. at each step (as on a canonical path space), where it fails pathwise.
@isnad1 id=eq.1h6v.s7.7ce0c34d4046 from=translated src=- shape=40baecda vocab=19722422
-/
lemma measure_absorptionTime_gt_eq_of_ae {Ω β : Type*} [Zero β]
    {_ : MeasurableSpace Ω} {μ : Measure Ω} {X : ℕ → Ω → β}
    (habs_ae : ∀ s, ∀ᵐ ω ∂μ, X s ω = 0 → X (s + 1) ω = 0) (t : ℕ) :
    μ {ω | (t : WithTop ℕ) < absorptionTime X ω}
      = μ {ω | X t ω ≠ 0} := by
  have hall : ∀ᵐ ω ∂μ, ∀ s, X s ω = 0 → X (s + 1) ω = 0 := ae_all_iff.mpr habs_ae
  have hEq : {ω | (t : WithTop ℕ) < absorptionTime X ω} =ᵐ[μ] {ω | X t ω ≠ 0} := by
    filter_upwards [hall] with ω hω
    have hiff : ((t : WithTop ℕ) < absorptionTime X ω) ↔ (X t ω ≠ 0) := by
      rw [absorptionTime_gt_iff]
      exact ⟨fun h => h t le_rfl, fun ht s hst hs => ht (zero_persists' hω hst hs)⟩
    exact propext hiff
  exact measure_congr hEq

/-- If the time-`t` marginal of an absorbing process is `ν`, then its survival probability
through `t` is exactly `ν({0}ᶜ)`.
@isnad1 id=eq.3h8v.s7.86c3d2e176f0 from=translated src=- shape=f1f3f906 vocab=f1764812
-/
lemma measure_absorptionTime_gt_eq_of_map {Ω β : Type*}
    {_ : MeasurableSpace Ω} {_ : MeasurableSpace β}
    [Zero β] [MeasurableSingletonClass β]
    {μ : Measure Ω} {ν : Measure β} {X : ℕ → Ω → β}
    (habs : ∀ t ω, X t ω = 0 → X (t + 1) ω = 0)
    (t : ℕ) (hXt : Measurable (X t)) (hmarg : μ.map (X t) = ν) :
    μ {ω | (t : WithTop ℕ) < absorptionTime X ω} = ν ({0}ᶜ) := by
  calc
    μ {ω | (t : WithTop ℕ) < absorptionTime X ω}
        = μ {ω | X t ω ≠ 0} := measure_absorptionTime_gt_eq habs t
    _ = μ ((X t) ⁻¹' ({0}ᶜ)) := by
      congr 1
    _ = μ.map (X t) ({0}ᶜ) :=
      (Measure.map_apply hXt (measurableSet_singleton 0).compl).symm
    _ = ν ({0}ᶜ) := by rw [hmarg]

/-- Kernel-power specialization of `measure_absorptionTime_gt_eq_of_map`. The sole
probabilistic input is the time-`t` marginal law.
@isnad1 id=eq.3h9v.s8.2289d0042761 from=translated src=- shape=18d9a822 vocab=85288622
-/
lemma measure_absorptionTime_gt_eq_kernel_pow {Ω β : Type*}
    {_ : MeasurableSpace Ω} {_ : MeasurableSpace β}
    [Zero β] [MeasurableSingletonClass β]
    {μ : Measure Ω} {κ : Kernel β β} [IsMarkovKernel κ]
    {X : ℕ → Ω → β} {x : β}
    (habs : ∀ t ω, X t ω = 0 → X (t + 1) ω = 0)
    (t : ℕ) (hXt : Measurable (X t))
    (hmarg : μ.map (X t) = (κ ^ t) x) :
    μ {ω | (t : WithTop ℕ) < absorptionTime X ω}
      = (κ ^ t) x ({0}ᶜ) :=
  measure_absorptionTime_gt_eq_of_map habs t hXt hmarg

/-- Almost-everywhere version of `measure_absorptionTime_gt_eq_of_map`: if the time-`t`
marginal of an a.e.-absorbing process is `ν`, then its survival probability through `t`
is exactly `ν({0}ᶜ)`.
@isnad1 id=eq.3h8v.s7.cd68b0feb997 from=translated src=- shape=e46e1e83 vocab=86a28efa
-/
lemma measure_absorptionTime_gt_eq_of_ae_map {Ω β : Type*}
    {_ : MeasurableSpace Ω} {_ : MeasurableSpace β}
    [Zero β] [MeasurableSingletonClass β]
    {μ : Measure Ω} {ν : Measure β} {X : ℕ → Ω → β}
    (habs_ae : ∀ s, ∀ᵐ ω ∂μ, X s ω = 0 → X (s + 1) ω = 0)
    (t : ℕ) (hXt : Measurable (X t)) (hmarg : μ.map (X t) = ν) :
    μ {ω | (t : WithTop ℕ) < absorptionTime X ω} = ν ({0}ᶜ) := by
  calc
    μ {ω | (t : WithTop ℕ) < absorptionTime X ω}
        = μ {ω | X t ω ≠ 0} := measure_absorptionTime_gt_eq_of_ae habs_ae t
    _ = μ ((X t) ⁻¹' ({0}ᶜ)) := by
      congr 1
    _ = μ.map (X t) ({0}ᶜ) :=
      (Measure.map_apply hXt (measurableSet_singleton 0).compl).symm
    _ = ν ({0}ᶜ) := by rw [hmarg]

/-- Almost-everywhere version of `measure_absorptionTime_gt_eq_kernel_pow`. The sole
probabilistic input is the time-`t` marginal law; absorption need only hold `μ`-a.e.
@isnad1 id=eq.3h9v.s8.2064e80c7a61 from=translated src=- shape=83e04685 vocab=e4c6be7a
-/
lemma measure_absorptionTime_gt_eq_of_ae_kernel_pow {Ω β : Type*}
    {_ : MeasurableSpace Ω} {_ : MeasurableSpace β}
    [Zero β] [MeasurableSingletonClass β]
    {μ : Measure Ω} {κ : Kernel β β} [IsMarkovKernel κ]
    {X : ℕ → Ω → β} {x : β}
    (habs_ae : ∀ s, ∀ᵐ ω ∂μ, X s ω = 0 → X (s + 1) ω = 0)
    (t : ℕ) (hXt : Measurable (X t))
    (hmarg : μ.map (X t) = (κ ^ t) x) :
    μ {ω | (t : WithTop ℕ) < absorptionTime X ω}
      = (κ ^ t) x ({0}ᶜ) :=
  measure_absorptionTime_gt_eq_of_ae_map habs_ae t hXt hmarg

end AbsorptionCutoff
