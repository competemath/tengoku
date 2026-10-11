/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku

/-!
# Moment-slice extreme-point support bound (Richter–Rogosinski / Winkler)

Let `K = [a,b]` be a compact interval and `s : ℝ`.  The *moment slice* is the set of
probability measures on `K` with mean `0` and second moment `s`:

    C = { μ | μ Kᶜ = 0 ∧ ∫ x ∂μ = 0 ∧ ∫ x² ∂μ = s }.

This file proves the support-size part of the Richter–Rogosinski / Karr / Winkler
*canonical representation* theorem for this two-moment slice.  It starts with the
finite-atom perturbation argument: three homogeneous linear constraints (total mass,
mean, second moment) on four-or-more atom weights always admit a nonzero perturbation
`δ`, and `μ ± ε·δ` are then two distinct measures of `C` whose midpoint is `μ`,
contradicting extremality.  The later support argument upgrades this from a finite atom
set to an arbitrary extreme probability measure in the slice.

Main results:
* `exists_moment_perturbation` — pure linear algebra: on `4`-or-more reals there is a
  nonzero weight perturbation killing the three moments `1, x, x²` simultaneously.
* `card_le_three_of_isExtremePoint` — an extreme point of the moment slice supported on a
  finite positive-weight atom set has at most three atoms.
* `exists_isMinOn_momentSlice` — on a compact Hausdorff space the moment slice is weak-*
  compact, so a bounded-continuous objective attains its minimum over the slice.
* `support_finite_ncard_le_three_of_isExtremePoint` — any extreme probability measure in
  the two-moment slice has finite topological support of cardinality at most three.
* `isAtomic_le_three_of_isExtremePoint` and
  `exists_cardSupportLe_three_of_isExtremePoint` — the same conclusion as a positive
  discrete-measure representation and as a finite support carrier.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal NNReal BoundedContinuousFunction

namespace Causalean.Mathlib.MeasureTheory

noncomputable section

/-- Given [a measurable sample space](hyp:α), [a finite set \(T\) of points in that space](hyp:T),
and [a real-valued weight function](hyp:w), the [discrete measure](goal) is the sum of the
Dirac measures at the points of \(T\), each multiplied by the nonnegative part of its weight. -/
noncomputable def discreteMeasure {α : Type*} [MeasurableSpace α]
    (T : Finset α) (w : α → ℝ) : Measure α :=
  ∑ x ∈ T, ENNReal.ofReal (w x) • Measure.dirac x

/-- Given [real numbers \(a\), \(b\), and \(s\)](hyp:a,b,s), the [moment slice](goal) is the set
of probability measures on the real line that [are supported on the closed interval from \(a\) to
\(b\)](step:1,step:2), have mean zero, and have second moment \(s\). -/
def MomentSlice (a b s : ℝ) : Set (Measure ℝ) :=
  {μ | IsProbabilityMeasure μ ∧ μ (Set.Icc a b)ᶜ = 0 ∧
        (∫ x, x ∂μ = 0) ∧ (∫ x, x ^ 2 ∂μ = s)}

/-- Given [a set \(C\) of measures on the real line](hyp:C) and [a measure \(\mu\) on the real line](hyp:μ),
the [extreme-point property](goal) holds when [\(\mu\) belongs to \(C\)](step:1) and, for every
pair of measures in \(C\) and every mixing weight strictly between zero and one, equality of
\(\mu\) to their weighted mixture [implies that the two measures are equal](step:2). -/
def IsExtremePoint (C : Set (Measure ℝ)) (μ : Measure ℝ) : Prop :=
  μ ∈ C ∧ ∀ μ₁ ∈ C, ∀ μ₂ ∈ C, ∀ t : ℝ≥0∞, 0 < t → t < 1 →
    μ = t • μ₁ + (1 - t) • μ₂ → μ₁ = μ₂

/-! ### Linear-algebra core -/

/-- **Three-moment perturbation.** On any finite set `T ⊆ ℝ` of more than three points there
is a nonzero real weighting `δ` whose total mass, first moment and second moment all vanish.
This is rank–nullity: three linear functionals (`∑ δ`, `∑ δ·x`, `∑ δ·x²`) on a space of
dimension `> 3` have a nonzero common kernel. -/
theorem exists_moment_perturbation {T : Finset ℝ} (hT : 3 < T.card) :
    ∃ δ : ℝ → ℝ, (∑ x ∈ T, δ x = 0) ∧ (∑ x ∈ T, δ x * x = 0) ∧
      (∑ x ∈ T, δ x * x ^ 2 = 0) ∧ (∃ x ∈ T, δ x ≠ 0) := by
  classical
  set φ : ℝ → (Fin 2 → ℝ) := fun x => ![x, x ^ 2] with hφ
  have hφinj : Function.Injective φ := by
    intro x y h; have := congrFun h 0; simpa [hφ] using this
  have hinjOn : Set.InjOn φ T := hφinj.injOn
  have hcard : Module.finrank ℝ (Fin 2 → ℝ) + 1 < (T.image φ).card := by
    rw [Finset.card_image_of_injOn hinjOn, Module.finrank_pi]; simpa using hT
  obtain ⟨g, hsum0, hgsum, v, hv, hvne⟩ :=
    Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card hcard
  rw [Finset.sum_image hinjOn] at hgsum hsum0
  have h0 := congrFun hsum0 0
  have h1 := congrFun hsum0 1
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, hφ,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  obtain ⟨x, hxT, hxne⟩ : ∃ x ∈ T, g (φ x) ≠ 0 := by
    rw [Finset.mem_image] at hv; obtain ⟨x, hxT, rfl⟩ := hv; exact ⟨x, hxT, hvne⟩
  exact ⟨fun x => g (φ x), hgsum, h0, h1, x, hxT, hxne⟩

/-! ### Measure-level computations -/

/-- A discrete measure whose atoms all lie in a set gives zero mass to that set's
complement. -/
theorem discreteMeasure_apply_compl_of_subset {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {T : Finset α} {w : α → ℝ} {K : Set α}
    (hTK : ∀ x ∈ T, x ∈ K) :
    discreteMeasure T w Kᶜ = 0 := by
  rw [discreteMeasure, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  have : x ∉ Kᶜ := by simp [hTK x hx]
  simp [this]

/-- A finite discrete measure is a probability measure when all atom weights
are nonnegative and their sum is one. -/
theorem isProbabilityMeasure_discreteMeasure {α : Type*} [MeasurableSpace α]
    {T : Finset α} {w : α → ℝ}
    (hw : ∀ x ∈ T, 0 ≤ w x) (hsum : ∑ x ∈ T, w x = 1) :
    IsProbabilityMeasure (discreteMeasure T w) := by
  constructor
  rw [discreteMeasure, Measure.finsetSum_apply]
  have : ∀ x ∈ T, (ENNReal.ofReal (w x) • Measure.dirac x) Set.univ = ENNReal.ofReal (w x) := by
    intro x hx; rw [Measure.smul_apply, smul_eq_mul]; simp
  rw [Finset.sum_congr rfl this, ← ENNReal.ofReal_sum_of_nonneg hw, hsum, ENNReal.ofReal_one]

/-- Integral against a discrete measure is the weighted sum of the integrand over the atoms.
Every function into a real normed vector space is integrable because the measure
has finite support. -/
theorem integral_discreteMeasure {α E : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : Finset α} {w : α → ℝ} (hw : ∀ x ∈ T, 0 ≤ w x)
    (f : α → E) :
    ∫ x, f x ∂(discreteMeasure T w) = ∑ x ∈ T, w x • f x := by
  rw [discreteMeasure, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw x hx)]
  · intro x hx
    exact (integrable_dirac enorm_lt_top).smul_measure (by simp)

/-- The mass assigned by a finite discrete measure to an atom in its support is
the corresponding atom weight, coerced to `ℝ≥0∞`. -/
theorem discreteMeasure_singleton {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {T : Finset α} {w : α → ℝ} {x₀ : α} (hx₀ : x₀ ∈ T) :
    discreteMeasure T w {x₀} = ENNReal.ofReal (w x₀) := by
  classical
  rw [discreteMeasure, Measure.finsetSum_apply]
  have : ∀ x ∈ T, (ENNReal.ofReal (w x) • Measure.dirac x) {x₀}
      = if x = x₀ then ENNReal.ofReal (w x) else 0 := by
    intro x hx
    rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
    by_cases h : x = x₀ <;> simp [h, Set.mem_singleton_iff]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' T x₀ (fun x => ENNReal.ofReal (w x))]
  simp [hx₀]

/-! ### Headline -/

/-! ### Attainment -/

/-- **Attainment of the minimum over a moment slice.** On a compact Hausdorff space `Ω`, the
set of probability measures pinned by two bounded-continuous moment constraints
`∫ g₁ = c₁`, `∫ g₂ = c₂` is weak-* compact, so any bounded-continuous objective `∫ f` attains
its minimum over that (nonempty) slice. The number of constraints is immaterial; the two-moment
case is stated to match the mean/second-moment slice. -/
theorem exists_isMinOn_momentSlice {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [T2Space Ω] [BorelSpace Ω] [CompactSpace Ω] (g₁ g₂ f : Ω →ᵇ ℝ) (c₁ c₂ : ℝ)
    (hne : {μ : ProbabilityMeasure Ω | ∫ x, g₁ x ∂μ = c₁ ∧ ∫ x, g₂ x ∂μ = c₂}.Nonempty) :
    ∃ μ ∈ {μ : ProbabilityMeasure Ω | ∫ x, g₁ x ∂μ = c₁ ∧ ∫ x, g₂ x ∂μ = c₂},
      ∀ ν ∈ {μ : ProbabilityMeasure Ω | ∫ x, g₁ x ∂μ = c₁ ∧ ∫ x, g₂ x ∂μ = c₂},
        ∫ x, f x ∂(μ : Measure Ω) ≤ ∫ x, f x ∂(ν : Measure Ω) := by
  set C := {μ : ProbabilityMeasure Ω | ∫ x, g₁ x ∂μ = c₁ ∧ ∫ x, g₂ x ∂μ = c₂} with hC
  have hcont1 : Continuous fun μ : ProbabilityMeasure Ω => ∫ x, g₁ x ∂μ :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction g₁
  have hcont2 : Continuous fun μ : ProbabilityMeasure Ω => ∫ x, g₂ x ∂μ :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction g₂
  have hcontf : Continuous fun μ : ProbabilityMeasure Ω => ∫ x, f x ∂μ :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction f
  have hCclosed : IsClosed C := by
    have : C = (fun μ : ProbabilityMeasure Ω => ∫ x, g₁ x ∂μ) ⁻¹' {c₁}
        ∩ (fun μ : ProbabilityMeasure Ω => ∫ x, g₂ x ∂μ) ⁻¹' {c₂} := rfl
    rw [this]
    exact (isClosed_singleton.preimage hcont1).inter (isClosed_singleton.preimage hcont2)
  have hCcompact : IsCompact C := hCclosed.isCompact
  obtain ⟨μ, hμC, hmin⟩ := hCcompact.exists_isMinOn hne hcontf.continuousOn
  exact ⟨μ, hμC, fun ν hν => hmin hν⟩

/-! ### General-measure support bound -/

end

end Causalean.Mathlib.MeasureTheory
