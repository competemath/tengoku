/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.KStatistic

/-!
# Mean-one two-point systems

This file develops the two-point reduction used in the formal proof of
Theorem 2.1.  It records the canonical parametrization

`Yᵢ ∈ {1 - γᵢ, 1 + βᵢ}`,  `P(Yᵢ = 1 + βᵢ) = γᵢ / (γᵢ + βᵢ)`

and proves the required Boolean-lattice monotonicity.  The latter is obtained
directly from the coordinatewise antitonicity of the exponential Dirichlet
statistic.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace Feige

section Parameters

/-- Probability of the high value in a mean-one two-point law. -/
noncomputable def highProbability (γ β : ℝ) : ℝ :=
  γ / (γ + β)

/-- The low value in the mean-one two-point parametrization. -/
def lowValue (γ : ℝ) : ℝ := 1 - γ

/-- The high value in the mean-one two-point parametrization. -/
def highValue (β : ℝ) : ℝ := 1 + β

/--
@isnad1 id=le.2h2v.s5.19c6c0538822 from=translated src=- shape=42f03e2c vocab=cb4f5fe3
-/
theorem highProbability_nonneg {γ β : ℝ} (hγ : 0 ≤ γ) (hβ : 0 < β) :
    0 ≤ highProbability γ β := by
  exact div_nonneg hγ (add_pos_of_nonneg_of_pos hγ hβ).le

/--
@isnad1 id=le.2h2v.s5.88596906985d from=translated src=- shape=df10c736 vocab=cb4f5fe3
-/
theorem highProbability_le_one {γ β : ℝ} (hγ : 0 ≤ γ) (hβ : 0 < β) :
    highProbability γ β ≤ 1 := by
  rw [highProbability, div_le_one (add_pos_of_nonneg_of_pos hγ hβ)]
  linarith

/-- The complementary probability in symmetric form.
@isnad1 id=eq.1h2v.s5.7401eda64dc0 from=translated src=- shape=3230021d vocab=9ee0c633
-/
theorem one_sub_highProbability {γ β : ℝ} (h : γ + β ≠ 0) :
    1 - highProbability γ β = β / (γ + β) := by
  rw [highProbability]
  field_simp
  ring

/-- The parametrized two-point law has mean exactly one.
@isnad1 id=eq.1h2v.s6.c6e28a1d8d45 from=translated src=- shape=def18136 vocab=7b3ea521
-/
theorem twoPoint_mean_one {γ β : ℝ} (h : γ + β ≠ 0) :
    highProbability γ β * highValue β +
        (1 - highProbability γ β) * lowValue γ = 1 := by
  rw [one_sub_highProbability h]
  simp only [highProbability, highValue, lowValue]
  field_simp
  ring

end Parameters

section BooleanLattice

variable {ι : Type*} [Fintype ι]

/-- The vector encoded by a high set `S`: coordinates in `S` take their
high value, and all remaining coordinates take their low value. -/
noncomputable def twoPointVector (γ β : ι → ℝ) (S : Set ι) (i : ι) : ℝ :=
  by
    classical
    exact if i ∈ S then highValue (β i) else lowValue (γ i)

/-- The Dirichlet statistic at the two-point vector encoded by `S`. -/
noncomputable def twoPointK (γ β : ι → ℝ) (S : Set ι) : ℝ :=
  dirichletK (twoPointVector γ β S)

omit [Fintype ι] in
/--
@isnad1 id=monotone.2h3v.s6.9b68ffc6b3fc from=translated src=- shape=8e6eb3b0 vocab=e574eb4f
-/
theorem twoPointVector_mono {γ β : ι → ℝ}
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i) :
    Monotone (twoPointVector γ β : Set ι → ι → ℝ) := by
  classical
  intro A B hAB i
  by_cases hiA : i ∈ A
  · have hiB : i ∈ B := hAB hiA
    simp [twoPointVector, hiA, hiB]
  · by_cases hiB : i ∈ B
    · simp only [twoPointVector, ite_eq_right hiA, ite_eq_left hiB, lowValue, highValue]
      linarith [hγ i, hβ i]
    · simp [twoPointVector, hiA, hiB]

section ProductHighSet

variable [DecidableEq ι]

/-- Product-law mass of a high set. -/
def highSetMass (p : ι → ℝ) (S : Finset ι) : ℝ :=
  (∏ i ∈ S, p i) * ∏ i ∈ Finset.univ \ S, (1 - p i)

/--
@isnad1 id=le.2h3v.s5.c15f93bca7ba from=translated src=- shape=79708094 vocab=ef459e2a
-/
theorem highSetMass_nonneg {p : ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (S : Finset ι) :
    0 ≤ highSetMass p S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg fun i _ ↦ hp0 i
  · exact Finset.prod_nonneg fun i _ ↦ sub_nonneg.mpr (hp1 i)

/-- The product masses over all Boolean-lattice states sum to one.
@isnad1 id=eq.0h2v.s5.510c9c472e04 from=translated src=- shape=bc438088 vocab=e2412584
-/
theorem sum_highSetMass (p : ι → ℝ) :
    (∑ S ∈ Finset.univ.powerset, highSetMass p S) = 1 := by
  simp only [highSetMass]
  rw [← Finset.prod_add]
  simp

/-- Finset-indexed version of `Kₘ(S)`, convenient for finite products and
maximal-chain constructions. -/
noncomputable def twoPointKFinset (γ β : ι → ℝ) (S : Finset ι) : ℝ :=
  twoPointK γ β (S : Set ι)

/-- Coordinatewise high probabilities in the two-point parametrization. -/
noncomputable def twoPointHighProbability (γ β : ι → ℝ) (i : ι) : ℝ :=
  highProbability (γ i) (β i)

/-- Rejection probability under the independent two-point product law,
written as a finite sum over high sets. -/
noncomputable def twoPointRejectionMass
    (γ β : ι → ℝ) (α : ℝ) : ℝ := by
  classical
  exact ∑ S ∈ Finset.univ.powerset.filter
      (fun S ↦ twoPointKFinset γ β S ≤ α),
    highSetMass (twoPointHighProbability γ β) S

omit [Fintype ι] [DecidableEq ι] in
/--
@isnad1 id=le.2h4v.s5.6fc458762877 from=translated src=- shape=4b1e3c85 vocab=0df740d6
-/
theorem twoPointHighProbability_nonneg {γ β : ι → ℝ}
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 < β i) (i : ι) :
    0 ≤ twoPointHighProbability γ β i :=
  highProbability_nonneg (hγ i) (hβ i)

omit [Fintype ι] [DecidableEq ι] in
/--
@isnad1 id=le.2h4v.s5.432ee930e40b from=translated src=- shape=4e26eaf3 vocab=0df740d6
-/
theorem twoPointHighProbability_le_one {γ β : ι → ℝ}
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 < β i) (i : ι) :
    twoPointHighProbability γ β i ≤ 1 :=
  highProbability_le_one (hγ i) (hβ i)

/--
@isnad1 id=le.2h4v.s6.cc6c27394321 from=translated src=- shape=14a55487 vocab=589a3b99
-/
theorem twoPointRejectionMass_nonneg {γ β : ι → ℝ} {α : ℝ}
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 < β i) :
    0 ≤ twoPointRejectionMass γ β α := by
  classical
  unfold twoPointRejectionMass
  exact Finset.sum_nonneg fun S _ ↦ highSetMass_nonneg
    (twoPointHighProbability_nonneg hγ hβ)
    (twoPointHighProbability_le_one hγ hβ) S

/--
@isnad1 id=le.2h4v.s6.9f0bd5d03ace from=translated src=- shape=5fd174fc vocab=589a3b99
-/
theorem twoPointRejectionMass_le_one {γ β : ι → ℝ} {α : ℝ}
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 < β i) :
    twoPointRejectionMass γ β α ≤ 1 := by
  classical
  unfold twoPointRejectionMass
  calc
    (∑ S ∈ Finset.univ.powerset.filter
          (fun S ↦ twoPointKFinset γ β S ≤ α),
        highSetMass (twoPointHighProbability γ β) S) ≤
        ∑ S ∈ Finset.univ.powerset,
          highSetMass (twoPointHighProbability γ β) S := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro S _ _
        exact highSetMass_nonneg
          (twoPointHighProbability_nonneg hγ hβ)
          (twoPointHighProbability_le_one hγ hβ) S
    _ = 1 := sum_highSetMass _

end ProductHighSet

end BooleanLattice

end Feige
