import Tengoku.PaperCLean.PaperC.Probability.ArratiaGoldsteinGordonInput
import Tengoku.Seed.Analysis.SpecialFunctions.Exp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact finite auxiliary thinning and Laplace identities

This module isolates the finite probability calculation used in Section
14.2.  For a finite family of sites and retention probabilities `q i`, it
constructs the independent Bernoulli product PMF and computes the probability
that no active site is retained.

At the manuscript choice `q i = 1 - exp (-g i)`, the answer is exactly
`exp (-∑_{i active} g i)`.  This is the finite conditional void/Laplace
identity.  No Riemann-sum limit or vague-convergence claim is made here.
-/

namespace PaperC
namespace SpatialThinningFinite

open scoped BigOperators

open ArratiaGoldsteinGordonInput

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- One-coordinate Bernoulli weight.-/
def bernoulliWeight (q : ι → ℝ) (i : ι) (b : Bool) : ℝ :=
  if b = true then q i else 1 - q i

/-- Independent, possibly inhomogeneous, finite Bernoulli product law.-/
noncomputable def bernoulliProductPMF
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1) :
    FinitePMF (ι → Bool) where
  prob ξ := ∏ i, bernoulliWeight q i (ξ i)
  nonneg ξ := by
    apply Finset.prod_nonneg
    intro i _hi
    unfold bernoulliWeight
    split_ifs
    · exact hq0 i
    · linarith [hq1 i]
  sum_prob := by
    classical
    change
      (∑ ξ : ι → Bool,
        ∏ i, bernoulliWeight q i (ξ i)) = 1
    rw [← Fintype.prod_sum]
    apply Finset.prod_eq_one
    intro i _hi
    simp [bernoulliWeight]

/-- No active coordinate is retained by the auxiliary thinning.-/
def NoRetainedActive
    (active : ι → Bool) (ξ : ι → Bool) : Prop :=
  ∀ i, active i = true → ξ i = false

/-- Number of coordinates which are both active and retained.-/
noncomputable def thinnedCount
    (active ξ : ι → Bool) : ℕ := by
  classical
  exact
    (Finset.univ.filter fun i ↦
      active i = true ∧ ξ i = true).card

omit [DecidableEq ι] in
/--
@isnad1 id=iff.0h3v.s4.9f18f0c8157c from=translated src=- shape=0eccb7df vocab=58d0d978
-/
theorem thinnedCount_eq_zero_iff
    (active ξ : ι → Bool) :
    thinnedCount active ξ = 0 ↔
      NoRetainedActive active ξ := by
  classical
  unfold thinnedCount NoRetainedActive
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i hiActive
    have hnot : ¬ξ i = true := by
      intro hiTrue
      exact h (Finset.mem_univ i) ⟨hiActive, hiTrue⟩
    cases hi : ξ i
    · rfl
    · exact (hnot hi).elim
  · intro h i _hi
    push Not
    intro hiActive hiTrue
    have := h i hiActive
    simp_all

omit [DecidableEq ι] in
/--
Pointwise factorization of the indicator of the void event against the
Bernoulli product weight.
@isnad1 id=eq.0h4v.s6.76646a44fd6e from=translated src=- shape=e08881ca vocab=8874292b
-/
theorem voidIndicator_mul_product_eq
    (q : ι → ℝ) (active ξ : ι → Bool) :
    (if NoRetainedActive active ξ then
        ∏ i, bernoulliWeight q i (ξ i)
      else 0) =
      ∏ i,
        if active i = true ∧ ξ i = true then
          0
        else bernoulliWeight q i (ξ i) := by
  classical
  by_cases hvoid : NoRetainedActive active ξ
  · rw [ite_eq_left hvoid]
    apply Finset.prod_congr rfl
    intro i _hi
    rw [ite_eq_right]
    intro h
    have := hvoid i h.1
    simp_all
  · rw [ite_eq_right hvoid]
    unfold NoRetainedActive at hvoid
    push Not at hvoid
    obtain ⟨i, hiActive, hiRetained⟩ := hvoid
    have hiTrue : ξ i = true := by
      cases h : ξ i
      · exact (hiRetained h).elim
      · rfl
    symm
    apply (Finset.prod_eq_zero (Finset.mem_univ i))
    rw [ite_eq_left]
    exact ⟨hiActive, hiTrue⟩

/--
Exact conditional void probability for an arbitrary deterministic active
configuration.
@isnad1 id=eq.2h3v.s6.a3c7ccb1009e from=translated src=- shape=7f3a12c2 vocab=9241ed38
-/
theorem eventProbability_noRetainedActive_eq_prod
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1)
    (active : ι → Bool) :
    eventProbability
        (bernoulliProductPMF q hq0 hq1)
        (NoRetainedActive active) =
      ∏ i, if active i = true then 1 - q i else 1 := by
  classical
  unfold eventProbability
  simp only [bernoulliProductPMF]
  simp_rw [voidIndicator_mul_product_eq q active]
  let f : ι → Bool → ℝ :=
    fun i b ↦
      if active i = true ∧ b = true then
        0
      else bernoulliWeight q i b
  calc
    (∑ x : ι → Bool,
        ∏ i,
          if active i = true ∧ x i = true then
            0
          else bernoulliWeight q i (x i)) =
        ∑ x : ι → Bool, ∏ i, f i (x i) := rfl
    _ = ∏ i, ∑ b, f i b :=
      (Fintype.prod_sum f).symm
    _ = ∏ i, if active i = true then 1 - q i else 1 := by
      apply Finset.prod_congr rfl
      intro i _hi
      by_cases hactive : active i = true
      · simp [f, hactive, bernoulliWeight]
      · have hfalse : active i = false := by
          cases h : active i
          · rfl
          · exact (hactive h).elim
        simp [f, hfalse, bernoulliWeight]

/-- Manuscript retention probability `q_i = 1 - exp(-g_i)`.-/
noncomputable def exponentialRetention
    (g : ι → ℝ) (i : ι) : ℝ :=
  1 - Real.exp (-g i)

omit [Fintype ι] [DecidableEq ι] in
/--
@isnad1 id=le.1h3v.s5.96cbda560532 from=translated src=- shape=186a0309 vocab=0ecf225b
-/
theorem exponentialRetention_nonneg
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) (i : ι) :
    0 ≤ exponentialRetention g i := by
  unfold exponentialRetention
  exact sub_nonneg.mpr
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg i)))

omit [Fintype ι] [DecidableEq ι] in
/--
@isnad1 id=le.0h3v.s4.94c1f3e04b62 from=translated src=- shape=9734203e vocab=0ecf225b
-/
theorem exponentialRetention_le_one
    (g : ι → ℝ) (i : ι) :
    exponentialRetention g i ≤ 1 := by
  unfold exponentialRetention
  linarith [Real.exp_pos (-g i)]

/--
Finite conditional Laplace identity:

`P(no retained active site | active) = exp(-∑ active g)`.
@isnad1 id=eq.1h3v.s6.5b9e5679c147 from=translated src=- shape=4909dda2 vocab=1ab502df
-/
theorem eventProbability_noRetainedActive_exponential_eq
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i)
    (active : ι → Bool) :
    eventProbability
        (bernoulliProductPMF
          (exponentialRetention g)
          (fun i ↦ exponentialRetention_nonneg g hg i)
          (fun i ↦ exponentialRetention_le_one g i))
        (NoRetainedActive active) =
      Real.exp
        (-(∑ i, if active i = true then g i else 0)) := by
  rw [eventProbability_noRetainedActive_eq_prod]
  calc
    (∏ i, if active i = true then
          1 - exponentialRetention g i else 1) =
        ∏ i, Real.exp
          (if active i = true then -g i else 0) := by
      apply Finset.prod_congr rfl
      intro i _hi
      by_cases hactive : active i = true
      · simp [hactive, exponentialRetention]
      · simp [hactive]
    _ =
        Real.exp
          (∑ i, if active i = true then -g i else 0) := by
      rw [Real.exp_sum]
    _ =
        Real.exp
          (-(∑ i, if active i = true then g i else 0)) := by
      congr 1
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hactive : active i = true <;>
        simp [hactive]

/--
Equivalent count form of the finite Laplace identity, matching the manuscript
event `W_g = 0`.
@isnad1 id=eq.1h3v.s6.9564a8c89ff3 from=translated src=- shape=83f67b97 vocab=d54197b1
-/
theorem eventProbability_thinnedCount_zero_exponential_eq
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i)
    (active : ι → Bool) :
    eventProbability
        (bernoulliProductPMF
          (exponentialRetention g)
          (fun i ↦ exponentialRetention_nonneg g hg i)
          (fun i ↦ exponentialRetention_le_one g i))
        (fun ξ ↦ thinnedCount active ξ = 0) =
      Real.exp
        (-(∑ i, if active i = true then g i else 0)) := by
  have hevent :
      (fun ξ : ι → Bool ↦ thinnedCount active ξ = 0) =
        NoRetainedActive active := by
    funext ξ
    apply propext
    exact thinnedCount_eq_zero_iff active ξ
  rw [hevent]
  exact eventProbability_noRetainedActive_exponential_eq g hg active

omit [DecidableEq ι] in
/--
The weighted Poisson parameter of a thinned finite family is bounded by the
unthinned parameter.
@isnad1 id=le.2h3v.s6.9d23b6eeffb0 from=translated src=- shape=ba010c63 vocab=9c3f0da6
-/
theorem sum_retention_mul_le_sum
    (q p : ι → ℝ)
    (hq1 : ∀ i, q i ≤ 1)
    (hp : ∀ i, 0 ≤ p i) :
    (∑ i, q i * p i) ≤ ∑ i, p i := by
  apply Finset.sum_le_sum
  intro i _hi
  exact mul_le_of_le_one_left (hp i) (hq1 i)

omit [DecidableEq ι] in
/--
The pair-weighted Stein--Chen summand is likewise dominated coordinatewise.
@isnad1 id=le.3h3v.s7.451e8bd8d5e2 from=translated src=- shape=96ef238e vocab=9c3f0da6
-/
theorem sum_pair_retention_mul_le_sum
    (q : ι → ℝ) (p : ι → ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1)
    (hp : ∀ i j, 0 ≤ p i j) :
    (∑ i, ∑ j, q i * q j * p i j) ≤
      ∑ i, ∑ j, p i j := by
  apply Finset.sum_le_sum
  intro i _hi
  apply Finset.sum_le_sum
  intro j _hj
  have hqq0 : 0 ≤ q i * q j :=
    mul_nonneg (hq0 i) (hq0 j)
  have hqq1 : q i * q j ≤ 1 := by
    nlinarith [hq0 i, hq0 j, hq1 i, hq1 j]
  nlinarith [hp i j]

end

end SpatialThinningFinite
end PaperC
