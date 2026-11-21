/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.CountableChaining
import Tengoku.Randomsettheory.RandomSetTheory.EuclideanNetCardinality
import Tengoku.Randomsettheory.RandomSetTheory.EuclideanUnitBall

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Entropy-optimal chaining for bounded Euclidean processes

This file assembles the quantitative part of the usual dyadic chaining
argument on a finite-dimensional Euclidean unit ball.  The confidence spent
at level `k` grows linearly in `k`; the corresponding increment radius decays
as `2⁻ᵏ`.  Their product is summable and gives a bound of order
`sqrt d + sqrt x`, with no `sqrt (log n)` loss.

The probabilistic theorem is formulated for an explicit family of finite
local edge graphs.  This keeps it useful beyond random sets and avoids any
measurability assumption on an uncountable supremum.
-/

open Filter Real Set Finset MeasureTheory Module
open scoped BigOperators ProbabilityTheory ENNReal NNReal Topology

noncomputable section

namespace ProbabilityTheory

/-- Confidence parameter assigned to dyadic level `k`.  Its dimension term
leaves enough room to pay for the product of two adjacent volumetric nets,
whose cardinality is bounded below by `exp (4 d (k+2))` in the theorem.-/
def boundedEuclideanConfidence (d : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  x + (4 * (d : ℝ) + 2) * (k + 2 : ℝ)

/-- Increment threshold for a process whose sub-Gaussian metric is at most
`sigma` times the ambient metric and whose level-`k` edges have length at
most `3 * 2⁻ᵏ`.-/
def boundedEuclideanThreshold (sigma : ℝ) (d : ℕ) (x : ℝ)
    (k : ℕ) : ℝ :=
  3 * sigma * ((1 / 2 : ℝ) ^ k) *
    Real.sqrt (2 * boundedEuclideanConfidence d x k)

theorem boundedEuclideanConfidence_nonneg (d : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ boundedEuclideanConfidence d x k := by
  unfold boundedEuclideanConfidence
  positivity

theorem boundedEuclideanThreshold_nonneg {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (d : ℕ) {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ boundedEuclideanThreshold sigma d x k := by
  unfold boundedEuclideanThreshold
  positivity

/-- Elementary square-root split used in the entropy sum.  We deliberately
use the loose bound `sqrt (k+2) ≤ k+2`; it gives a clean universal constant
and preserves the optimal `sqrt d + sqrt x` scale.-/
theorem sqrt_boundedEuclideanConfidence_le (d : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt (2 * boundedEuclideanConfidence d x k) ≤
      Real.sqrt (2 * x) +
        4 * Real.sqrt (d + 1 : ℝ) * (k + 2 : ℝ) := by
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hD : 0 ≤ (d + 1 : ℝ) := by positivity
  have hk : 0 ≤ (k + 2 : ℝ) := by positivity
  have hkone : 1 ≤ (k + 2 : ℝ) := by
    exact_mod_cast (show 1 ≤ k + 2 by omega)
  have hx2 : 0 ≤ 2 * x := by positivity
  have hsqx := Real.sq_sqrt hx2
  have hsqD := Real.sq_sqrt hD
  have hdim :
      (8 * (d : ℝ) + 4) * (k + 2 : ℝ) ≤
        16 * (d + 1 : ℝ) * (k + 2 : ℝ) ^ 2 := by
    have hcoef : 8 * (d : ℝ) + 4 ≤
        16 * (d + 1 : ℝ) * (k + 2 : ℝ) := by nlinarith
    simpa only [pow_two, mul_assoc] using
      (mul_le_mul_of_nonneg_right hcoef hk)
  have hcross :
      0 ≤ Real.sqrt (2 * x) *
        (4 * Real.sqrt (d + 1 : ℝ) * (k + 2 : ℝ)) := by
    positivity
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · unfold boundedEuclideanConfidence
    nlinarith [Real.sqrt_nonneg (2 * x), Real.sqrt_nonneg (d + 1 : ℝ)]

/-- The dyadic threshold series has the desired dimension/confidence order.
The explicit constant is intentionally conservative.-/
theorem summable_boundedEuclideanThreshold {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (boundedEuclideanThreshold sigma d x) := by
  let q : ℝ := 1 / 2
  have hq : ‖q‖ < 1 := by norm_num [q, Real.norm_eq_abs]
  have hgeom : Summable (fun k : ℕ ↦ q ^ k) :=
    summable_geometric_of_norm_lt_one hq
  have hnat : Summable (fun k : ℕ ↦ (k : ℝ) * q ^ k) :=
    by simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hq
  have hlinear : Summable (fun k : ℕ ↦ (k + 2 : ℝ) * q ^ k) := by
    have htwo := hgeom.mul_left (2 : ℝ)
    convert hnat.add htwo using 1
    ext k
    push_cast
    ring
  have hmajor : Summable (fun k : ℕ ↦
      3 * sigma * (q ^ k) *
        (Real.sqrt (2 * x) +
          4 * Real.sqrt (d + 1 : ℝ) * (k + 2 : ℝ))) := by
    have hfirst := hgeom.mul_left (3 * sigma * Real.sqrt (2 * x))
    have hsecond := hlinear.mul_left
      (12 * sigma * Real.sqrt (d + 1 : ℝ))
    exact (hfirst.add hsecond).congr (fun k ↦ by
      push_cast
      ring)
  apply Summable.of_nonneg_of_le
    (fun k ↦ boundedEuclideanThreshold_nonneg hsigma d hx k)
    (fun k ↦ ?_) hmajor
  unfold boundedEuclideanThreshold
  change 3 * sigma * q ^ k *
      Real.sqrt (2 * boundedEuclideanConfidence d x k) ≤ _
  exact mul_le_mul_of_nonneg_left
    (sqrt_boundedEuclideanConfidence_le d hx k) (by positivity)

/-- Closed upper bound for the whole entropy integral/sum.  In particular it
is `O(sigma * (sqrt x + sqrt d))`, independently of a sample size or a finest
net level.-/
theorem tsum_boundedEuclideanThreshold_le {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∑' k, boundedEuclideanThreshold sigma d x k ≤
      6 * sigma * Real.sqrt (2 * x) +
        72 * sigma * Real.sqrt (d + 1 : ℝ) := by
  let q : ℝ := 1 / 2
  have hq : ‖q‖ < 1 := by norm_num [q, Real.norm_eq_abs]
  have hgeom : HasSum (fun k : ℕ ↦ q ^ k) 2 := by
    have h := hasSum_geometric_of_norm_lt_one hq
    norm_num [q] at h
    exact h
  have hnat : HasSum (fun k : ℕ ↦ (k : ℝ) * q ^ k) 2 := by
    have h := hasSum_coe_mul_geometric_of_norm_lt_one hq
    norm_num [q] at h
    exact h
  have hlinear : HasSum (fun k : ℕ ↦ (k + 2 : ℝ) * q ^ k) 6 := by
    convert hnat.add (hgeom.mul_left (2 : ℝ)) using 1
    · ext k
      push_cast
      ring
    · ring
  have hmajor : HasSum (fun k : ℕ ↦
      3 * sigma * (q ^ k) *
        (Real.sqrt (2 * x) +
          4 * Real.sqrt (d + 1 : ℝ) * (k + 2 : ℝ)))
      (6 * sigma * Real.sqrt (2 * x) +
        72 * sigma * Real.sqrt (d + 1 : ℝ)) := by
    have hfirst := hgeom.mul_left (3 * sigma * Real.sqrt (2 * x))
    have hsecond := hlinear.mul_left
      (12 * sigma * Real.sqrt (d + 1 : ℝ))
    have hsum : HasSum (fun k : ℕ ↦
        3 * sigma * (q ^ k) *
          (Real.sqrt (2 * x) +
            4 * Real.sqrt (d + 1 : ℝ) * (k + 2 : ℝ)))
        (3 * sigma * Real.sqrt (2 * x) * 2 +
          12 * sigma * Real.sqrt (d + 1 : ℝ) * 6) :=
      (hfirst.add hsecond).congr (fun k ↦ by
        push_cast
        ring)
    convert hsum using 1
    ring
  have hthreshold := summable_boundedEuclideanThreshold hsigma d hx
  calc
    ∑' k, boundedEuclideanThreshold sigma d x k ≤
        ∑' k : ℕ, 3 * sigma * (q ^ k) *
          (Real.sqrt (2 * x) +
            4 * Real.sqrt (d + 1 : ℝ) * (k + 2 : ℝ)) := by
      apply hthreshold.tsum_le_tsum
      · intro k
        unfold boundedEuclideanThreshold
        change 3 * sigma * q ^ k *
            Real.sqrt (2 * boundedEuclideanConfidence d x k) ≤ _
        exact mul_le_mul_of_nonneg_left
          (sqrt_boundedEuclideanConfidence_le d hx k) (by positivity)
      · exact hmajor.summable
    _ = 6 * sigma * Real.sqrt (2 * x) +
        72 * sigma * Real.sqrt (d + 1 : ℝ) := hmajor.tsum_eq

/-- The entropy cost corresponding to `boundedEuclideanConfidence`.  The
factor in front is the permitted cardinality of the local edge graph.-/
def boundedEuclideanEntropyCost (d : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  Real.exp (4 * (d : ℝ) * (k + 2 : ℝ)) *
    (2 * Real.exp (-boundedEuclideanConfidence d x k))

theorem boundedEuclideanEntropyCost_eq (d : ℕ) (x : ℝ) (k : ℕ) :
    boundedEuclideanEntropyCost d x k =
      2 * Real.exp (-x) * (Real.exp (-2)) ^ 2 *
        (Real.exp (-2)) ^ k := by
  unfold boundedEuclideanEntropyCost boundedEuclideanConfidence
  have hexponent :
      4 * (d : ℝ) * (k + 2 : ℝ) +
          -(x + (4 * (d : ℝ) + 2) * (k + 2 : ℝ)) =
        -x + ((k + 2 : ℕ) : ℝ) * (-2) := by
    push_cast
    ring
  calc
    Real.exp (4 * (d : ℝ) * (k + 2 : ℝ)) *
        (2 * Real.exp (-(x + (4 * (d : ℝ) + 2) * (k + 2 : ℝ)))) =
      2 * Real.exp (4 * (d : ℝ) * (k + 2 : ℝ) +
        -(x + (4 * (d : ℝ) + 2) * (k + 2 : ℝ))) := by
          rw [Real.exp_add]
          ring
    _ = 2 * Real.exp (-x + ((k + 2 : ℕ) : ℝ) * (-2)) := by
      rw [hexponent]
    _ = 2 * Real.exp (-x) * (Real.exp (-2)) ^ (k + 2) := by
      rw [Real.exp_add, Real.exp_nat_mul]
      ring
    _ = 2 * Real.exp (-x) * (Real.exp (-2)) ^ 2 *
        (Real.exp (-2)) ^ k := by rw [pow_add]; ring

/-- The confidence allocation pays for all dyadic entropy levels.  The
right-hand side is a single `exp (-x)` tail, not a sample-size-dependent
logarithmic penalty.-/
theorem summable_boundedEuclideanEntropyCost (d : ℕ) (x : ℝ) :
    Summable (boundedEuclideanEntropyCost d x) := by
  let q : ℝ := Real.exp (-2)
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    norm_num [q]
  have hgeom : Summable (fun k : ℕ ↦ q ^ k) :=
    summable_geometric_of_norm_lt_one hq
  have hscaled := hgeom.mul_left
    (2 * Real.exp (-x) * q ^ 2)
  exact hscaled.congr (fun k ↦ by
    symm
    simpa only [q] using boundedEuclideanEntropyCost_eq d x k)

theorem tsum_boundedEuclideanEntropyCost_le (d : ℕ) (x : ℝ) :
    ∑' k, boundedEuclideanEntropyCost d x k ≤ Real.exp (-x) := by
  let q : ℝ := Real.exp (-2)
  have hqpos : 0 < q := Real.exp_pos _
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos, Real.exp_lt_one_iff]
    norm_num [q]
  have hqquarter : q ≤ 1 / 4 := by
    have he : Real.exp (-1) < 0.3678794412 := Real.exp_neg_one_lt_d9
    have hqeq : q = Real.exp (-1) ^ 2 := by
      dsimp only [q]
      calc
        Real.exp (-2) = Real.exp ((-1) + (-1)) := by norm_num
        _ = Real.exp (-1) * Real.exp (-1) := Real.exp_add _ _
        _ = Real.exp (-1) ^ 2 := by ring
    rw [hqeq]
    nlinarith [Real.exp_pos (-1)]
  have hsum :
      ∑' k, boundedEuclideanEntropyCost d x k =
        2 * Real.exp (-x) * q ^ 2 * (1 - q)⁻¹ := by
    rw [show (∑' k, boundedEuclideanEntropyCost d x k) =
        ∑' k, (2 * Real.exp (-x) * q ^ 2) * q ^ k by
      apply tsum_congr
      intro k
      simpa only [q] using boundedEuclideanEntropyCost_eq d x k]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq]
  rw [hsum]
  have hden : 0 < 1 - q := by nlinarith
  have hfactor : 2 * q ^ 2 * (1 - q)⁻¹ ≤ 1 := by
    rw [inv_eq_one_div]
    rw [show 2 * q ^ 2 * (1 / (1 - q)) =
      (2 * q ^ 2) / (1 - q) by ring]
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg q]
  calc
    2 * Real.exp (-x) * q ^ 2 * (1 - q)⁻¹ =
        Real.exp (-x) * (2 * q ^ 2 * (1 - q)⁻¹) := by ring
    _ ≤ Real.exp (-x) * 1 :=
      mul_le_mul_of_nonneg_left hfactor (Real.exp_pos _).le
    _ = Real.exp (-x) := mul_one _

variable {Omega T : Type*} [MeasurableSpace Omega] [PseudoMetricSpace T]
  {mu : Measure Omega}

/-- Entropy-optimal countable chaining for a sub-Gaussian process on a
finite-dimensional Euclidean-type index set.

The geometry is exposed through finite local edge graphs.  At level `k`,
all traversed edges have length at most `3 * 2⁻ᵏ`, and their cardinality
is at most `exp (4 d (k+2))`.  `hsubgaussian` is the normalized scalar tail
bound with metric coefficient `sigma`.  Under these assumptions the whole
uncountable process has a tail of order

`sigma * (sqrt x + sqrt (d+1))`

with no logarithm of a truncation or sample size.  The event remains
existential, so its measure is meaningful without first proving that an
uncountable supremum is measurable.-/
theorem measureReal_boundedEuclideanProcess_largeDeviation_le
    [IsProbabilityMeasure mu]
    (Z : Omega → T → ℝ) (N0 : Finset T)
    (edges : ℕ → Finset (T × T)) (proj : ℕ → T → T)
    (d : ℕ) {sigma x : ℝ} (hsigma : 0 ≤ sigma) (hx : 0 ≤ x)
    (hbase : ∀ t, proj 0 t ∈ N0)
    (hedge : ∀ k t, (proj (k + 1) t, proj k t) ∈ edges k)
    (hremainder : ∀ omega t, Tendsto
      (fun m ↦ |Z omega t - Z omega (proj m t)|) atTop (nhds 0))
    (hbaseZero : ∀ omega, ∀ u ∈ N0, Z omega u = 0)
    (hedgeDist : ∀ k, ∀ e ∈ edges k,
      dist e.1 e.2 ≤ 3 * ((1 / 2 : ℝ) ^ k))
    (hedgeCard : ∀ k,
      ((edges k).card : ℝ) ≤
        Real.exp (4 * (d : ℝ) * (k + 2 : ℝ)))
    (hsubgaussian : ∀ k, ∀ e ∈ edges k,
      mu.real {omega |
        sigma * dist e.1 e.2 *
            Real.sqrt (2 * boundedEuclideanConfidence d x k) <
          |Z omega e.1 - Z omega e.2|} ≤
        2 * Real.exp (-boundedEuclideanConfidence d x k)) :
    mu.real {omega | ∃ t,
        6 * sigma * Real.sqrt (2 * x) +
            72 * sigma * Real.sqrt (d + 1 : ℝ) <
          |Z omega t|} ≤
      Real.exp (-x) := by
  let threshold : ℕ → ℝ := boundedEuclideanThreshold sigma d x
  let delta : ℕ → ℝ := fun k ↦
    2 * Real.exp (-boundedEuclideanConfidence d x k)
  have hthresholdSummable : Summable threshold :=
    summable_boundedEuclideanThreshold hsigma d hx
  have hbaseTail : ∀ u ∈ N0,
      mu.real {omega | (0 : ℝ) < |Z omega u|} ≤ 0 := by
    intro u hu
    simp only [hbaseZero _ u hu, abs_zero, lt_self_iff_false,
      Set.ofPred_false, measureReal_empty, le_refl]
  have hedgeTail : ∀ k, ∀ e ∈ edges k,
      mu.real {omega | threshold k < |Z omega e.1 - Z omega e.2|} ≤
        delta k := by
    intro k e he
    have hlocal :
        sigma * dist e.1 e.2 *
            Real.sqrt (2 * boundedEuclideanConfidence d x k) ≤
          threshold k := by
      dsimp only [threshold]
      unfold boundedEuclideanThreshold
      have hsqrt :
          0 ≤ Real.sqrt (2 * boundedEuclideanConfidence d x k) :=
        Real.sqrt_nonneg _
      exact mul_le_mul_of_nonneg_right
        (by
          calc
            sigma * dist e.1 e.2 ≤ sigma * (3 * ((1 / 2 : ℝ) ^ k)) :=
              mul_le_mul_of_nonneg_left (hedgeDist k e he) hsigma
            _ = 3 * sigma * ((1 / 2 : ℝ) ^ k) := by ring)
        hsqrt
    exact (measureReal_mono (by
      intro omega homega
      exact lt_of_le_of_lt hlocal homega)).trans (by
        exact hsubgaussian k e he)
  have hcostPointwise : ∀ k,
      (edges k).card * delta k ≤ boundedEuclideanEntropyCost d x k := by
    intro k
    unfold boundedEuclideanEntropyCost
    dsimp only [delta]
    exact mul_le_mul_of_nonneg_right (hedgeCard k) (by positivity)
  have hcostSummable : Summable fun k ↦ (edges k).card * delta k :=
    Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (Nat.cast_nonneg _) (by positivity))
      hcostPointwise (summable_boundedEuclideanEntropyCost d x)
  have hchain := measureReal_countableChaining_edges_largeDeviation_le
    Z N0 edges proj threshold delta 0 0 hbase hedge hthresholdSummable
      hremainder hcostSummable hbaseTail hedgeTail
  have hchain' :
      mu.real {omega | ∃ t, (∑' k, threshold k) < |Z omega t|} ≤
        ∑' k, (edges k).card * delta k := by
    simpa only [zero_add, Nat.cast_zero, zero_mul, mul_zero, add_zero] using hchain
  calc
    mu.real {omega | ∃ t,
        6 * sigma * Real.sqrt (2 * x) +
            72 * sigma * Real.sqrt (d + 1 : ℝ) < |Z omega t|} ≤
        mu.real {omega | ∃ t, (∑' k, threshold k) < |Z omega t|} := by
      apply measureReal_mono
      rintro omega ⟨t, ht⟩
      refine ⟨t, lt_of_le_of_lt ?_ ht⟩
      exact tsum_boundedEuclideanThreshold_le hsigma d hx
      finiteness
    _ ≤ ∑' k, (edges k).card * delta k := hchain'
    _ ≤ ∑' k, boundedEuclideanEntropyCost d x k :=
      hcostSummable.tsum_le_tsum hcostPointwise
        (summable_boundedEuclideanEntropyCost d x)
    _ ≤ Real.exp (-x) := tsum_boundedEuclideanEntropyCost_le d x

end ProbabilityTheory

namespace RandomSetTheory

/-- Radius of the `k`-th Euclidean net.-/
def dyadicResolution (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

theorem dyadicResolution_pos (k : ℕ) : 0 < dyadicResolution k := by
  unfold dyadicResolution
  positivity

theorem dyadicResolution_le_one (k : ℕ) : dyadicResolution k ≤ 1 := by
  unfold dyadicResolution
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- Simultaneous dyadic volumetric nets of a finite-dimensional unit ball.
The coarsest net is fixed to `{0}`, which anchors processes satisfying
`Z(0)=0`; every finer net enjoys the standard `(3/ε)^d` cardinality bound.-/
theorem exists_unitBall_dyadic_finset_nets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ N : ℕ → Finset E,
      N 0 = {0} ∧
      (∀ k, ∀ v ∈ N k, ‖v‖ ≤ 1) ∧
      (∀ k, ∀ u : E, ‖u‖ ≤ 1 →
        ∃ v ∈ N k, dist u v ≤ dyadicResolution k) ∧
      ∀ k, ((N k).card : ℝ) ≤
        (3 / dyadicResolution k) ^ finrank ℝ E := by
  classical
  have hexists : ∀ k : ℕ, ∃ M : Finset E,
      (∀ v ∈ M, ‖v‖ ≤ 1) ∧
      (∀ u : E, ‖u‖ ≤ 1 →
        ∃ v ∈ M, dist u v ≤ dyadicResolution k) ∧
      (M.card : ℝ) ≤
        (3 / dyadicResolution k) ^ finrank ℝ E := by
    intro k
    exact exists_unitBall_finset_net_card_le_three_div
      (dyadicResolution_pos k) (dyadicResolution_le_one k)
  let M : ℕ → Finset E := fun k ↦ Classical.choose (hexists k)
  let N : ℕ → Finset E := fun k ↦ if k = 0 then {0} else M k
  refine ⟨N, by simp [N], ?_, ?_, ?_⟩
  · intro k v hv
    by_cases hk : k = 0
    · subst k
      simp only [N, ite_eq_left, Finset.mem_singleton] at hv
      subst v
      simp
    · have hvM : v ∈ M k := by simpa [N, hk] using hv
      exact (Classical.choose_spec (hexists k)).1 v hvM
  · intro k u hu
    by_cases hk : k = 0
    · subst k
      refine ⟨0, by simp [N], ?_⟩
      simpa [dyadicResolution, dist_zero_right] using hu
    · obtain ⟨v, hv, huv⟩ :=
        (Classical.choose_spec (hexists k)).2.1 u hu
      exact ⟨v, by simpa [N, hk] using hv, huv⟩
  · intro k
    by_cases hk : k = 0
    · subst k
      simp only [N, ite_eq_left, Finset.card_singleton, Nat.cast_one,
        dyadicResolution, pow_zero, div_one]
      exact one_le_pow₀ (by norm_num)
    · simpa only [N, ite_eq_right hk] using
        (Classical.choose_spec (hexists k)).2.2

/-- Local pairs of adjacent dyadic nets.  Filtering the product by distance
is what keeps every increment at its own dyadic scale.-/
def unitBallLocalDyadicEdges {E : Type*} [PseudoMetricSpace E]
    (N : ℕ → Finset E) (k : ℕ) : Finset (E × E) := by
  classical
  exact (N (k + 1) ×ˢ N k).filter fun e ↦
    dist e.1 e.2 ≤ dyadicResolution (k + 1) + dyadicResolution k

theorem mem_unitBallLocalDyadicEdges_iff
    {E : Type*} [PseudoMetricSpace E] (N : ℕ → Finset E)
    (k : ℕ) (e : E × E) :
    e ∈ unitBallLocalDyadicEdges N k ↔
      e.1 ∈ N (k + 1) ∧ e.2 ∈ N k ∧
        dist e.1 e.2 ≤
          dyadicResolution (k + 1) + dyadicResolution k := by
  classical
  simp [unitBallLocalDyadicEdges, and_assoc]

theorem card_unitBallLocalDyadicEdges_le
    {E : Type*} [PseudoMetricSpace E] (N : ℕ → Finset E) (k : ℕ) :
    (unitBallLocalDyadicEdges N k).card ≤
      (N (k + 1)).card * (N k).card := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_product _ _)

theorem dist_le_three_mul_dyadicResolution_of_mem_localEdges
    {E : Type*} [PseudoMetricSpace E] (N : ℕ → Finset E)
    {k : ℕ} {e : E × E} (he : e ∈ unitBallLocalDyadicEdges N k) :
    dist e.1 e.2 ≤ 3 * dyadicResolution k := by
  have hdist := (mem_unitBallLocalDyadicEdges_iff N k e).1 he |>.2.2
  have hhalf : dyadicResolution (k + 1) =
      (1 / 2 : ℝ) * dyadicResolution k := by
    simp [dyadicResolution, pow_succ, mul_comm]
  rw [hhalf] at hdist
  have hr := (dyadicResolution_pos k).le
  nlinarith

/-- A convenient exponential restatement of the volumetric base
`3 / 2⁻ᵏ`.  The factor `2` is deliberately loose and makes the subsequent
adjacent-product estimate elementary.-/
theorem three_div_dyadicResolution_le_exp (k : ℕ) :
    3 / dyadicResolution k ≤
      Real.exp (2 * (k + 1 : ℝ)) := by
  have he : (3 : ℝ) ≤ Real.exp 2 := by
    have he1 : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith
  have hpow : (2 : ℝ) ^ k ≤ (Real.exp 2) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by linarith : (2 : ℝ) ≤ Real.exp 2) k
  calc
    3 / dyadicResolution k = 3 * (2 : ℝ) ^ k := by
      simp [dyadicResolution, div_eq_mul_inv, inv_pow]
    _ ≤ Real.exp 2 * (Real.exp 2) ^ k :=
      mul_le_mul he hpow (by positivity) (by positivity)
    _ = (Real.exp 2) ^ (k + 1) := by rw [pow_succ']
    _ = Real.exp (2 * (k + 1 : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

/-- Adjacent local edge graphs built from volumetric dyadic nets satisfy the
exponential entropy hypothesis of the generic probabilistic theorem.-/
theorem card_unitBallLocalDyadicEdges_real_le_exp
    {E : Type*} [PseudoMetricSpace E]
    (N : ℕ → Finset E) (d : ℕ)
    (hcard : ∀ j, ((N j).card : ℝ) ≤
      (3 / dyadicResolution j) ^ d) (k : ℕ) :
    ((unitBallLocalDyadicEdges N k).card : ℝ) ≤
      Real.exp (4 * (d : ℝ) * (k + 2 : ℝ)) := by
  have hA : (3 / dyadicResolution (k + 1)) ^ d ≤
      (Real.exp (2 * (k + 2 : ℝ))) ^ d :=
    pow_le_pow_left₀
      (div_nonneg (by norm_num) (dyadicResolution_pos (k + 1)).le)
      (by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
          using three_div_dyadicResolution_le_exp (k + 1)) d
  have hB : (3 / dyadicResolution k) ^ d ≤
      (Real.exp (2 * (k + 1 : ℝ))) ^ d :=
    pow_le_pow_left₀
      (div_nonneg (by norm_num) (dyadicResolution_pos k).le)
      (three_div_dyadicResolution_le_exp k) d
  calc
    ((unitBallLocalDyadicEdges N k).card : ℝ) ≤
        (((N (k + 1)).card * (N k).card : ℕ) : ℝ) := by
      exact_mod_cast card_unitBallLocalDyadicEdges_le N k
    _ = ((N (k + 1)).card : ℝ) * ((N k).card : ℝ) := by push_cast; rfl
    _ ≤ (3 / dyadicResolution (k + 1)) ^ d *
          (3 / dyadicResolution k) ^ d :=
      mul_le_mul (hcard (k + 1)) (hcard k) (Nat.cast_nonneg _)
        (pow_nonneg (div_nonneg (by norm_num)
          (dyadicResolution_pos (k + 1)).le) _)
    _ ≤ (Real.exp (2 * (k + 2 : ℝ))) ^ d *
          (Real.exp (2 * (k + 1 : ℝ))) ^ d :=
      mul_le_mul hA hB
        (pow_nonneg (div_nonneg (by norm_num)
          (dyadicResolution_pos k).le) _)
        (pow_nonneg (Real.exp_pos _).le _)
    _ = Real.exp ((d : ℝ) * (2 * (k + 2 : ℝ)) +
          (d : ℝ) * (2 * (k + 1 : ℝ))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (4 * (d : ℝ) * (k + 2 : ℝ)) := by
      rw [Real.exp_le_exp]
      calc
        (d : ℝ) * (2 * (k + 2 : ℝ)) +
            (d : ℝ) * (2 * (k + 1 : ℝ)) =
          4 * (d : ℝ) * (k + 2 : ℝ) - 2 * (d : ℝ) := by ring
        _ ≤ 4 * (d : ℝ) * (k + 2 : ℝ) :=
          sub_le_self _ (mul_nonneg (by norm_num) (Nat.cast_nonneg d))

/-- Dyadic nets, simultaneous projections and local edge graphs on the
Euclidean unit ball.  This packages all deterministic geometry required by
`measureReal_boundedEuclideanProcess_largeDeviation_le`, except for the
elementary exponential restatement of the displayed volumetric card bound.-/
theorem exists_unitBall_dyadic_chainingData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ (N : ℕ → Finset (EuclideanUnitBall E))
      (proj : ℕ → EuclideanUnitBall E → EuclideanUnitBall E),
      (∀ u ∈ N 0, (u : E) = 0) ∧
      (∀ k, ((N k).card : ℝ) ≤
        (3 / dyadicResolution k) ^ finrank ℝ E) ∧
      (∀ k t, proj k t ∈ N k) ∧
      (∀ k t, dist t (proj k t) ≤ dyadicResolution k) ∧
      (∀ k t, (proj (k + 1) t, proj k t) ∈
        unitBallLocalDyadicEdges N k) ∧
      ∀ t, Tendsto (fun k ↦ dist t (proj k t)) atTop (nhds 0) := by
  classical
  obtain ⟨M, hM0, hMmem, hMcover, hMcard⟩ :=
    exists_unitBall_dyadic_finset_nets (E := E)
  let emb : ∀ k, {v : E // v ∈ M k} ↪ EuclideanUnitBall E := fun k ↦
    ⟨fun v ↦ ⟨v.1, hMmem k v.1 v.2⟩, by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun z : EuclideanUnitBall E ↦ (z : E)) hab⟩
  let N : ℕ → Finset (EuclideanUnitBall E) := fun k ↦
    (M k).attach.map (emb k)
  have hNzero : ∀ u ∈ N 0, (u : E) = 0 := by
    intro u hu
    obtain ⟨v, _hv, hvu⟩ := Finset.mem_map.1 hu
    have hv0 : (v : E) = 0 := by
      have hvM : (v : E) ∈ M 0 := v.property
      simpa [hM0] using hvM
    rw [← hvu]
    exact hv0
  have hNcard : ∀ k, ((N k).card : ℝ) ≤
      (3 / dyadicResolution k) ^ finrank ℝ E := by
    intro k
    simpa only [N, Finset.card_map, Finset.card_attach] using hMcard k
  have hNcover : ∀ k (t : EuclideanUnitBall E),
      ∃ u ∈ N k, dist t u ≤ dyadicResolution k := by
    intro k t
    obtain ⟨v, hvM, htv⟩ := hMcover k (t : E) t.property
    let vM : {w : E // w ∈ M k} := ⟨v, hvM⟩
    refine ⟨emb k vM, ?_, ?_⟩
    · exact Finset.mem_map.2 ⟨vM, Finset.mem_attach _ _, rfl⟩
    · change dist (t : E) v ≤ dyadicResolution k
      exact htv
  let zeroUnit : EuclideanUnitBall E := ⟨0, by simp⟩
  letI : Nonempty (EuclideanUnitBall E) := ⟨zeroUnit⟩
  obtain ⟨proj, hprojMem, hprojNear⟩ :=
    ProbabilityTheory.exists_countableNetProjections N dyadicResolution hNcover
  have hedge : ∀ k t, (proj (k + 1) t, proj k t) ∈
      unitBallLocalDyadicEdges N k := by
    intro k t
    rw [mem_unitBallLocalDyadicEdges_iff]
    refine ⟨hprojMem (k + 1) t, hprojMem k t, ?_⟩
    calc
      dist (proj (k + 1) t) (proj k t) ≤
          dist (proj (k + 1) t) t + dist t (proj k t) := dist_triangle _ _ _
      _ ≤ dyadicResolution (k + 1) + dyadicResolution k :=
        add_le_add (by simpa only [dist_comm] using hprojNear (k + 1) t)
          (hprojNear k t)
  have heps : Tendsto dyadicResolution atTop (nhds 0) := by
    change Tendsto (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) atTop (nhds 0)
    exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      (show |(1 / 2 : ℝ)| < 1 by norm_num)
  have hprojTendsto : ∀ t, Tendsto (fun k ↦ dist t (proj k t))
      atTop (nhds 0) := by
    intro t
    exact squeeze_zero (fun k ↦ dist_nonneg) (fun k ↦ hprojNear k t) heps
  exact ⟨N, proj, hNzero, hNcard, hprojMem, hprojNear, hedge, hprojTendsto⟩

/-- Fully geometric specialization to a continuous sub-Gaussian process on
the unit ball of a finite-dimensional real normed space.  All nets,
projections and local edge graphs are constructed internally from the
volumetric estimate.

The scalar hypothesis is the standard normalized increment tail.  It is
required for every nonnegative confidence parameter so the theorem can
allocate its entropy budget automatically.-/
theorem measureReal_unitBall_subgaussianProcess_largeDeviation_le
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (Z : Omega → EuclideanUnitBall E → ℝ)
    {sigma x : ℝ} (hsigma : 0 ≤ sigma) (hx : 0 ≤ x)
    (hcontinuous : ∀ omega, Continuous (Z omega))
    (hzero : ∀ omega, Z omega ⟨0, by simp⟩ = 0)
    (hsubgaussian : ∀ (s t : EuclideanUnitBall E) (y : ℝ), 0 ≤ y →
      mu.real {omega |
        sigma * dist s t * Real.sqrt (2 * y) <
          |Z omega s - Z omega t|} ≤ 2 * Real.exp (-y)) :
    mu.real {omega | ∃ t : EuclideanUnitBall E,
        6 * sigma * Real.sqrt (2 * x) +
            72 * sigma * Real.sqrt (finrank ℝ E + 1 : ℝ) <
          |Z omega t|} ≤
      Real.exp (-x) := by
  obtain ⟨N, proj, hNzero, hNcard, hprojMem, _hprojNear, hedge,
      hprojDist⟩ := exists_unitBall_dyadic_chainingData (E := E)
  let edges : ℕ → Finset (EuclideanUnitBall E × EuclideanUnitBall E) :=
    unitBallLocalDyadicEdges N
  have hbase : ∀ t, proj 0 t ∈ N 0 := hprojMem 0
  have hbaseZero : ∀ omega, ∀ u ∈ N 0, Z omega u = 0 := by
    intro omega u hu
    have huval : (u : E) = 0 := hNzero u hu
    have hu : u = (⟨0, by simp⟩ : EuclideanUnitBall E) := by
      apply Subtype.ext
      exact huval
    rw [hu]
    exact hzero omega
  have hedgeDist : ∀ k, ∀ e ∈ edges k,
      dist e.1 e.2 ≤ 3 * ((1 / 2 : ℝ) ^ k) := by
    intro k e he
    simpa only [edges, dyadicResolution] using
      dist_le_three_mul_dyadicResolution_of_mem_localEdges N he
  have hedgeCard : ∀ k, ((edges k).card : ℝ) ≤
      Real.exp (4 * (finrank ℝ E : ℝ) * (k + 2 : ℝ)) := by
    intro k
    exact card_unitBallLocalDyadicEdges_real_le_exp N (finrank ℝ E)
      hNcard k
  have hremainder : ∀ omega t, Tendsto
      (fun m ↦ |Z omega t - Z omega (proj m t)|) atTop (nhds 0) := by
    intro omega t
    have hproj : Tendsto (fun m ↦ proj m t) atTop (nhds t) := by
      rw [tendsto_iff_dist_tendsto_zero]
      simpa only [dist_comm] using hprojDist t
    have hZproj : Tendsto (fun m ↦ Z omega (proj m t)) atTop
        (nhds (Z omega t)) := (hcontinuous omega).tendsto t |>.comp hproj
    have hsub : Tendsto (fun m ↦ Z omega t - Z omega (proj m t)) atTop
        (nhds 0) := by
      have hc : Tendsto (fun _m : ℕ ↦ Z omega t) atTop
          (nhds (Z omega t)) := tendsto_const_nhds
      simpa only [sub_self] using hc.sub hZproj
    simpa only [abs_zero] using hsub.abs
  apply ProbabilityTheory.measureReal_boundedEuclideanProcess_largeDeviation_le
    Z (N 0) edges proj (finrank ℝ E) hsigma hx hbase
      (by simpa only [edges] using hedge) hremainder hbaseZero hedgeDist
      hedgeCard
  intro k e he
  exact hsubgaussian e.1 e.2
    (ProbabilityTheory.boundedEuclideanConfidence (finrank ℝ E) x k)
    (ProbabilityTheory.boundedEuclideanConfidence_nonneg (finrank ℝ E) hx k)

end RandomSetTheory
