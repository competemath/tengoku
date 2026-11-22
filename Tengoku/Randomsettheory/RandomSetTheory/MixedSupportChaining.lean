/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.CountableChaining

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Entropy-optimal chaining for mixed Bernstein support processes

This file assembles the stable countable-chaining API for a continuous
anchored process whose increments have the mixed tail

`σ₂ d(s,t) sqrt (2 y) + 2 σ₁ d(s,t) y`.

At dyadic level `k`, local edges have length at most `3 · 2⁻ᵏ` and their
cardinality is at most `exp (4 d (k+2))`.  A linearly increasing confidence
budget pays this entropy while both metric contributions remain summable.
The resulting deviation has the form

`σ₂ (sqrt d + sqrt x) + σ₁ (d + x)`

with explicit constants and no logarithm of a sample size or truncation
level.  The geometric edge data are explicit arguments, so this module does
not depend on `BoundedSupportChaining`.
-/

open Filter Real Set Finset MeasureTheory Module
open scoped BigOperators ProbabilityTheory ENNReal NNReal Topology

noncomputable section

namespace ProbabilityTheory

/-- Confidence allocated to dyadic level `k`.  Its dimension term pays for
the product of two adjacent volumetric nets.-/
def mixedEuclideanConfidence (d : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  x + (4 * (d : ℝ) + 2) * (k + 2 : ℝ)

/-- Level threshold for mixed Bernstein metrics `σ₂ dist` and `σ₁ dist`.-/
def mixedEuclideanThreshold (σ₂ σ₁ : ℝ) (d : ℕ) (x : ℝ)
    (k : ℕ) : ℝ :=
  3 * σ₂ * ((1 / 2 : ℝ) ^ k) *
      Real.sqrt (2 * mixedEuclideanConfidence d x k) +
    6 * σ₁ * ((1 / 2 : ℝ) ^ k) * mixedEuclideanConfidence d x k

/--
@isnad1 id=le.1h3v.s4.e3f0a25f6d1f from=translated src=- shape=144bfabc vocab=7f6b9dae
-/
theorem mixedEuclideanConfidence_nonneg (d : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ mixedEuclideanConfidence d x k := by
  unfold mixedEuclideanConfidence
  positivity

/--
@isnad1 id=le.3h5v.s5.c203d34afb44 from=translated src=- shape=17dd1c97 vocab=1cda453b
-/
theorem mixedEuclideanThreshold_nonneg {σ₂ σ₁ : ℝ}
    (hσ₂ : 0 ≤ σ₂) (hσ₁ : 0 ≤ σ₁) (d : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ mixedEuclideanThreshold σ₂ σ₁ d x k := by
  unfold mixedEuclideanThreshold
  have hc : 0 ≤ mixedEuclideanConfidence d x k :=
    mixedEuclideanConfidence_nonneg d hx k
  have hp : 0 ≤ (1 / 2 : ℝ) ^ k := pow_nonneg (by norm_num) _
  have hs : 0 ≤ Real.sqrt (2 * mixedEuclideanConfidence d x k) :=
    Real.sqrt_nonneg _
  exact add_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hσ₂) hp) hs)
    (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hσ₁) hp) hc)

/-- Conservative square-root split used in the `γ₂` part of the sum.
@isnad1 id=le.1h3v.s6.0e5980fef04f from=translated src=- shape=38ad0db2 vocab=fb2ad3f3
-/
theorem sqrt_mixedEuclideanConfidence_le (d : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt (2 * mixedEuclideanConfidence d x k) ≤
      Real.sqrt (2 * x) +
        4 * Real.sqrt (d + 1 : ℝ) * (k + 2 : ℝ) := by
  have hD : 0 ≤ (d + 1 : ℝ) := by positivity
  have hk : 0 ≤ (k + 2 : ℝ) := by positivity
  have hkone : 1 ≤ (k + 2 : ℝ) := by
    exact_mod_cast (show 1 ≤ k + 2 by omega)
  have hx2 : 0 ≤ 2 * x := by positivity
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
  · unfold mixedEuclideanConfidence
    nlinarith [Real.sq_sqrt hx2, Real.sq_sqrt hD, hcross,
      Real.sqrt_nonneg (2 * x), Real.sqrt_nonneg (d + 1 : ℝ)]

private def mixedEuclideanMajorant (σ₂ σ₁ : ℝ) (d : ℕ) (x : ℝ)
    (k : ℕ) : ℝ :=
  3 * σ₂ * ((1 / 2 : ℝ) ^ k) *
      (Real.sqrt (2 * x) +
        4 * Real.sqrt (d + 1 : ℝ) * (k + 2 : ℝ)) +
    6 * σ₁ * ((1 / 2 : ℝ) ^ k) *
      (x + (4 * (d : ℝ) + 2) * (k + 2 : ℝ))

private theorem mixedEuclideanThreshold_le_majorant
    {σ₂ σ₁ : ℝ} (hσ₂ : 0 ≤ σ₂) (_hσ₁ : 0 ≤ σ₁)
    (d : ℕ) {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    mixedEuclideanThreshold σ₂ σ₁ d x k ≤
      mixedEuclideanMajorant σ₂ σ₁ d x k := by
  unfold mixedEuclideanThreshold mixedEuclideanMajorant
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (sqrt_mixedEuclideanConfidence_le d hx k) (by positivity)
  · rw [mixedEuclideanConfidence]

private theorem hasSum_mixedEuclideanMajorant
    (σ₂ σ₁ : ℝ) (d : ℕ) (x : ℝ) :
    HasSum (mixedEuclideanMajorant σ₂ σ₁ d x)
      (6 * σ₂ * Real.sqrt (2 * x) +
        72 * σ₂ * Real.sqrt (d + 1 : ℝ) +
        12 * σ₁ * x + 36 * σ₁ * (4 * (d : ℝ) + 2)) := by
  let q : ℝ := 1 / 2
  have hq : ‖q‖ < 1 := by norm_num [q, Real.norm_eq_abs]
  have hgeom : HasSum (fun k : ℕ => q ^ k) 2 := by
    have h := hasSum_geometric_of_norm_lt_one hq
    norm_num [q] at h
    exact h
  have hnat : HasSum (fun k : ℕ => (k : ℝ) * q ^ k) 2 := by
    have h := hasSum_coe_mul_geometric_of_norm_lt_one hq
    norm_num [q] at h
    exact h
  have hlinear : HasSum (fun k : ℕ => (k + 2 : ℝ) * q ^ k) 6 := by
    convert hnat.add (hgeom.mul_left (2 : ℝ)) using 1
    · ext k
      ring
    · ring
  have h1 := hgeom.mul_left (3 * σ₂ * Real.sqrt (2 * x))
  have h2 := hlinear.mul_left (12 * σ₂ * Real.sqrt (d + 1 : ℝ))
  have h3 := hgeom.mul_left (6 * σ₁ * x)
  have h4 := hlinear.mul_left (6 * σ₁ * (4 * (d : ℝ) + 2))
  have hsum := ((h1.add h2).add h3).add h4
  have hfun : mixedEuclideanMajorant σ₂ σ₁ d x = fun k : ℕ =>
      3 * σ₂ * Real.sqrt (2 * x) * q ^ k +
        12 * σ₂ * Real.sqrt (d + 1 : ℝ) * (((k : ℝ) + 2) * q ^ k) +
        6 * σ₁ * x * q ^ k +
        6 * σ₁ * (4 * (d : ℝ) + 2) * (((k : ℝ) + 2) * q ^ k) := by
    funext k
    dsimp only [mixedEuclideanMajorant, q]
    ring
  have hsum' : HasSum (mixedEuclideanMajorant σ₂ σ₁ d x)
      ((3 * σ₂ * Real.sqrt (2 * x)) * 2 +
        (12 * σ₂ * Real.sqrt (d + 1 : ℝ)) * 6 +
        (6 * σ₁ * x) * 2 +
        (6 * σ₁ * (4 * (d : ℝ) + 2)) * 6) := by
    rw [hfun]
    exact hsum
  convert hsum' using 1
  ring

/--
@isnad1 id=summable.3h4v.s5.c274878e8698 from=translated src=- shape=cbadd400 vocab=391f5a6a
-/
theorem summable_mixedEuclideanThreshold {σ₂ σ₁ : ℝ}
    (hσ₂ : 0 ≤ σ₂) (hσ₁ : 0 ≤ σ₁)
    (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (mixedEuclideanThreshold σ₂ σ₁ d x) := by
  apply Summable.of_nonneg_of_le
    (fun k => mixedEuclideanThreshold_nonneg hσ₂ hσ₁ d hx k)
    (fun k => mixedEuclideanThreshold_le_majorant hσ₂ hσ₁ d hx k)
    (hasSum_mixedEuclideanMajorant σ₂ σ₁ d x).summable

/-- Closed bound for the mixed entropy sum.  The constants are deliberately
conservative; their important feature is the optimal dependence on `d,x`.
@isnad1 id=le.3h4v.s7.f52c10b81b26 from=translated src=- shape=c3bcd134 vocab=4a6ba6ae
-/
theorem tsum_mixedEuclideanThreshold_le {σ₂ σ₁ : ℝ}
    (hσ₂ : 0 ≤ σ₂) (hσ₁ : 0 ≤ σ₁)
    (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∑' k, mixedEuclideanThreshold σ₂ σ₁ d x k ≤
      6 * σ₂ * Real.sqrt (2 * x) +
        72 * σ₂ * Real.sqrt (d + 1 : ℝ) +
        12 * σ₁ * x + 144 * σ₁ * (d + 1 : ℝ) := by
  have hthreshold := summable_mixedEuclideanThreshold hσ₂ hσ₁ d hx
  have hmajor := hasSum_mixedEuclideanMajorant σ₂ σ₁ d x
  calc
    ∑' k, mixedEuclideanThreshold σ₂ σ₁ d x k ≤
        ∑' k, mixedEuclideanMajorant σ₂ σ₁ d x k :=
      hthreshold.tsum_le_tsum
        (fun k => mixedEuclideanThreshold_le_majorant hσ₂ hσ₁ d hx k)
        hmajor.summable
    _ = 6 * σ₂ * Real.sqrt (2 * x) +
        72 * σ₂ * Real.sqrt (d + 1 : ℝ) +
        12 * σ₁ * x + 36 * σ₁ * (4 * (d : ℝ) + 2) := hmajor.tsum_eq
    _ ≤ 6 * σ₂ * Real.sqrt (2 * x) +
        72 * σ₂ * Real.sqrt (d + 1 : ℝ) +
        12 * σ₁ * x + 144 * σ₁ * (d + 1 : ℝ) := by
      nlinarith [hσ₁]

/-- Entropy cost associated with `mixedEuclideanConfidence`.-/
def mixedEuclideanEntropyCost (d : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  Real.exp (4 * (d : ℝ) * (k + 2 : ℝ)) *
    (2 * Real.exp (-mixedEuclideanConfidence d x k))

/--
@isnad1 id=eq.0h3v.s6.25968a759eae from=translated src=- shape=ee2bfeb1 vocab=28771aa5
-/
theorem mixedEuclideanEntropyCost_eq (d : ℕ) (x : ℝ) (k : ℕ) :
    mixedEuclideanEntropyCost d x k =
      2 * Real.exp (-x) * (Real.exp (-2)) ^ 2 *
        (Real.exp (-2)) ^ k := by
  unfold mixedEuclideanEntropyCost mixedEuclideanConfidence
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

/--
@isnad1 id=summable.0h2v.s4.35de13bf811f from=translated src=- shape=27343aff vocab=a3344ba6
-/
theorem summable_mixedEuclideanEntropyCost (d : ℕ) (x : ℝ) :
    Summable (mixedEuclideanEntropyCost d x) := by
  let q : ℝ := Real.exp (-2)
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    norm_num [q]
  have hgeom : Summable (fun k : ℕ => q ^ k) :=
    summable_geometric_of_norm_lt_one hq
  have hscaled := hgeom.mul_left (2 * Real.exp (-x) * q ^ 2)
  exact hscaled.congr (fun k => by
    simpa only [q] using (mixedEuclideanEntropyCost_eq d x k).symm)

/--
@isnad1 id=le.0h2v.s4.70d7b9bc8a45 from=translated src=- shape=92528953 vocab=c8e17ba9
-/
theorem tsum_mixedEuclideanEntropyCost_le (d : ℕ) (x : ℝ) :
    ∑' k, mixedEuclideanEntropyCost d x k ≤ Real.exp (-x) := by
  let q : ℝ := Real.exp (-2)
  have hqpos : 0 < q := Real.exp_pos _
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos, Real.exp_lt_one_iff]
    norm_num [q]
  have hqquarter : q ≤ 1 / 4 := by
    have he : Real.exp (-1) < 0.3678794412 := Real.exp_neg_one_lt_d9
    have hqeq : q = Real.exp (-1) ^ 2 := by
      dsimp only [q]
      rw [pow_two, ← Real.exp_add]
      norm_num
    rw [hqeq]
    nlinarith [Real.exp_pos (-1)]
  have hsum :
      ∑' k, mixedEuclideanEntropyCost d x k =
        2 * Real.exp (-x) * q ^ 2 * (1 - q)⁻¹ := by
    rw [show (∑' k, mixedEuclideanEntropyCost d x k) =
        ∑' k, (2 * Real.exp (-x) * q ^ 2) * q ^ k by
      apply tsum_congr
      intro k
      simpa only [q] using mixedEuclideanEntropyCost_eq d x k]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq]
  rw [hsum]
  have hden : 0 < 1 - q := by nlinarith
  have hfactor : 2 * q ^ 2 * (1 - q)⁻¹ ≤ 1 := by
    calc
      2 * q ^ 2 * (1 - q)⁻¹ = (2 * q ^ 2) / (1 - q) := by
        rw [div_eq_mul_inv]
      _ ≤ 1 := (div_le_iff₀ hden).2 (by nlinarith [sq_nonneg q])
  calc
    2 * Real.exp (-x) * q ^ 2 * (1 - q)⁻¹ =
        Real.exp (-x) * (2 * q ^ 2 * (1 - q)⁻¹) := by ring
    _ ≤ Real.exp (-x) * 1 :=
      mul_le_mul_of_nonneg_left hfactor (Real.exp_pos _).le
    _ = Real.exp (-x) := mul_one _

variable {Ω T : Type*} [MeasurableSpace Ω] [PseudoMetricSpace T]
  {μ : Measure Ω}

/-- Countable Euclidean chaining for a continuous anchored mixed-tail
process, formulated over explicit local edge graphs.

No independence between edges is used.  The tail hypothesis is exactly the
Bernstein mixed metric bound, and the existential deviation event avoids a
measurability assumption on an uncountable supremum.
@isnad1 id=le.10h11v.s9.27cdac0a225f from=translated src=- shape=2704bc13 vocab=05caaeba
-/
theorem measureReal_mixedEuclideanProcess_largeDeviation_le
    [IsProbabilityMeasure μ]
    (Z : Ω → T → ℝ) (N0 : Finset T)
    (edges : ℕ → Finset (T × T)) (proj : ℕ → T → T)
    (d : ℕ) {σ₂ σ₁ x : ℝ}
    (hσ₂ : 0 ≤ σ₂) (hσ₁ : 0 ≤ σ₁) (hx : 0 ≤ x)
    (hbase : ∀ t, proj 0 t ∈ N0)
    (hedge : ∀ k t, (proj (k + 1) t, proj k t) ∈ edges k)
    (hremainder : ∀ ω t, Tendsto
      (fun m => |Z ω t - Z ω (proj m t)|) atTop (nhds 0))
    (hbaseZero : ∀ ω, ∀ u ∈ N0, Z ω u = 0)
    (hedgeDist : ∀ k, ∀ e ∈ edges k,
      dist e.1 e.2 ≤ 3 * ((1 / 2 : ℝ) ^ k))
    (hedgeCard : ∀ k,
      ((edges k).card : ℝ) ≤
        Real.exp (4 * (d : ℝ) * (k + 2 : ℝ)))
    (hmixedTail : ∀ k, ∀ e ∈ edges k,
      μ.real {ω |
        σ₂ * dist e.1 e.2 *
              Real.sqrt (2 * mixedEuclideanConfidence d x k) +
            2 * σ₁ * dist e.1 e.2 * mixedEuclideanConfidence d x k <
          |Z ω e.1 - Z ω e.2|} ≤
        2 * Real.exp (-mixedEuclideanConfidence d x k)) :
    μ.real {ω | ∃ t,
        6 * σ₂ * Real.sqrt (2 * x) +
            72 * σ₂ * Real.sqrt (d + 1 : ℝ) +
            12 * σ₁ * x + 144 * σ₁ * (d + 1 : ℝ) <
          |Z ω t|} ≤
      Real.exp (-x) := by
  let threshold : ℕ → ℝ := mixedEuclideanThreshold σ₂ σ₁ d x
  let delta : ℕ → ℝ := fun k =>
    2 * Real.exp (-mixedEuclideanConfidence d x k)
  have hthresholdSummable : Summable threshold :=
    summable_mixedEuclideanThreshold hσ₂ hσ₁ d hx
  have hbaseTail : ∀ u ∈ N0,
      μ.real {ω | (0 : ℝ) < |Z ω u|} ≤ 0 := by
    intro u hu
    simp only [hbaseZero _ u hu, abs_zero, lt_self_iff_false,
      Set.ofPred_false, measureReal_empty, le_refl]
  have hedgeTail : ∀ k, ∀ e ∈ edges k,
      μ.real {ω | threshold k < |Z ω e.1 - Z ω e.2|} ≤
        delta k := by
    intro k e he
    have hc : 0 ≤ mixedEuclideanConfidence d x k :=
      mixedEuclideanConfidence_nonneg d hx k
    have hlocal :
        σ₂ * dist e.1 e.2 *
              Real.sqrt (2 * mixedEuclideanConfidence d x k) +
            2 * σ₁ * dist e.1 e.2 * mixedEuclideanConfidence d x k ≤
          threshold k := by
      dsimp only [threshold]
      unfold mixedEuclideanThreshold
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (by
            calc
              σ₂ * dist e.1 e.2 ≤ σ₂ * (3 * ((1 / 2 : ℝ) ^ k)) :=
                mul_le_mul_of_nonneg_left (hedgeDist k e he) hσ₂
              _ = 3 * σ₂ * ((1 / 2 : ℝ) ^ k) := by ring)
          (Real.sqrt_nonneg _)
      · have hcoef : 2 * σ₁ * dist e.1 e.2 ≤
            6 * σ₁ * ((1 / 2 : ℝ) ^ k) := by
          calc
            2 * σ₁ * dist e.1 e.2 ≤
                2 * σ₁ * (3 * ((1 / 2 : ℝ) ^ k)) :=
              mul_le_mul_of_nonneg_left (hedgeDist k e he) (by positivity)
            _ = 6 * σ₁ * ((1 / 2 : ℝ) ^ k) := by ring
        exact mul_le_mul_of_nonneg_right hcoef hc
    exact (measureReal_mono (by
      intro ω hω
      exact lt_of_le_of_lt hlocal hω)).trans (hmixedTail k e he)
  have hcostPointwise : ∀ k,
      (edges k).card * delta k ≤ mixedEuclideanEntropyCost d x k := by
    intro k
    unfold mixedEuclideanEntropyCost
    dsimp only [delta]
    exact mul_le_mul_of_nonneg_right (hedgeCard k) (by positivity)
  have hcostSummable : Summable fun k => (edges k).card * delta k :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (Nat.cast_nonneg _) (by positivity))
      hcostPointwise (summable_mixedEuclideanEntropyCost d x)
  have hchain := measureReal_countableChaining_edges_largeDeviation_le
    Z N0 edges proj threshold delta 0 0 hbase hedge hthresholdSummable
      hremainder hcostSummable hbaseTail hedgeTail
  have hchain' :
      μ.real {ω | ∃ t, (∑' k, threshold k) < |Z ω t|} ≤
        ∑' k, (edges k).card * delta k := by
    simpa only [zero_add, Nat.cast_zero, zero_mul, mul_zero, add_zero] using hchain
  calc
    μ.real {ω | ∃ t,
        6 * σ₂ * Real.sqrt (2 * x) +
            72 * σ₂ * Real.sqrt (d + 1 : ℝ) +
            12 * σ₁ * x + 144 * σ₁ * (d + 1 : ℝ) <
          |Z ω t|} ≤
        μ.real {ω | ∃ t, (∑' k, threshold k) < |Z ω t|} := by
      apply measureReal_mono _ (measure_ne_top μ _)
      rintro ω ⟨t, ht⟩
      refine ⟨t, lt_of_le_of_lt ?_ ht⟩
      exact tsum_mixedEuclideanThreshold_le hσ₂ hσ₁ d hx
    _ ≤ ∑' k, (edges k).card * delta k := hchain'
    _ ≤ ∑' k, mixedEuclideanEntropyCost d x k :=
      hcostSummable.tsum_le_tsum hcostPointwise
        (summable_mixedEuclideanEntropyCost d x)
    _ ≤ Real.exp (-x) := tsum_mixedEuclideanEntropyCost_le d x

/-- Continuous-process interface for the preceding chaining theorem.  The
projections converge to every index point, so path continuity discharges the
infinite remainder.  The mixed tail is assumed for every pair and every
nonnegative confidence level; the entropy allocation is then automatic.
@isnad1 id=le.11h11v.s9.1080f71825fc from=translated src=- shape=8d19c9b2 vocab=068f6edf
-/
theorem measureReal_mixedEuclideanContinuousProcess_largeDeviation_le
    [IsProbabilityMeasure μ]
    (Z : Ω → T → ℝ) (N0 : Finset T)
    (edges : ℕ → Finset (T × T)) (proj : ℕ → T → T)
    (d : ℕ) {σ₂ σ₁ x : ℝ}
    (hσ₂ : 0 ≤ σ₂) (hσ₁ : 0 ≤ σ₁) (hx : 0 ≤ x)
    (hcontinuous : ∀ ω, Continuous (Z ω))
    (hbase : ∀ t, proj 0 t ∈ N0)
    (hedge : ∀ k t, (proj (k + 1) t, proj k t) ∈ edges k)
    (hproj : ∀ t, Tendsto (fun k => proj k t) atTop (nhds t))
    (hbaseZero : ∀ ω, ∀ u ∈ N0, Z ω u = 0)
    (hedgeDist : ∀ k, ∀ e ∈ edges k,
      dist e.1 e.2 ≤ 3 * ((1 / 2 : ℝ) ^ k))
    (hedgeCard : ∀ k,
      ((edges k).card : ℝ) ≤
        Real.exp (4 * (d : ℝ) * (k + 2 : ℝ)))
    (hmixedTail : ∀ s t (y : ℝ), 0 ≤ y →
      μ.real {ω |
        σ₂ * dist s t * Real.sqrt (2 * y) +
            2 * σ₁ * dist s t * y < |Z ω s - Z ω t|} ≤
        2 * Real.exp (-y)) :
    μ.real {ω | ∃ t,
        6 * σ₂ * Real.sqrt (2 * x) +
            72 * σ₂ * Real.sqrt (d + 1 : ℝ) +
            12 * σ₁ * x + 144 * σ₁ * (d + 1 : ℝ) <
          |Z ω t|} ≤
      Real.exp (-x) := by
  have hremainder : ∀ ω t, Tendsto
      (fun m => |Z ω t - Z ω (proj m t)|) atTop (nhds 0) := by
    intro ω t
    have hZproj : Tendsto (fun m => Z ω (proj m t)) atTop
        (nhds (Z ω t)) := (hcontinuous ω).tendsto t |>.comp (hproj t)
    have hsub : Tendsto (fun m => Z ω t - Z ω (proj m t)) atTop
        (nhds 0) := by
      have hc : Tendsto (fun _m : ℕ => Z ω t) atTop
          (nhds (Z ω t)) := tendsto_const_nhds
      simpa only [sub_self] using hc.sub hZproj
    simpa only [abs_zero] using hsub.abs
  apply measureReal_mixedEuclideanProcess_largeDeviation_le
    Z N0 edges proj d hσ₂ hσ₁ hx hbase hedge hremainder hbaseZero
      hedgeDist hedgeCard
  intro k e he
  exact hmixedTail e.1 e.2 (mixedEuclideanConfidence d x k)
    (mixedEuclideanConfidence_nonneg d hx k)

end ProbabilityTheory
