/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Seed.Analysis.Normed.Algebra.Exponential
import Tengoku.Seed.Analysis.Complex.Exponential
import Tengoku.Seed.Analysis.Convex.Mul
import Tengoku.Seed.Analysis.SpecialFunctions.Exponential
import Tengoku.Seed.Topology.Algebra.InfiniteSum.NatInt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit bounds for tails of the exponential series

The strong-moment Fuk--Nagaev argument splits the exponential series at the
available moment order.  This file isolates the deterministic estimates used
in that split.  In particular, for `x >= 0`,

`sum_{k >= q} x^k / k! <= (x^q / q!) * exp x`.

Keeping this statement independent of probability theory makes it reusable
for ordinary and conditional moment-generating-function estimates.
-/

open Real Finset
open scoped BigOperators

noncomputable section

namespace ProbabilityTheory

/-- Factorials are supermultiplicative after addition, in real
coordinates.-/
theorem factorial_mul_factorial_cast_le_factorial_add_cast (q k : ℕ) :
    (q.factorial : ℝ) * (k.factorial : ℝ) ≤ ((q + k).factorial : ℝ) := by
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (q + k))
    (Nat.factorial_mul_factorial_dvd_factorial_add q k)

/-- Termwise domination used to compare a shifted exponential tail with the
full exponential series.-/
theorem pow_add_div_factorial_add_le_mul_pow_div_factorial
    {x : ℝ} (hx : 0 ≤ x) (q k : ℕ) :
    x ^ (q + k) / ((q + k).factorial : ℝ) ≤
      (x ^ q / (q.factorial : ℝ)) *
        (x ^ k / (k.factorial : ℝ)) := by
  have hfac := factorial_mul_factorial_cast_le_factorial_add_cast q k
  have hfacPos : 0 < (q.factorial : ℝ) * (k.factorial : ℝ) := by
    positivity
  calc
    x ^ (q + k) / ((q + k).factorial : ℝ) =
        (x ^ q * x ^ k) / ((q + k).factorial : ℝ) := by
      rw [pow_add]
    _ ≤ (x ^ q * x ^ k) /
        ((q.factorial : ℝ) * (k.factorial : ℝ)) :=
      div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hx q) (pow_nonneg hx k))
        hfacPos hfac
    _ = (x ^ q / (q.factorial : ℝ)) *
        (x ^ k / (k.factorial : ℝ)) := by
      field_simp

/-- The shifted tail of the real exponential series is summable.-/
theorem summable_expSeries_nat_add (x : ℝ) (q : ℕ) :
    Summable (fun k : ℕ => x ^ (q + k) / ((q + k).factorial : ℝ)) := by
  simpa only [add_comm] using
    ((summable_nat_add_iff q).2 (Real.summable_pow_div_factorial x))

/-- The exact tail of the exponential series starting at degree `q`.

Keeping this object, rather than immediately replacing it by the coarser
Lagrange majorant, is what makes the sharp polynomial term in the
Rio--Marchina argument possible.-/
def expSeriesTail (q : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, x ^ (q + k) / ((q + k).factorial : ℝ)

theorem summable_expSeriesTail (q : ℕ) (x : ℝ) :
    Summable (fun k : ℕ => x ^ (q + k) / ((q + k).factorial : ℝ)) :=
  summable_expSeries_nat_add x q

/-- The exact exponential tail is nonnegative on the nonnegative
half-line.-/
theorem expSeriesTail_nonneg {x : ℝ} (hx : 0 ≤ x) (q : ℕ) :
    0 ≤ expSeriesTail q x := by
  exact tsum_nonneg fun k => by positivity

/-- A tail starting at a positive degree vanishes at zero.-/
@[simp] theorem expSeriesTail_zero {q : ℕ} (hq : q ≠ 0) :
    expSeriesTail q 0 = 0 := by
  simp [expSeriesTail, hq, Nat.add_eq_zero_iff]

/-- Exponential-series tail bound with the exact leading factorial.-/
theorem tsum_pow_add_div_factorial_add_le (x : ℝ) (hx : 0 ≤ x) (q : ℕ) :
    (∑' k : ℕ, x ^ (q + k) / ((q + k).factorial : ℝ)) ≤
      (x ^ q / (q.factorial : ℝ)) * Real.exp x := by
  have hleft := summable_expSeries_nat_add x q
  have hright : Summable (fun k : ℕ =>
      (x ^ q / (q.factorial : ℝ)) *
        (x ^ k / (k.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial x).mul_left
      (x ^ q / (q.factorial : ℝ))
  calc
    (∑' k : ℕ, x ^ (q + k) / ((q + k).factorial : ℝ)) ≤
        ∑' k : ℕ, (x ^ q / (q.factorial : ℝ)) *
          (x ^ k / (k.factorial : ℝ)) :=
      hleft.tsum_le_tsum
        (fun k => pow_add_div_factorial_add_le_mul_pow_div_factorial hx q k)
        hright
    _ = (x ^ q / (q.factorial : ℝ)) *
        (∑' k : ℕ, x ^ k / (k.factorial : ℝ)) := by
      rw [tsum_mul_left]
    _ = (x ^ q / (q.factorial : ℝ)) * Real.exp x := by
      rw [(NormedSpace.expSeries_div_hasSum_exp x).tsum_eq,
        ← Real.exp_eq_exp_ℝ]

/-- Exact decomposition of the exponential into its first `q` terms and its
shifted tail.-/
theorem exp_eq_sum_range_add_tsum_nat_add (x : ℝ) (q : ℕ) :
    Real.exp x =
      (∑ k ∈ range q, x ^ k / (k.factorial : ℝ)) +
        ∑' k : ℕ, x ^ (q + k) / ((q + k).factorial : ℝ) := by
  have hsplit :=
    (Real.summable_pow_div_factorial x).sum_add_tsum_nat_add q
  rw [(NormedSpace.expSeries_div_hasSum_exp x).tsum_eq] at hsplit
  calc
    Real.exp x = NormedSpace.exp x := congrFun Real.exp_eq_exp_ℝ x
    _ = (∑ k ∈ range q, x ^ k / (k.factorial : ℝ)) +
        ∑' k : ℕ, x ^ (k + q) / ((k + q).factorial : ℝ) := hsplit.symm
    _ = (∑ k ∈ range q, x ^ k / (k.factorial : ℝ)) +
        ∑' k : ℕ, x ^ (q + k) / ((q + k).factorial : ℝ) := by
      congr 1
      apply tsum_congr
      intro k
      rw [add_comm]

/-- Exact decomposition of `exp` using the named series tail.-/
theorem exp_eq_sum_range_add_expSeriesTail (x : ℝ) (q : ℕ) :
    Real.exp x =
      (∑ k ∈ range q, x ^ k / (k.factorial : ℝ)) + expSeriesTail q x := by
  simpa only [expSeriesTail] using exp_eq_sum_range_add_tsum_nat_add x q

/-- The exact tail is at most the whole exponential series on the
nonnegative half-line.-/
theorem expSeriesTail_le_exp (x : ℝ) (hx : 0 ≤ x) (q : ℕ) :
    expSeriesTail q x ≤ Real.exp x := by
  have hfinite :
      0 ≤ ∑ k ∈ range q, x ^ k / (k.factorial : ℝ) := by
    positivity
  rw [exp_eq_sum_range_add_expSeriesTail x q]
  exact le_add_of_nonneg_left hfinite

/-- Contraction of the exact exponential tail under a decrease of its
nonnegative argument.  The factor has precisely degree `q`; retaining that
degree is the key advantage over the usual Lagrange remainder.-/
theorem expSeriesTail_mul_le_ratio_pow_mul
    (q : ℕ) {t a y : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hay : a ≤ y) (hy : 0 < y) :
    expSeriesTail q (t * a) ≤
      (a / y) ^ q * expSeriesTail q (t * y) := by
  let r : ℝ := a / y
  let u : ℝ := t * y
  have hr0 : 0 ≤ r := div_nonneg ha hy.le
  have hr1 : r ≤ 1 := (div_le_one hy).2 hay
  have hu : 0 ≤ u := mul_nonneg ht hy.le
  have hta : t * a = r * u := by
    dsimp only [r, u]
    field_simp [ne_of_gt hy]
  have hleft := summable_expSeries_nat_add (t * a) q
  have hright : Summable (fun k : ℕ =>
      r ^ q * (u ^ (q + k) / ((q + k).factorial : ℝ))) :=
    (summable_expSeries_nat_add u q).mul_left (r ^ q)
  have hterm : ∀ k : ℕ,
      (t * a) ^ (q + k) / ((q + k).factorial : ℝ) ≤
        r ^ q * (u ^ (q + k) / ((q + k).factorial : ℝ)) := by
    intro k
    have hrpow : r ^ (q + k) ≤ r ^ q :=
      pow_le_pow_of_le_one hr0 hr1 (Nat.le_add_right q k)
    calc
      (t * a) ^ (q + k) / ((q + k).factorial : ℝ) =
          r ^ (q + k) *
            (u ^ (q + k) / ((q + k).factorial : ℝ)) := by
        rw [hta, mul_pow]
        ring
      _ ≤ r ^ q *
            (u ^ (q + k) / ((q + k).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right hrpow (by positivity)
  unfold expSeriesTail
  calc
    (∑' k : ℕ, (t * a) ^ (q + k) /
        ((q + k).factorial : ℝ)) ≤
        ∑' k : ℕ, r ^ q *
          (u ^ (q + k) / ((q + k).factorial : ℝ)) :=
      hleft.tsum_le_tsum hterm hright
    _ = r ^ q *
        ∑' k : ℕ, u ^ (q + k) / ((q + k).factorial : ℝ) := by
      rw [tsum_mul_left]
    _ = (a / y) ^ q *
        ∑' k : ℕ, (t * y) ^ (q + k) /
          ((q + k).factorial : ℝ) := by rfl

/-- Removing the first degree from an exponential tail costs at most the
factor `x / (n + 1)`.-/
theorem expSeriesTail_succ_le_mul_expSeriesTail
    (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    expSeriesTail (n + 1) x ≤
      (x / (n + 1 : ℕ)) * expSeriesTail n x := by
  have hleft := summable_expSeries_nat_add x (n + 1)
  have hright : Summable (fun k : ℕ =>
      (x / (n + 1 : ℕ)) *
        (x ^ (n + k) / ((n + k).factorial : ℝ))) :=
    (summable_expSeries_nat_add x n).mul_left (x / (n + 1 : ℕ))
  have hterm : ∀ k : ℕ,
      x ^ (n + 1 + k) / ((n + 1 + k).factorial : ℝ) ≤
        (x / (n + 1 : ℕ)) *
          (x ^ (n + k) / ((n + k).factorial : ℝ)) := by
    intro k
    have hden :
        ((n + 1 : ℕ) : ℝ) * ((n + k).factorial : ℝ) ≤
          ((n + k + 1 : ℕ) : ℝ) * ((n + k).factorial : ℝ) := by
      gcongr
      omega
    have hdenPos :
        0 < ((n + 1 : ℕ) : ℝ) * ((n + k).factorial : ℝ) := by
      positivity
    calc
      x ^ (n + 1 + k) / ((n + 1 + k).factorial : ℝ) =
          (x ^ (n + k) * x) /
            (((n + k + 1 : ℕ) : ℝ) * ((n + k).factorial : ℝ)) := by
        rw [show n + 1 + k = n + k + 1 by omega, pow_succ,
          Nat.factorial_succ]
        norm_num
      _ ≤ (x ^ (n + k) * x) /
            (((n + 1 : ℕ) : ℝ) * ((n + k).factorial : ℝ)) :=
        div_le_div_of_nonneg_left
          (mul_nonneg (pow_nonneg hx _) hx) hdenPos hden
      _ = (x / (n + 1 : ℕ)) *
          (x ^ (n + k) / ((n + k).factorial : ℝ)) := by
        field_simp
  unfold expSeriesTail
  calc
    (∑' k : ℕ, x ^ (n + 1 + k) /
        ((n + 1 + k).factorial : ℝ)) ≤
        ∑' k : ℕ, (x / (n + 1 : ℕ)) *
          (x ^ (n + k) / ((n + k).factorial : ℝ)) :=
      hleft.tsum_le_tsum hterm hright
    _ = (x / (n + 1 : ℕ)) *
        ∑' k : ℕ, x ^ (n + k) /
          ((n + k).factorial : ℝ) := by
      rw [tsum_mul_left]

/-- Rio's elementary estimate for the exact exponential tail:
`psi_q(x) <= (x / q) * exp x` for every positive order `q`.-/
theorem expSeriesTail_le_div_mul_exp
    (q : ℕ) (hq : 1 ≤ q) (x : ℝ) (hx : 0 ≤ x) :
    expSeriesTail q x ≤ (x / q) * Real.exp x := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hq
  calc
    expSeriesTail (1 + n) x = expSeriesTail (n + 1) x := by
      rw [add_comm]
    _ ≤ (x / (n + 1 : ℕ)) * expSeriesTail n x :=
      expSeriesTail_succ_le_mul_expSeriesTail n x hx
    _ ≤ (x / (n + 1 : ℕ)) * Real.exp x := by
      exact mul_le_mul_of_nonneg_left (expSeriesTail_le_exp x hx n)
        (div_nonneg hx (by positivity))
    _ = (x / (1 + n : ℕ)) * Real.exp x := by
      rw [add_comm]

/-- The exact exponential tail is convex on the nonnegative half-line.-/
theorem convexOn_expSeriesTail (q : ℕ) :
    ConvexOn ℝ (Set.Ici 0) (expSeriesTail q) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hsx := summable_expSeries_nat_add x q
  have hsy := summable_expSeries_nat_add y q
  have hsax : Summable (fun k : ℕ =>
      a * (x ^ (q + k) / ((q + k).factorial : ℝ))) :=
    hsx.mul_left a
  have hsby : Summable (fun k : ℕ =>
      b * (y ^ (q + k) / ((q + k).factorial : ℝ))) :=
    hsy.mul_left b
  have hright : Summable (fun k : ℕ =>
      a * (x ^ (q + k) / ((q + k).factorial : ℝ)) +
        b * (y ^ (q + k) / ((q + k).factorial : ℝ))) :=
    hsax.add hsby
  have hterm : ∀ k : ℕ,
      (a * x + b * y) ^ (q + k) / ((q + k).factorial : ℝ) ≤
        a * (x ^ (q + k) / ((q + k).factorial : ℝ)) +
          b * (y ^ (q + k) / ((q + k).factorial : ℝ)) := by
    intro k
    have hp := (convexOn_pow (q + k)).2 hx hy ha hb hab
    have hfac : 0 ≤ ((q + k).factorial : ℝ) := by positivity
    calc
      (a * x + b * y) ^ (q + k) / ((q + k).factorial : ℝ) ≤
          (a * x ^ (q + k) + b * y ^ (q + k)) /
            ((q + k).factorial : ℝ) :=
        div_le_div_of_nonneg_right (by simpa only [smul_eq_mul] using hp) hfac
      _ = a * (x ^ (q + k) / ((q + k).factorial : ℝ)) +
          b * (y ^ (q + k) / ((q + k).factorial : ℝ)) := by ring
  unfold expSeriesTail
  calc
    (∑' k : ℕ, (a * x + b * y) ^ (q + k) /
        ((q + k).factorial : ℝ)) ≤
        ∑' k : ℕ, (
          a * (x ^ (q + k) / ((q + k).factorial : ℝ)) +
            b * (y ^ (q + k) / ((q + k).factorial : ℝ))) :=
      (summable_expSeries_nat_add (a * x + b * y) q).tsum_le_tsum
        hterm hright
    _ = a * (∑' k : ℕ,
          x ^ (q + k) / ((q + k).factorial : ℝ)) +
        b * (∑' k : ℕ,
          y ^ (q + k) / ((q + k).factorial : ℝ)) := by
      rw [hsax.tsum_add hsby, tsum_mul_left, tsum_mul_left]

/-- Finite Taylor expansion with an explicit exponentially weighted
remainder, valid on the nonnegative half-line.-/
theorem exp_le_sum_range_add_pow_div_factorial_mul_exp
    (x : ℝ) (hx : 0 ≤ x) (q : ℕ) :
    Real.exp x ≤
      (∑ k ∈ range q, x ^ k / (k.factorial : ℝ)) +
        (x ^ q / (q.factorial : ℝ)) * Real.exp x := by
  calc
    Real.exp x =
        (∑ k ∈ range q, x ^ k / (k.factorial : ℝ)) +
          ∑' k : ℕ, x ^ (q + k) / ((q + k).factorial : ℝ) :=
      exp_eq_sum_range_add_tsum_nat_add x q
    _ ≤ (∑ k ∈ range q, x ^ k / (k.factorial : ℝ)) +
        (x ^ q / (q.factorial : ℝ)) * Real.exp x :=
      add_le_add le_rfl (tsum_pow_add_div_factorial_add_le x hx q)

/-- The quadratic upper Taylor bound needed on the negative half-line.  A
coefficient `3/4` is sufficient globally; no boundedness assumption on `x`
remains.-/
theorem exp_le_one_add_add_three_quarters_sq_of_nonpos
    {x : ℝ} (hx : x ≤ 0) :
    Real.exp x ≤ 1 + x + (3 / 4 : ℝ) * x ^ 2 := by
  by_cases hunit : -1 ≤ x
  · have habs : |x| ≤ 1 := by
      rw [abs_le]
      exact ⟨hunit, hx.trans (by norm_num)⟩
    have h := (abs_le.mp (Real.exp_bound habs (n := 2) (by norm_num))).2
    norm_num [sum_range_succ, Nat.factorial] at h ⊢
    nlinarith
  · have hxlt : x < -1 := lt_of_not_ge hunit
    have hexpMono : Real.exp x ≤ Real.exp (-1) :=
      Real.exp_monotone hxlt.le
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp 1]
    have hhalf : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
      rw [Real.exp_neg]
      calc
        (Real.exp 1)⁻¹ ≤ (2 : ℝ)⁻¹ :=
          (inv_le_inv₀ (Real.exp_pos 1) (by norm_num)).2 htwo
        _ = 1 / 2 := by norm_num
    have hquad : (1 / 2 : ℝ) ≤ 1 + x + (3 / 4 : ℝ) * x ^ 2 := by
      nlinarith [sq_nonneg (3 * x + 2)]
    exact hexpMono.trans (hhalf.trans hquad)

/-- Exact quadratic upper Taylor bound on the negative half-line.  This is
the coefficient used in Rio's one-sided exponential estimate.-/
theorem exp_le_one_add_add_half_sq_of_nonpos
    {x : ℝ} (hx : x ≤ 0) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 := by
  let u : ℝ := -x
  have hu : 0 ≤ u := neg_nonneg.mpr hx
  have hpolyExp : 1 + u + u ^ 2 / 2 ≤ Real.exp u := by
    have h := Real.sum_le_exp_of_nonneg hu 3
    norm_num [sum_range_succ, Nat.factorial] at h ⊢
    nlinarith
  have hpolyPos : 0 < 1 + u + u ^ 2 / 2 := by
    nlinarith [sq_nonneg u]
  have hinv : (Real.exp u)⁻¹ ≤ (1 + u + u ^ 2 / 2)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos u) hpolyPos).2 hpolyExp
  have hprod :
      1 ≤ (1 - u + u ^ 2 / 2) * (1 + u + u ^ 2 / 2) := by
    calc
      (1 : ℝ) ≤ 1 + u ^ 4 / 4 := by
        have hu4 : 0 ≤ u ^ 4 / 4 := by positivity
        linarith
      _ = (1 - u + u ^ 2 / 2) * (1 + u + u ^ 2 / 2) := by ring
  have hrecip : (1 + u + u ^ 2 / 2)⁻¹ ≤ 1 - u + u ^ 2 / 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hpolyPos).2 hprod
  calc
    Real.exp x = (Real.exp u)⁻¹ := by
      have hxu : x = -u := by simp only [u, neg_neg]
      rw [hxu, Real.exp_neg]
    _ ≤ (1 + u + u ^ 2 / 2)⁻¹ := hinv
    _ ≤ 1 - u + u ^ 2 / 2 := hrecip
    _ = 1 + x + x ^ 2 / 2 := by
      dsimp only [u]
      ring

/-- One-sided Taylor majorant.  Only the positive part occurs above order
two; this is the scalar inequality behind moment-sensitive martingale MGF
bounds.-/
def oneSidedExpTaylorBound (q : ℕ) (x : ℝ) : ℝ :=
  1 + x + x ^ 2 / 2 +
    (∑ k ∈ Ico 3 q, (max x 0) ^ k / (k.factorial : ℝ)) +
    (max x 0) ^ q / (q.factorial : ℝ) * Real.exp (max x 0)

/-- The real exponential is bounded by its one-sided Taylor majorant at any
natural order `q >= 3`.-/
theorem exp_le_oneSidedExpTaylorBound
    (q : ℕ) (hq : 3 ≤ q) (x : ℝ) :
    Real.exp x ≤ oneSidedExpTaylorBound q x := by
  by_cases hx : 0 ≤ x
  · have hbase :=
      exp_le_sum_range_add_pow_div_factorial_mul_exp x hx q
    let f : ℕ → ℝ := fun k => x ^ k / (k.factorial : ℝ)
    have hsplit := sum_range_add_sum_Ico f hq
    have hthree : (∑ k ∈ range 3, f k) = 1 + x + x ^ 2 / 2 := by
      simp only [f, sum_range_succ, range_one, sum_singleton, pow_zero,
        Nat.factorial, Nat.cast_one, div_one, pow_one]
      ring
    have hsum : (∑ k ∈ range q, f k) =
        1 + x + x ^ 2 / 2 + ∑ k ∈ Ico 3 q, f k := by
      rw [← hsplit, hthree]
    change Real.exp x ≤ _ at hbase
    rw [hsum] at hbase
    unfold oneSidedExpTaylorBound
    rw [max_eq_left hx]
    calc
      Real.exp x ≤
          1 + x + x ^ 2 / 2 +
            (∑ k ∈ Ico 3 q, x ^ k / (k.factorial : ℝ)) +
            x ^ q / (q.factorial : ℝ) * Real.exp x := hbase
      _ ≤ 1 + x + x ^ 2 / 2 +
            (∑ k ∈ Ico 3 q, x ^ k / (k.factorial : ℝ)) +
            x ^ q / (q.factorial : ℝ) * Real.exp x := le_rfl
  · have hxnonpos : x ≤ 0 := le_of_not_ge hx
    have hbase := exp_le_one_add_add_half_sq_of_nonpos hxnonpos
    have hq0 : q ≠ 0 := by omega
    have hsumzero :
        (∑ k ∈ Ico 3 q, (0 : ℝ) ^ k / (k.factorial : ℝ)) = 0 := by
      apply sum_eq_zero
      intro k hk
      have hk0 : k ≠ 0 := by
        have hk3 := (mem_Ico.mp hk).1
        omega
      simp [hk0]
    unfold oneSidedExpTaylorBound
    rw [max_eq_right hxnonpos, hsumzero, zero_pow hq0]
    simp only [zero_div, zero_mul, add_zero]
    exact hbase

end ProbabilityTheory
