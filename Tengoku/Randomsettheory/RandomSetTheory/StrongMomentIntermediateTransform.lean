/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentChernoff
import Tengoku.Randomsettheory.RandomSetTheory.BernsteinChernoff
import Tengoku.Seed.Algebra.Order.Field.GeomSum
import Tengoku.Seed.Analysis.Complex.ExponentialBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rio's intermediate strong-moment transform

This file contains the deterministic finite-series estimates used in
Rio's proof for moment orders `q > 3`.  It is kept separate from the
probabilistic MGF construction.
-/

open Real Set Finset
open scoped BigOperators

noncomputable section

namespace ProbabilityTheory

/-- The elementary factorial estimate behind the Bernstein majorant:
`k! >= 2 * 3^(k-2)` for `k >= 2`.
@isnad1 id=le.1h1v.s5.304ff81a40e1 from=translated src=- shape=48170ec0 vocab=c9343037
-/
theorem two_mul_three_pow_sub_le_factorial {k : ℕ} (hk : 2 ≤ k) :
    2 * 3 ^ (k - 2) ≤ k.factorial := by
  rcases hk.eq_or_lt with rfl | hk
  · norm_num
  · have hk3 : 3 ≤ k := by omega
    have h := Nat.factorial_mul_pow_sub_le_factorial hk3
    have hsub : k - 2 = (k - 3) + 1 := by omega
    rw [hsub, pow_succ]
    norm_num [Nat.factorial] at h
    calc
      2 * (3 ^ (k - 3) * 3) = 3 ^ (k - 3) * 6 := by ring
      _ ≤ k.factorial := by simpa [mul_comm] using h

/-- Reindexing the powers which occur in the intermediate-moment
polynomial.
@isnad1 id=eq.1h2v.s6.98e331b57f47 from=translated src=- shape=2129fc5e vocab=7de29fe7
-/
theorem sum_Ico_three_pow_sub_two_eq
    (q : ℕ) (hq : 3 ≤ q) (r : ℝ) :
    (∑ k ∈ Ico 3 q, r ^ (k - 2)) =
      ∑ j ∈ Ico 1 (q - 2), r ^ j := by
  have h := Finset.sum_Ico_add
    (fun k : ℕ => r ^ (k - 2)) 1 (q - 2) 2
  simpa [Nat.sub_add_cancel (show 2 ≤ q by omega), Nat.add_sub_cancel_left]
    using h.symm

/-- A finite intermediate geometric sum is bounded by its infinite
counterpart.
@isnad1 id=le.3h2v.s6.0006efe0399c from=translated src=- shape=723428e6 vocab=b05b30e6
-/
theorem sum_Ico_three_pow_sub_two_le
    (q : ℕ) (hq : 3 ≤ q) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑ k ∈ Ico 3 q, r ^ (k - 2)) ≤ r / (1 - r) := by
  rw [sum_Ico_three_pow_sub_two_eq q hq r]
  simpa using
    (geom_sum_Ico_le_of_lt_one (x := r) (m := 1) (n := q - 2) hr hr1)

/-- A term of the intermediate polynomial is dominated by the
corresponding term in the Bernstein geometric series.
@isnad1 id=le.5h5v.s7.c8d8a21630e7 from=translated src=- shape=e61a38cb vocab=cf2bf199
-/
theorem intermediate_term_le_bernstein_geometric
    {k : ℕ} (hk : 2 ≤ k) {V c t A : ℝ}
    (hV : 0 ≤ V) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hA_le : A ≤ V * c ^ (k - 2)) :
    t ^ k / (k.factorial : ℝ) * A ≤
      gaussianChernoffExponent V t * (c * t / 3) ^ (k - 2) := by
  have hfacNat := two_mul_three_pow_sub_le_factorial hk
  have hfac : (2 : ℝ) * 3 ^ (k - 2) ≤ (k.factorial : ℝ) := by
    exact_mod_cast hfacNat
  have hdiv :
      t ^ k / (k.factorial : ℝ) ≤
        t ^ k / ((2 : ℝ) * 3 ^ (k - 2)) :=
    div_le_div_of_nonneg_left (pow_nonneg ht k) (by positivity) hfac
  calc
    t ^ k / (k.factorial : ℝ) * A ≤
        t ^ k / (k.factorial : ℝ) * (V * c ^ (k - 2)) :=
      mul_le_mul_of_nonneg_left hA_le
        (div_nonneg (pow_nonneg ht k) (by positivity))
    _ ≤ t ^ k / ((2 : ℝ) * 3 ^ (k - 2)) *
        (V * c ^ (k - 2)) :=
      mul_le_mul_of_nonneg_right hdiv
        (mul_nonneg hV (pow_nonneg hc (k - 2)))
    _ = gaussianChernoffExponent V t * (c * t / 3) ^ (k - 2) := by
      unfold gaussianChernoffExponent
      have hpow : t ^ k = t ^ 2 * t ^ (k - 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow, mul_div_assoc, div_pow]
      ring

/-- The whole intermediate polynomial is bounded by the nonconstant part
of the Bernstein geometric series.
@isnad1 id=le.6h5v.s7.bbc564346318 from=translated src=- shape=e1b21709 vocab=1c30f1db
-/
theorem strongMomentIntermediateExponent_le_bernstein_geometric
    (q : ℕ) (hq : 3 ≤ q) {V Q c t : ℝ}
    (hV : 0 ≤ V) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hr : c * t / 3 < 1)
    (hcoeff : ∀ k ∈ Finset.Ico 3 q,
      interpolatedStrongMomentCoefficient q V Q k ≤
        V * c ^ (k - 2)) :
    strongMomentIntermediateExponent q V Q t ≤
      gaussianChernoffExponent V t *
        ((c * t / 3) / (1 - c * t / 3)) := by
  have hr0 : 0 ≤ c * t / 3 := by positivity
  have hgeom := sum_Ico_three_pow_sub_two_le q hq hr0 hr
  unfold strongMomentIntermediateExponent
  calc
    (∑ k ∈ Ico 3 q,
        t ^ k / (k.factorial : ℝ) *
          interpolatedStrongMomentCoefficient q V Q k) ≤
      ∑ k ∈ Ico 3 q,
        gaussianChernoffExponent V t * (c * t / 3) ^ (k - 2) := by
      exact sum_le_sum fun k hk =>
        intermediate_term_le_bernstein_geometric
          (by have := (mem_Ico.mp hk).1; omega) hV hc ht (hcoeff k hk)
    _ = gaussianChernoffExponent V t *
        (∑ k ∈ Ico 3 q, (c * t / 3) ^ (k - 2)) := by
      rw [Finset.mul_sum]
    _ ≤ gaussianChernoffExponent V t *
        ((c * t / 3) / (1 - c * t / 3)) :=
      mul_le_mul_of_nonneg_left hgeom
        (gaussianChernoffExponent_nonneg hV)

/-- Rio's finite Gaussian-plus-intermediate exponent is dominated by the
rational Bernstein exponent whenever its interpolated coefficients have
the expected geometric form.
@isnad1 id=le.6h5v.s7.7b7949430bb6 from=translated src=- shape=43400f9f vocab=880a92e2
-/
theorem gaussian_add_strongMomentIntermediateExponent_le_bernstein
    (q : ℕ) (hq : 3 ≤ q) {V Q c t : ℝ}
    (hV : 0 ≤ V) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hr : c * t / 3 < 1)
    (hcoeff : ∀ k ∈ Finset.Ico 3 q,
      interpolatedStrongMomentCoefficient q V Q k ≤
        V * c ^ (k - 2)) :
    gaussianChernoffExponent V t +
        strongMomentIntermediateExponent q V Q t ≤
      bernsteinRationalExponent V c t := by
  have hmid := strongMomentIntermediateExponent_le_bernstein_geometric
    q hq hV hc ht hr hcoeff
  have hden : 0 < 1 - c * t / 3 := sub_pos.mpr hr
  have hden3 : 3 - t * c ≠ 0 := by nlinarith
  calc
    gaussianChernoffExponent V t +
        strongMomentIntermediateExponent q V Q t ≤
      gaussianChernoffExponent V t +
        gaussianChernoffExponent V t *
          ((c * t / 3) / (1 - c * t / 3)) := add_le_add le_rfl hmid
    _ = bernsteinRationalExponent V c t := by
      unfold gaussianChernoffExponent bernsteinRationalExponent
      field_simp [hden.ne', hden3]
      ring

/-- In the normalization `Q = 1`, Rio's interpolated coefficient is a
geometric sequence with ratio `V^(-1/(q-2))`.
@isnad1 id=eq.3h3v.s7.6eb97e00a589 from=translated src=- shape=0ff978c4 vocab=886ab4db
-/
theorem interpolatedStrongMomentCoefficient_one_eq_geometric
    {q k : ℕ} (hq : 3 ≤ q) (hk : 2 ≤ k)
    {V : ℝ} (hV : 0 < V) :
    interpolatedStrongMomentCoefficient q V 1 k =
      V * (V ^ (-(1 / ((q : ℝ) - 2)))) ^ (k - 2) := by
  have hden : (q : ℝ) - 2 ≠ 0 := by
    have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hweight :
      strongMomentSecondWeight q k =
        1 + (-(1 / ((q : ℝ) - 2))) * ((k - 2 : ℕ) : ℝ) := by
    unfold strongMomentSecondWeight
    rw [Nat.cast_sub hk]
    field_simp [hden]
    ring
  unfold interpolatedStrongMomentCoefficient
  rw [hweight, Real.rpow_add hV]
  simp only [one_rpow, mul_one, Real.rpow_one]
  rw [Real.rpow_mul hV.le, Real.rpow_natCast]

/-- Equivalent root form of the normalized interpolation coefficient.
@isnad1 id=eq.3h3v.s6.1ea1b2b20668 from=translated src=- shape=bf146b31 vocab=5b57cd57
-/
theorem interpolatedStrongMomentCoefficient_one_eq_root_pow
    {q k : ℕ} (hq : 3 ≤ q) (hkq : k ≤ q)
    {V : ℝ} (hV : 0 < V) :
    interpolatedStrongMomentCoefficient q V 1 k =
      (V ^ (1 / ((q : ℝ) - 2))) ^ (q - k) := by
  have hden : (q : ℝ) - 2 ≠ 0 := by
    have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hweight :
      strongMomentSecondWeight q k =
        (1 / ((q : ℝ) - 2)) * ((q - k : ℕ) : ℝ) := by
    unfold strongMomentSecondWeight
    rw [Nat.cast_sub hkq]
    field_simp [hden]
  unfold interpolatedStrongMomentCoefficient
  rw [hweight, Real.rpow_mul hV.le, Real.rpow_natCast]
  simp

/-- Pointwise normalized form of Rio's inequality preceding (3.21).
@isnad1 id=le.4h3v.s7.c235f70fc811 from=translated src=- shape=3743eea1 vocab=cd39047a
-/
theorem gaussian_add_strongMomentIntermediateExponent_one_le_bernstein
    (q : ℕ) (hq : 3 ≤ q) {V t : ℝ}
    (hV : 0 < V) (ht : 0 ≤ t)
    (hr : V ^ (-(1 / ((q : ℝ) - 2))) * t / 3 < 1) :
    gaussianChernoffExponent V t +
        strongMomentIntermediateExponent q V 1 t ≤
      bernsteinRationalExponent V
        (V ^ (-(1 / ((q : ℝ) - 2)))) t := by
  let c : ℝ := V ^ (-(1 / ((q : ℝ) - 2)))
  have hc : 0 ≤ c := Real.rpow_nonneg hV.le _
  apply gaussian_add_strongMomentIntermediateExponent_le_bernstein
    q hq hV.le hc ht (by simpa only [c] using hr)
  intro k hk
  have hkBounds := Finset.mem_Ico.mp hk
  rw [interpolatedStrongMomentCoefficient_one_eq_geometric hq
    (by omega) hV]

/-- The canonical Bernstein parameter lies strictly below the pole.
@isnad1 id=lt.3h3v.s6.fcdb824ae5a4 from=translated src=- shape=7ce8185d vocab=52bb9d2b
-/
theorem bernsteinOptimalParameter_scale_lt_three
    {V c x : ℝ} (hV : 0 < V) (hc : 0 ≤ c) (hx : 0 < x) :
    c * bernsteinOptimalParameter V c x / 3 < 1 := by
  let a : ℝ := Real.sqrt (2 * x / V)
  have ha : 0 < a := Real.sqrt_pos.2 (div_pos (by positivity) hV)
  have hd : 0 < 1 + c * a / 3 := by positivity
  have hfrac : c * a / (1 + c * a / 3) < 3 := by
    apply (div_lt_iff₀ hd).2
    nlinarith
  change c * (a / (1 + c * a / 3)) / 3 < 1
  calc
    c * (a / (1 + c * a / 3)) / 3 =
        (c * a / (1 + c * a / 3)) / 3 := by ring
    _ < 1 := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 3)).2 (by
      simpa using hfrac)

/-- Rio's transform estimate (3.21), in the normalization `Q = 1`.
@isnad1 id=le.3h3v.s7.26179336d5ee from=translated src=- shape=7adf0cc6 vocab=7b639513
-/
theorem chernoffTransform_gaussian_add_intermediate_one_le
    (q : ℕ) (hq : 3 ≤ q) {V x : ℝ}
    (hV : 0 < V) (hx : 0 < x) :
    chernoffTransform
        (fun t => gaussianChernoffExponent V t +
          strongMomentIntermediateExponent q V 1 t) x ≤
      Real.sqrt (2 * V * x) +
        V ^ (-(1 / ((q : ℝ) - 2))) * x / 3 := by
  let c : ℝ := V ^ (-(1 / ((q : ℝ) - 2)))
  have hc : 0 ≤ c := Real.rpow_nonneg hV.le _
  apply chernoffTransform_le_sqrt_add_linear_of_le_bernsteinOptimal
    hV hc hx
  · intro t ht
    exact add_nonneg
      (gaussianChernoffExponent_nonneg hV.le)
      (strongMomentIntermediateExponent_nonneg q hV.le (by norm_num) ht.le)
  · apply gaussian_add_strongMomentIntermediateExponent_one_le_bernstein
      q hq hV (bernsteinOptimalParameter_pos hV hc hx).le
    simpa only [c] using bernsteinOptimalParameter_scale_lt_three hV hc hx

/-- The second branch in Rio's transform decomposition (3.15): optimize
the Gaussian-plus-intermediate polynomial by Bernstein and the exact tail
separately.
@isnad1 id=le.5h4v.s7.70b90a1fdab7 from=translated src=- shape=42d41594 vocab=da260669
-/
theorem chernoffTransform_rioStrongMomentExponent_one_second_branch_le
    (q : ℕ) (hq : 3 ≤ q) {V y x : ℝ}
    (hV : 0 < V) (hy : 0 < y) (hx : 0 < x)
    (hscale : Real.exp x ≤ y ^ q) :
    chernoffTransform (rioStrongMomentExponent q V 1 y) x ≤
      Real.sqrt (2 * V * x) +
        V ^ (-(1 / ((q : ℝ) - 2))) * x / 3 +
          (1 + 1 / (q : ℝ)) * y := by
  let gm : ℝ → ℝ := fun t =>
    gaussianChernoffExponent V t +
      strongMomentIntermediateExponent q V 1 t
  have hgmConv : ConvexOn ℝ (Set.Ici 0) gm := by
    have hg := convexOn_gaussianChernoffExponent hV.le
    have hm := convexOn_strongMomentIntermediateExponent q
      (Q := 1) hV.le (by norm_num)
    refine ⟨convex_Ici 0, ?_⟩
    intro s hs t ht a b ha hb hab
    have hgs := hg.2 hs ht ha hb hab
    have hms := hm.2 hs ht ha hb hab
    simp only [gm, smul_eq_mul] at hgs hms ⊢
    calc
      gaussianChernoffExponent V (a * s + b * t) +
          strongMomentIntermediateExponent q V 1 (a * s + b * t) ≤
        (a * gaussianChernoffExponent V s +
          b * gaussianChernoffExponent V t) +
        (a * strongMomentIntermediateExponent q V 1 s +
          b * strongMomentIntermediateExponent q V 1 t) := add_le_add hgs hms
      _ = a * (gaussianChernoffExponent V s +
            strongMomentIntermediateExponent q V 1 s) +
          b * (gaussianChernoffExponent V t +
            strongMomentIntermediateExponent q V 1 t) := by ring
  have hgmZero : gm 0 = 0 := by simp [gm]
  have hgmNonneg : ∀ t : ℝ, 0 < t → 0 ≤ gm t := by
    intro t ht
    exact add_nonneg
      (gaussianChernoffExponent_nonneg hV.le)
      (strongMomentIntermediateExponent_nonneg q hV.le (by norm_num) ht.le)
  have htailConv := convexOn_exactStrongMomentTailExponent q
    (Q := 1) (by norm_num) hy
  have htailZero : exactStrongMomentTailExponent q 1 y 0 = 0 := by
    exact exactStrongMomentTailExponent_zero (by omega) 1 y
  have htailNonneg : ∀ t : ℝ, 0 < t →
      0 ≤ exactStrongMomentTailExponent q 1 y t := by
    intro t ht
    exact exactStrongMomentTailExponent_nonneg q (by norm_num) hy ht.le
  have hsplit := chernoffTransform_add_le hx.le hgmConv htailConv
    hgmZero htailZero hgmNonneg htailNonneg
  have hgm := chernoffTransform_gaussian_add_intermediate_one_le
    q hq hV hx
  have htail := chernoffTransform_exactStrongMomentTailExponent_le
    q (by omega) (Q := 1) (by norm_num) hy hx (by simpa using hscale)
  have hexponent : rioStrongMomentExponent q V 1 y =
      fun t => gm t + exactStrongMomentTailExponent q 1 y t := by
    funext t
    unfold rioStrongMomentExponent
    dsimp only [gm]
  rw [hexponent]
  calc
    chernoffTransform
        (fun t => gm t + exactStrongMomentTailExponent q 1 y t) x ≤
      chernoffTransform gm x +
        chernoffTransform (exactStrongMomentTailExponent q 1 y) x := hsplit
    _ ≤ (Real.sqrt (2 * V * x) +
          V ^ (-(1 / ((q : ℝ) - 2))) * x / 3) +
        (1 + 1 / (q : ℝ)) * y :=
      add_le_add (by simpa only [gm] using hgm) htail
    _ = Real.sqrt (2 * V * x) +
        V ^ (-(1 / ((q : ℝ) - 2))) * x / 3 +
          (1 + 1 / (q : ℝ)) * y := by ring

/-! ## Closing Rio's minimum estimate -/

/-- A convenient finite subseries bound for the exponential series.
@isnad1 id=le.0h1v.s5.2cd709f06dec from=translated src=- shape=fd2fe07e vocab=fa11c52f
-/
theorem sum_Ico_pow_div_factorial_le_exp (q : ℕ) :
    (∑ k ∈ Finset.Ico 3 q,
      (q : ℝ) ^ k / (k.factorial : ℝ)) ≤ Real.exp q := by
  simpa only [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div] using
    (Real.summable_pow_div_factorial (q : ℝ)).sum_le_tsum
      (Finset.Ico 3 q) (fun k _hk => by positivity)

/-- If the normalized coefficients obey Rio's comparison
`a_k <= exp(k-q)`, then the intermediate polynomial evaluated at `q/e`
is at most one.
@isnad1 id=le.1h3v.s6.5d6e29786d7d from=translated src=- shape=a86ed639 vocab=43d5a976
-/
theorem strongMomentIntermediateExponent_q_div_exp_one_le_one_of_coeff
    (q : ℕ) {V Q : ℝ}
    (hcoeff : ∀ k ∈ Finset.Ico 3 q,
      interpolatedStrongMomentCoefficient q V Q k ≤
        Real.exp ((k : ℝ) - (q : ℝ))) :
    strongMomentIntermediateExponent q V Q
        ((q : ℝ) / Real.exp 1) ≤ 1 := by
  have hsum := sum_Ico_pow_div_factorial_le_exp q
  unfold strongMomentIntermediateExponent
  calc
    (∑ k ∈ Finset.Ico 3 q,
        ((q : ℝ) / Real.exp 1) ^ k / (k.factorial : ℝ) *
          interpolatedStrongMomentCoefficient q V Q k) ≤
      ∑ k ∈ Finset.Ico 3 q,
        ((q : ℝ) / Real.exp 1) ^ k / (k.factorial : ℝ) *
          Real.exp ((k : ℝ) - (q : ℝ)) := by
      exact sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
        (hcoeff k hk) (div_nonneg (pow_nonneg (by positivity) k) (by positivity))
    _ = Real.exp (-(q : ℝ)) *
        (∑ k ∈ Finset.Ico 3 q,
          (q : ℝ) ^ k / (k.factorial : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [div_pow, Real.exp_one_pow, Real.exp_sub]
      have hexpK : Real.exp (k : ℝ) ≠ 0 := (Real.exp_pos _).ne'
      have hexpQ : Real.exp (q : ℝ) ≠ 0 := (Real.exp_pos _).ne'
      rw [Real.exp_neg]
      field_simp [hexpK, hexpQ]
    _ ≤ Real.exp (-(q : ℝ)) * Real.exp q :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- If Rio's Bernstein scale is larger than `e`, every normalized
interpolation coefficient is bounded by `exp(k-q)`.
@isnad1 id=le.4h3v.s6.cf67d4ad93f5 from=translated src=- shape=4bd4ae5f vocab=802c12d7
-/
theorem interpolatedStrongMomentCoefficient_one_le_exp_sub_of_exp_lt_scale
    {q k : ℕ} (hq : 3 ≤ q) (hkq : k ≤ q)
    {V : ℝ} (hV : 0 < V)
    (hscale : Real.exp 1 < V ^ (-(1 / ((q : ℝ) - 2)))) :
    interpolatedStrongMomentCoefficient q V 1 k ≤
      Real.exp ((k : ℝ) - (q : ℝ)) := by
  let r : ℝ := V ^ (1 / ((q : ℝ) - 2))
  have hr : 0 < r := Real.rpow_pos_of_pos hV _
  have hcInv : V ^ (-(1 / ((q : ℝ) - 2))) = r⁻¹ := by
    dsimp only [r]
    rw [Real.rpow_neg hV.le]
  have hrlt : r < (Real.exp 1)⁻¹ := by
    exact (lt_inv_comm₀ (Real.exp_pos 1) hr).1 (by
      simpa only [hcInv] using hscale)
  rw [interpolatedStrongMomentCoefficient_one_eq_root_pow hq hkq hV]
  calc
    r ^ (q - k) ≤ ((Real.exp 1)⁻¹) ^ (q - k) :=
      pow_le_pow_left₀ hr.le hrlt.le _
    _ = Real.exp ((k : ℝ) - (q : ℝ)) := by
      rw [inv_pow, Real.exp_one_pow, ← Real.exp_neg]
      congr 1
      rw [Nat.cast_sub hkq]
      ring

/-- The large-scale case in Rio's proof: if the Bernstein scale exceeds
`e`, the intermediate polynomial at `q/e` is at most one.
@isnad1 id=le.3h2v.s6.9d999c83f5e2 from=translated src=- shape=20e664ba vocab=bc928367
-/
theorem strongMomentIntermediateExponent_q_div_exp_one_le_one_of_exp_lt_scale
    (q : ℕ) (hq : 3 ≤ q) {V : ℝ} (hV : 0 < V)
    (hscale : Real.exp 1 < V ^ (-(1 / ((q : ℝ) - 2)))) :
    strongMomentIntermediateExponent q V 1
        ((q : ℝ) / Real.exp 1) ≤ 1 := by
  apply strongMomentIntermediateExponent_q_div_exp_one_le_one_of_coeff
  intro k hk
  exact interpolatedStrongMomentCoefficient_one_le_exp_sub_of_exp_lt_scale
    hq (by have := (Finset.mem_Ico.mp hk).2; omega) hV hscale

/-- Rio's key minimum estimate (3.23), with `e` written as `exp 1`.
@isnad1 id=le.2h2v.s6.34b1086ce1df from=translated src=- shape=624e4633 vocab=6d396aac
-/
theorem min_exp_mul_intermediate_or_scale_le_exp_one
    (q : ℕ) (hq : 3 ≤ q) {V : ℝ} (hV : 0 < V) :
    min
        (Real.exp 1 * strongMomentIntermediateExponent q V 1
          ((q : ℝ) / Real.exp 1))
        (V ^ (-(1 / ((q : ℝ) - 2)))) ≤
      Real.exp 1 := by
  by_cases hscale : V ^ (-(1 / ((q : ℝ) - 2))) ≤ Real.exp 1
  · exact (min_le_right _ _).trans hscale
  · have hlarge : Real.exp 1 < V ^ (-(1 / ((q : ℝ) - 2))) :=
      lt_of_not_ge hscale
    have hmid :=
      strongMomentIntermediateExponent_q_div_exp_one_le_one_of_exp_lt_scale
        q hq hV hlarge
    calc
      min
          (Real.exp 1 * strongMomentIntermediateExponent q V 1
            ((q : ℝ) / Real.exp 1))
          (V ^ (-(1 / ((q : ℝ) - 2)))) ≤
        Real.exp 1 * strongMomentIntermediateExponent q V 1
          ((q : ℝ) / Real.exp 1) := min_le_left _ _
      _ ≤ Real.exp 1 * 1 :=
        mul_le_mul_of_nonneg_left hmid (Real.exp_pos 1).le
      _ = Real.exp 1 := mul_one _

/-- Multiplying (3.23) by `x/3` gives the universal linear correction
`(e/3) x`.
@isnad1 id=le.3h3v.s7.8fb2c02e6d2b from=translated src=- shape=8b73a97b vocab=6d396aac
-/
theorem rio_intermediate_min_linear_correction_le
    (q : ℕ) (hq : 3 ≤ q) {V x : ℝ}
    (hV : 0 < V) (hx : 0 ≤ x) :
    x / 3 *
        min
          (Real.exp 1 * strongMomentIntermediateExponent q V 1
            ((q : ℝ) / Real.exp 1))
          (V ^ (-(1 / ((q : ℝ) - 2)))) ≤
      Real.exp 1 * x / 3 := by
  have hmin := min_exp_mul_intermediate_or_scale_le_exp_one q hq hV
  calc
    x / 3 *
        min
          (Real.exp 1 * strongMomentIntermediateExponent q V 1
            ((q : ℝ) / Real.exp 1))
          (V ^ (-(1 / ((q : ℝ) - 2)))) ≤
      x / 3 * Real.exp 1 :=
        mul_le_mul_of_nonneg_left hmin (div_nonneg hx (by norm_num))
    _ = Real.exp 1 * x / 3 := by ring

end ProbabilityTheory
