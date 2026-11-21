/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentMGF

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact-series strong-moment MGF estimates

This file refines `StrongMomentMGF` by retaining the exact tail of the
exponential series.  If `X ≤ y`, then the part of the exponential series
starting at degree `q` is bounded by

`expSeriesTail q (t * y) / y ^ q * (max X 0) ^ q`.

This is the form needed in the Rio--Marchina argument: unlike the usual
Lagrange remainder, its coefficient keeps the degree-`q` contraction.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The one-sided Taylor majorant retaining the exact exponential-series
tail.-/
def oneSidedExpSeriesTaylorBound (q : ℕ) (x : ℝ) : ℝ :=
  1 + x + x ^ 2 / 2 +
    (∑ k ∈ Ico 3 q, (max x 0) ^ k / (k.factorial : ℝ)) +
    expSeriesTail q (max x 0)

/-- Exact-series version of the one-sided Taylor majorant.
@isnad1 id=le.1h2v.s4.4d6c80a9f1ea from=translated src=- shape=530dc965 vocab=cf4e8c7a
-/
theorem exp_le_oneSidedExpSeriesTaylorBound
    (q : ℕ) (hq : 3 ≤ q) (x : ℝ) :
    Real.exp x ≤ oneSidedExpSeriesTaylorBound q x := by
  by_cases hx : 0 ≤ x
  · have hexact := exp_eq_sum_range_add_expSeriesTail x q
    let f : ℕ → ℝ := fun k => x ^ k / (k.factorial : ℝ)
    have hsplit := sum_range_add_sum_Ico f hq
    have hthree : (∑ k ∈ range 3, f k) = 1 + x + x ^ 2 / 2 := by
      simp only [f, sum_range_succ, range_one, sum_singleton, pow_zero,
        Nat.factorial, Nat.cast_one, div_one, pow_one]
      ring
    have hsum : (∑ k ∈ range q, f k) =
        1 + x + x ^ 2 / 2 + ∑ k ∈ Ico 3 q, f k := by
      rw [← hsplit, hthree]
    unfold oneSidedExpSeriesTaylorBound
    rw [max_eq_left hx]
    rw [hexact, hsum]
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
    unfold oneSidedExpSeriesTaylorBound
    rw [max_eq_right hxnonpos, hsumzero, expSeriesTail_zero hq0]
    simp only [add_zero]
    exact hbase

/-- Pointwise exact-series estimate after rescaling by an upper bound `y`.
Only the positive part enters at degrees at least three.
@isnad1 id=le.4h4v.s8.af8307a5cb29 from=translated src=- shape=c5158698 vocab=26b7d8f9
-/
theorem exp_mul_le_exactStrongMomentMajorant
    (q : ℕ) (hq : 3 ≤ q) {t x y : ℝ}
    (ht : 0 ≤ t) (hy : 0 < y) (hxy : x ≤ y) :
    Real.exp (t * x) ≤
      1 + t * x + (1 / 2 : ℝ) * (t * x) ^ 2 +
        (∑ k ∈ Ico 3 q,
          (t ^ k / (k.factorial : ℝ)) * (max x 0) ^ k) +
        (expSeriesTail q (t * y) / y ^ q) * (max x 0) ^ q := by
  have hTaylor := exp_le_oneSidedExpSeriesTaylorBound q hq (t * x)
  have hmax : max (t * x) 0 = t * max x 0 :=
    max_mul_eq_mul_max t x ht
  have ha : 0 ≤ max x 0 := le_max_right _ _
  have hay : max x 0 ≤ y := max_le hxy hy.le
  have htail := expSeriesTail_mul_le_ratio_pow_mul q ht ha hay hy
  have hsumEq :
      (∑ k ∈ Ico 3 q,
        (t * max x 0) ^ k / (k.factorial : ℝ)) =
      ∑ k ∈ Ico 3 q,
        (t ^ k / (k.factorial : ℝ)) * (max x 0) ^ k := by
    apply sum_congr rfl
    intro k _hk
    rw [mul_pow]
    ring
  have hratio :
      (max x 0 / y) ^ q * expSeriesTail q (t * y) =
        (expSeriesTail q (t * y) / y ^ q) * (max x 0) ^ q := by
    rw [div_pow]
    ring
  unfold oneSidedExpSeriesTaylorBound at hTaylor
  rw [hmax, hsumEq] at hTaylor
  have hprefix :
      1 + t * x + (t * x) ^ 2 / 2 +
          (∑ k ∈ Ico 3 q,
            (t ^ k / (k.factorial : ℝ)) * (max x 0) ^ k) =
        1 + t * x + (1 / 2 : ℝ) * (t * x) ^ 2 +
          (∑ k ∈ Ico 3 q,
            (t ^ k / (k.factorial : ℝ)) * (max x 0) ^ k) := by
    ring
  calc
    Real.exp (t * x) ≤
        1 + t * x + (t * x) ^ 2 / 2 +
          (∑ k ∈ Ico 3 q,
            (t ^ k / (k.factorial : ℝ)) * (max x 0) ^ k) +
          expSeriesTail q (t * max x 0) := hTaylor
    _ ≤ 1 + t * x + (t * x) ^ 2 / 2 +
          (∑ k ∈ Ico 3 q,
            (t ^ k / (k.factorial : ℝ)) * (max x 0) ^ k) +
          (max x 0 / y) ^ q * expSeriesTail q (t * y) :=
      add_le_add le_rfl htail
    _ = 1 + t * x + (1 / 2 : ℝ) * (t * x) ^ 2 +
          (∑ k ∈ Ico 3 q,
            (t ^ k / (k.factorial : ℝ)) * (max x 0) ^ k) +
          (expSeriesTail q (t * y) / y ^ q) * (max x 0) ^ q := by
      rw [hratio, hprefix]

/-- Deterministic exponent obtained by integrating the exact-series
one-sided Taylor majorant.-/
def strongMomentSeriesExponent
    (q : ℕ) (t y second : ℝ) (moment : ℕ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * t ^ 2 * second +
    (∑ k ∈ Ico 3 q, t ^ k / (k.factorial : ℝ) * moment k) +
    expSeriesTail q (t * y) / y ^ q * moment q

/-- Exact-series strong-moment exponents add when their moment proxies add.
@isnad1 id=eq.0h7v.s6.9d5f118e1e78 from=translated src=- shape=75974dbf vocab=f2a11385
-/
theorem sum_strongMomentSeriesExponent
    {ι : Type*} (s : Finset ι) (q : ℕ) (t y : ℝ)
    (second : ι → ℝ) (moment : ι → ℕ → ℝ) :
    (∑ i ∈ s, strongMomentSeriesExponent q t y (second i) (moment i)) =
      strongMomentSeriesExponent q t y
        (∑ i ∈ s, second i) (fun k => ∑ i ∈ s, moment i k) := by
  classical
  have hfirst :
      (∑ i ∈ s, (1 / 2 : ℝ) * t ^ 2 * second i) =
        (1 / 2 : ℝ) * t ^ 2 * ∑ i ∈ s, second i := by
    rw [Finset.mul_sum]
  have hmiddle :
      (∑ i ∈ s, ∑ k ∈ Ico 3 q,
        t ^ k / (k.factorial : ℝ) * moment i k) =
        ∑ k ∈ Ico 3 q,
          t ^ k / (k.factorial : ℝ) * ∑ i ∈ s, moment i k := by
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro k _hk
    rw [Finset.mul_sum]
  have htail :
      (∑ i ∈ s,
        expSeriesTail q (t * y) / y ^ q * moment i q) =
        expSeriesTail q (t * y) / y ^ q * ∑ i ∈ s, moment i q := by
    rw [Finset.mul_sum]
  unfold strongMomentSeriesExponent
  simp only [Finset.sum_add_distrib]
  rw [hfirst, hmiddle, htail]

/-- The integrated exact-series one-sided Taylor estimate.

The variable may have an unbounded negative tail.  Its upper bound `y` is
strictly positive because the degree-`q` contraction is normalized by
`y ^ q`.
@isnad1 id=le.8h6v.s8.d372731d6f39 from=translated src=- shape=dad14768 vocab=0b497828
-/
theorem integral_exp_mul_le_exp_strongMomentSeriesExponent
    [IsProbabilityMeasure mu]
    (X : Omega → ℝ) (q : ℕ) (hq : 3 ≤ q)
    {t y : ℝ} (ht : 0 ≤ t) (hy : 0 < y)
    (hX : Integrable X mu)
    (hXsq : Integrable (fun omega => X omega ^ 2) mu)
    (hpow : ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega => (max (X omega) 0) ^ k) mu)
    (hupper : ∀ᵐ omega ∂mu, X omega ≤ y)
    (hcenter : (∫ omega, X omega ∂mu) ≤ 0) :
    (∫ omega, Real.exp (t * X omega) ∂mu) ≤
      Real.exp (strongMomentSeriesExponent q t y
        (∫ omega, X omega ^ 2 ∂mu)
        (fun k => ∫ omega, (max (X omega) 0) ^ k ∂mu)) := by
  let M : ℕ → ℝ := fun k => ∫ omega, (max (X omega) 0) ^ k ∂mu
  let V : ℝ := ∫ omega, X omega ^ 2 ∂mu
  let C : ℝ := expSeriesTail q (t * y) / y ^ q
  let E : ℝ := strongMomentSeriesExponent q t y V M
  have hExp : Integrable (fun omega => Real.exp (t * X omega)) mu := by
    apply Integrable.of_bound
      ((hX.aemeasurable.const_mul t).exp.aestronglyMeasurable)
      (Real.exp (t * y))
    filter_upwards [hupper] with omega homega
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_monotone (mul_le_mul_of_nonneg_left homega ht)
  have hMomentNonneg : ∀ k, 0 ≤ M k := by
    intro k
    exact integral_nonneg fun omega => pow_nonneg (le_max_right _ _) k
  have hVNonneg : 0 ≤ V := integral_nonneg fun omega => sq_nonneg _
  have hTailNonneg : 0 ≤ expSeriesTail q (t * y) :=
    expSeriesTail_nonneg (mul_nonneg ht hy.le) q
  have hCNonneg : 0 ≤ C := by
    unfold C
    exact div_nonneg hTailNonneg (pow_nonneg hy.le q)
  have hENonneg : 0 ≤ E := by
    unfold E strongMomentSeriesExponent
    have hsum : 0 ≤ ∑ k ∈ Ico 3 q,
        t ^ k / (k.factorial : ℝ) * M k := by
      positivity
    have htail : 0 ≤
        expSeriesTail q (t * y) / y ^ q * M q := by
      change 0 ≤ C * M q
      positivity
    positivity
  have hfiniteInt : ∀ k ∈ Finset.Ico 3 q,
      Integrable (fun omega =>
        (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) mu := by
    intro k hk
    exact (hpow k (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Ico.mp hk).1.trans' (by norm_num),
        (Finset.mem_Ico.mp hk).2.le⟩)).const_mul _
  have htailInt : Integrable (fun omega =>
      C * (max (X omega) 0) ^ q) mu :=
    (hpow q (Finset.mem_Icc.mpr
      ⟨hq.trans' (by norm_num), le_rfl⟩)).const_mul _
  have hmajorantInt : Integrable (fun omega =>
      1 + t * X omega + (1 / 2 : ℝ) * (t * X omega) ^ 2 +
        (∑ k ∈ Ico 3 q,
          (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) +
        C * (max (X omega) 0) ^ q) mu := by
    have hlin : Integrable (fun omega => t * X omega) mu := hX.const_mul t
    have hquad : Integrable
        (fun omega => (1 / 2 : ℝ) * (t * X omega) ^ 2) mu := by
      have hs : Integrable (fun omega => (t * X omega) ^ 2) mu := by
        convert hXsq.const_mul (t ^ 2) using 1
        ext omega
        ring
      exact hs.const_mul _
    have hsumInt : Integrable (fun omega =>
        ∑ k ∈ Ico 3 q,
          (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) mu :=
      integrable_finsetSum _ hfiniteInt
    have hshape :
        (fun omega =>
          1 + t * X omega + (1 / 2 : ℝ) * (t * X omega) ^ 2 +
            (∑ k ∈ Ico 3 q,
              (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) +
            C * (max (X omega) 0) ^ q) =
          ((((fun _ : Omega => (1 : ℝ)) + (fun omega => t * X omega)) +
              (fun omega => (1 / 2 : ℝ) * (t * X omega) ^ 2)) +
            (fun omega => ∑ k ∈ Ico 3 q,
              (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k)) +
            (fun omega => C * (max (X omega) 0) ^ q) := by
      funext omega
      simp only [Pi.add_apply]
    rw [hshape]
    exact (((((integrable_const (1 : ℝ)).add hlin).add hquad).add
      hsumInt).add htailInt)
  have hpoint : ∀ᵐ omega ∂mu,
      Real.exp (t * X omega) ≤
        1 + t * X omega + (1 / 2 : ℝ) * (t * X omega) ^ 2 +
          (∑ k ∈ Ico 3 q,
            (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) +
          C * (max (X omega) 0) ^ q := by
    filter_upwards [hupper] with omega homega
    simpa only [C] using
      (exp_mul_le_exactStrongMomentMajorant q hq ht hy homega)
  have hint := integral_mono_ae hExp hmajorantInt hpoint
  have hlin : Integrable (fun omega => t * X omega) mu := hX.const_mul t
  have hquad : Integrable
      (fun omega => (1 / 2 : ℝ) * (t * X omega) ^ 2) mu := by
    have hs : Integrable (fun omega => (t * X omega) ^ 2) mu := by
      convert hXsq.const_mul (t ^ 2) using 1
      ext omega
      ring
    exact hs.const_mul _
  have hsumInt : Integrable (fun omega =>
      ∑ k ∈ Ico 3 q,
        (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) mu :=
    integrable_finsetSum _ hfiniteInt
  have hlinIntegral :
      (∫ omega, t * X omega ∂mu) = t * ∫ omega, X omega ∂mu := by
    rw [integral_const_mul]
  have hquadIntegral :
      (∫ omega, (1 / 2 : ℝ) * (t * X omega) ^ 2 ∂mu) =
        (1 / 2 : ℝ) * t ^ 2 * V := by
    rw [integral_const_mul]
    have hscaled :
        (∫ omega, (t * X omega) ^ 2 ∂mu) = t ^ 2 * V := by
      change (∫ omega, (t * X omega) ^ 2 ∂mu) =
        t ^ 2 * ∫ omega, X omega ^ 2 ∂mu
      have hfun : (fun omega => (t * X omega) ^ 2) =
          fun omega => t ^ 2 * X omega ^ 2 := by
        funext omega
        ring
      rw [hfun, integral_const_mul]
    rw [hscaled]
    ring
  have hsumIntegral :
      (∫ omega, (∑ k ∈ Ico 3 q,
        (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) ∂mu) =
      ∑ k ∈ Ico 3 q,
        t ^ k / (k.factorial : ℝ) * M k := by
    calc
      (∫ omega, (∑ k ∈ Ico 3 q,
          (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) ∂mu) =
          ∑ k ∈ Ico 3 q,
            ∫ omega, (t ^ k / (k.factorial : ℝ)) *
              (max (X omega) 0) ^ k ∂mu :=
        integral_finsetSum (Ico 3 q) hfiniteInt
      _ = ∑ k ∈ Ico 3 q,
          t ^ k / (k.factorial : ℝ) * M k := by
        apply sum_congr rfl
        intro k _hk
        rw [integral_const_mul]
  have htailIntegral :
      (∫ omega, C * (max (X omega) 0) ^ q ∂mu) = C * M q := by
    rw [integral_const_mul]
  have hmajorantIntegral :
      (∫ omega,
        1 + t * X omega + (1 / 2 : ℝ) * (t * X omega) ^ 2 +
          (∑ k ∈ Ico 3 q,
            (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) +
          C * (max (X omega) 0) ^ q ∂mu) =
        1 + t * (∫ omega, X omega ∂mu) + E := by
    have hconst : Integrable (fun _ : Omega => (1 : ℝ)) mu := integrable_const _
    have hconstLin := hconst.add hlin
    have hconstLinQuad := hconstLin.add hquad
    have hprefix := hconstLinQuad.add hsumInt
    have hshape :
        (fun omega =>
          1 + t * X omega + (1 / 2 : ℝ) * (t * X omega) ^ 2 +
            (∑ k ∈ Ico 3 q,
              (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) +
            C * (max (X omega) 0) ^ q) =
          ((((fun _ : Omega => (1 : ℝ)) + (fun omega => t * X omega)) +
              (fun omega => (1 / 2 : ℝ) * (t * X omega) ^ 2)) +
            (fun omega => ∑ k ∈ Ico 3 q,
              (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k)) +
            (fun omega => C * (max (X omega) 0) ^ q) := by
      funext omega
      simp only [Pi.add_apply]
    rw [hshape]
    rw [integral_add' hprefix htailInt,
      integral_add' hconstLinQuad hsumInt,
      integral_add' hconstLin hquad,
      integral_add' hconst hlin,
      integral_const, hlinIntegral, hquadIntegral,
      hsumIntegral, htailIntegral]
    simp only [probReal_univ, one_smul]
    unfold E strongMomentSeriesExponent C
    ring
  rw [hmajorantIntegral] at hint
  calc
    (∫ omega, Real.exp (t * X omega) ∂mu) ≤
        1 + t * (∫ omega, X omega ∂mu) + E := hint
    _ ≤ 1 + E := by
      have htcenter : t * (∫ omega, X omega ∂mu) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht hcenter
      linarith
    _ ≤ Real.exp E := by
      simpa [add_comm] using Real.add_one_le_exp E

end ProbabilityTheory
