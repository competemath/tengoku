import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Summable
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
import Tengoku.Seed.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Tengoku.Seed.Topology.Algebra.InfiniteSum.NatInt
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Order
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The analytic part of the sharp subgroup-interval bound.  In particular, the
shifted theta inequality below is obtained from Mathlib's proved Poisson
summation theorem, rather than being introduced as an additional assumption.
-/

namespace SharpIntermediateSubgroupBounds

open scoped BigOperators Topology
open Filter Finset Real

/-- The finite Euler factor `γ_{p,r}`, represented in `ℝ`.-/
noncomputable def gammaR (p : ℝ) (r : ℕ) : ℝ :=
  ∏ j ∈ Finset.range r, (1 - p⁻¹ ^ (j + 1))

/-- The reciprocal Euler product occurring in the sharp constant.-/
noncomputable def eulerC (p : ℝ) : ℝ :=
  ∏' n : ℕ, (1 - p⁻¹ ^ (n + 1))⁻¹

/-- The Gaussian theta series in exponential normal form.-/
noncomputable def gaussianTheta (p : ℝ) : ℝ :=
  ∑' z : ℤ, Real.exp (-Real.log p * (z : ℝ) ^ 2)

/-- The sharp analytic constant `C_p Θ_p`.-/
noncomputable def sharpConstant (p : ℝ) : ℝ :=
  eulerC p * gaussianTheta p

/-- A translate of the periodized Gaussian.-/
noncomputable def shiftedTheta (p x : ℝ) : ℝ :=
  ∑' z : ℤ, Real.exp (-Real.log p * ((z : ℝ) - x) ^ 2)

/-- The correction which writes an inverse Euler factor as `1 + correction`.-/
private noncomputable def eulerCorrection (p : ℝ) (n : ℕ) : ℝ :=
  p⁻¹ ^ (n + 1) / (1 - p⁻¹ ^ (n + 1))

private lemma euler_factor_eq_one_add (p : ℝ) (n : ℕ)
    (h : 1 - p⁻¹ ^ (n + 1) ≠ 0) :
    (1 - p⁻¹ ^ (n + 1))⁻¹ = 1 + eulerCorrection p n := by
  simp only [eulerCorrection, div_eq_mul_inv]
  calc
    (1 - p⁻¹ ^ (n + 1))⁻¹ =
        ((1 - p⁻¹ ^ (n + 1)) + p⁻¹ ^ (n + 1)) *
          (1 - p⁻¹ ^ (n + 1))⁻¹ := by rw [sub_add_cancel, one_mul]
    _ = 1 + p⁻¹ ^ (n + 1) * (1 - p⁻¹ ^ (n + 1))⁻¹ := by
      rw [add_mul, mul_inv_cancel₀ h]

private lemma eulerCorrection_nonneg {p : ℝ} (hp : 2 ≤ p) (n : ℕ) :
    0 ≤ eulerCorrection p n := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ p⁻¹ := (inv_pos.mpr hp0).le
  have hq_half : p⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
  have ht0 : 0 ≤ p⁻¹ ^ (n + 1) := pow_nonneg hq0 _
  have ht_half : p⁻¹ ^ (n + 1) ≤ (2 : ℝ)⁻¹ := by
    calc
      p⁻¹ ^ (n + 1) ≤ p⁻¹ ^ 1 :=
        pow_le_pow_of_le_one hq0 (hq_half.trans (by norm_num)) (by omega)
      _ ≤ (2 : ℝ)⁻¹ := by simpa using hq_half
  exact div_nonneg ht0 (by linarith)

private lemma eulerCorrection_le {p : ℝ} (hp : 2 ≤ p) (n : ℕ) :
    eulerCorrection p n ≤ 2 * p⁻¹ ^ (n + 1) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ p⁻¹ := (inv_pos.mpr hp0).le
  have hq_half : p⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
  have ht0 : 0 ≤ p⁻¹ ^ (n + 1) := pow_nonneg hq0 _
  have ht_half : p⁻¹ ^ (n + 1) ≤ (2 : ℝ)⁻¹ := by
    calc
      p⁻¹ ^ (n + 1) ≤ p⁻¹ ^ 1 :=
        pow_le_pow_of_le_one hq0 (hq_half.trans (by norm_num)) (by omega)
      _ ≤ (2 : ℝ)⁻¹ := by simpa using hq_half
  rw [eulerCorrection, div_le_iff₀ (by linarith : 0 < 1 - p⁻¹ ^ (n + 1))]
  nlinarith [mul_nonneg ht0 (sub_nonneg.mpr (by linarith : 2 * p⁻¹ ^ (n + 1) ≤ 1))]

/--
@isnad1 id=summable.1h1v.s4.2eb752f76509 from=translated src=- shape=2a9d7336 vocab=286e855b
-/
lemma summable_eulerCorrection {p : ℝ} (hp : 2 ≤ p) :
    Summable (eulerCorrection p) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ p⁻¹ := (inv_pos.mpr hp0).le
  have hq1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hgeom : Summable (fun n : ℕ ↦ p⁻¹ ^ (n + 1)) := by
    simpa using (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq0 hq1)
  exact (hgeom.mul_left 2).of_nonneg_of_le
    (fun n ↦ eulerCorrection_nonneg hp n) (fun n ↦ eulerCorrection_le hp n)

/--
@isnad1 id=multipli.1h1v.s6.c41d729bddce from=translated src=- shape=3e5c74d2 vocab=ba07fb0a
-/
lemma multipliable_euler_factors {p : ℝ} (hp : 2 ≤ p) :
    Multipliable (fun n : ℕ ↦ (1 - p⁻¹ ^ (n + 1))⁻¹) := by
  have hs := summable_eulerCorrection hp
  have habs (n : ℕ) : |eulerCorrection p n| = eulerCorrection p n :=
    abs_of_nonneg (eulerCorrection_nonneg hp n)
  have hm : Multipliable (fun n : ℕ ↦ 1 + eulerCorrection p n) :=
    multipliable_one_add_of_summable (by
      simpa only [Real.norm_eq_abs, habs] using hs)
  refine hm.congr ?_
  intro n
  symm
  apply euler_factor_eq_one_add
  have := eulerCorrection_nonneg hp n
  have hp0 : 0 < p := by linarith
  have hq1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hpow : p⁻¹ ^ (n + 1) < 1 :=
    (pow_lt_one₀ (inv_pos.mpr hp0).le hq1 (by omega))
  linarith

/-- The finite inverse Euler products converge to `eulerC`.
@isnad1 id=tendsto.1h1v.s6.507cdab32ffa from=translated src=- shape=43dec19e vocab=28b920be
-/
lemma eulerC_partial_tendsto {p : ℝ} (hp : 2 ≤ p) :
    Tendsto (fun r : ℕ ↦ ∏ n ∈ Finset.range r, (1 - p⁻¹ ^ (n + 1))⁻¹)
      atTop (nhds (eulerC p)) := by
  exact (multipliable_euler_factors hp).tendsto_prod_tprod_nat

private lemma euler_partial_pos {p : ℝ} (hp : 2 ≤ p) (r : ℕ) :
    0 < ∏ n ∈ Finset.range r, (1 - p⁻¹ ^ (n + 1))⁻¹ := by
  apply Finset.prod_pos
  intro n hn
  have hp0 : 0 < p := by linarith
  have hq1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  exact inv_pos.mpr (sub_pos.mpr (pow_lt_one₀ (inv_pos.mpr hp0).le hq1 (by omega)))

private lemma euler_partial_strictMono {p : ℝ} (hp : 2 ≤ p) :
    StrictMono (fun r : ℕ ↦ ∏ n ∈ Finset.range r, (1 - p⁻¹ ^ (n + 1))⁻¹) := by
  apply strictMono_nat_of_lt_succ
  intro r
  rw [Finset.prod_range_succ]
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < p⁻¹ ^ (r + 1) := pow_pos (inv_pos.mpr hp0) _
  have hq1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hden : 0 < 1 - p⁻¹ ^ (r + 1) :=
    sub_pos.mpr (pow_lt_one₀ (inv_pos.mpr hp0).le hq1 (by omega))
  have hfactor : 1 < (1 - p⁻¹ ^ (r + 1))⁻¹ := by
    exact (one_lt_inv₀ hden).2 (by linarith)
  nlinarith [euler_partial_pos hp r]

/--
@isnad1 id=lt.1h1v.s4.8dddd9b5999a from=translated src=- shape=a8dc2df9 vocab=7573e8be
-/
lemma eulerC_pos {p : ℝ} (hp : 2 ≤ p) : 0 < eulerC p := by
  have hmono := (euler_partial_strictMono hp).monotone
  have hlim := eulerC_partial_tendsto hp
  have hle := hmono.ge_of_tendsto hlim 1
  have hzero : (1 : ℝ) < ∏ n ∈ Finset.range 1,
      (1 - p⁻¹ ^ (n + 1))⁻¹ := by
    simpa using (euler_partial_strictMono hp (Nat.zero_lt_one))
  linarith

/-- Every finite inverse Euler factor is strictly below the infinite product.
@isnad1 id=lt.1h2v.s4.ffdf1e74be6e from=translated src=- shape=21a3902e vocab=957df523
-/
lemma gammaR_inv_lt_eulerC {p : ℝ} (hp : 2 ≤ p) (r : ℕ) :
    (gammaR p r)⁻¹ < eulerC p := by
  have hfinite : (gammaR p r)⁻¹ =
      ∏ n ∈ Finset.range r, (1 - p⁻¹ ^ (n + 1))⁻¹ := by
    simp [gammaR, Finset.prod_inv_distrib]
  rw [hfinite]
  have hs := euler_partial_strictMono hp
  have hle := hs.monotone.ge_of_tendsto (eulerC_partial_tendsto hp) (r + 1)
  exact (hs (Nat.lt_succ_self r)).trans_le hle

/-- Summability of an arbitrary positive Gaussian on `ℤ`.
@isnad1 id=summable.1h1v.s5.752dc00c3be6 from=translated src=- shape=18154e3c vocab=0137c2a1
-/
lemma summable_int_gaussian {A : ℝ} (hA : 0 < A) :
    Summable (fun z : ℤ ↦ Real.exp (-A * (z : ℝ) ^ 2)) := by
  have hT : 0 < A / Real.pi := div_pos hA Real.pi_pos
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0 hT 0
  simpa only [pow_zero, Int.cast_one, one_mul, mul_zero, sub_zero] using h.congr
    (fun z ↦ by
      congr 1
      field_simp [Real.pi_ne_zero]
      ring)

/--
@isnad1 id=summable.1h1v.s5.89c350027f21 from=translated src=- shape=8c067efd vocab=278ef414
-/
lemma gaussianTheta_summable {p : ℝ} (hp : 1 < p) :
    Summable (fun z : ℤ ↦ Real.exp (-Real.log p * (z : ℝ) ^ 2)) :=
  summable_int_gaussian (Real.log_pos hp)

/-- The symmetric Gaussian sum, split into its central term and the positive
tail.  This form is convenient for natural-number dominated convergence.
@isnad1 id=eq.1h1v.s6.0675cf3117e5 from=translated src=- shape=1bd81614 vocab=6f060e1f
-/
lemma gaussianTheta_eq_one_add_two_mul_tsum_pnat {p : ℝ} (hp : 1 < p) :
    gaussianTheta p = 1 + 2 * ∑' j : ℕ+,
      Real.exp (-Real.log p * (j : ℝ) ^ 2) := by
  unfold gaussianTheta
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat]
  · simp
  · intro z
    simp
  · exact gaussianTheta_summable hp

/--
@isnad1 id=summable.1h2v.s6.b3ed853746d1 from=translated src=- shape=ce9d8762 vocab=a703cff7
-/
lemma shiftedTheta_summable {p x : ℝ} (hp : 1 < p) :
    Summable (fun z : ℤ ↦ Real.exp (-Real.log p * ((z : ℝ) - x) ^ 2)) := by
  let A := Real.log p
  have hA : 0 < A := Real.log_pos hp
  have hbase := summable_int_gaussian (A := A / 2) (by positivity)
  have hmajor := hbase.mul_left (Real.exp (A * x ^ 2))
  refine hmajor.of_norm_bounded (fun z ↦ ?_)
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_add]
  rw [Real.exp_le_exp]
  have hs : 0 ≤ ((z : ℝ) - 2 * x) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hA.le hs]

/--
@isnad1 id=lt.1h1v.s4.ac1ddb358053 from=translated src=- shape=35bd48ee vocab=b6e84896
-/
lemma gaussianTheta_pos {p : ℝ} (hp : 1 < p) : 0 < gaussianTheta p := by
  unfold gaussianTheta
  apply (gaussianTheta_summable hp).tsum_pos (fun z ↦ (Real.exp_pos _).le) 0
  simpa using Real.exp_pos (0 : ℝ)

/--
@isnad1 id=lt.1h1v.s4.bf4b2acaf146 from=translated src=- shape=a8dc2df9 vocab=a245c036
-/
lemma sharpConstant_pos {p : ℝ} (hp2 : 2 ≤ p) : 0 < sharpConstant p := by
  exact mul_pos (eulerC_pos hp2) (gaussianTheta_pos (by linarith))

/-- Poisson summation for a translated Gaussian, in the real Fourier form
needed for the sharp theta estimate.-/
private lemma shifted_gaussian_fourier {A : ℝ} (hA : 0 < A) (x : ℝ) :
    (∑' z : ℤ, Real.exp (-A * ((z : ℝ) - x) ^ 2)) =
      1 / (A / Real.pi) ^ (1 / 2 : ℝ) *
        ∑' k : ℤ, Real.exp (-(Real.pi ^ 2 / A) * (k : ℝ) ^ 2) *
          Real.cos (2 * Real.pi * (k : ℝ) * x) := by
  let a : ℝ := A / Real.pi
  let b : ℝ := a * x
  have ha : 0 < a := div_pos hA Real.pi_pos
  have hP := Complex.tsum_exp_neg_quadratic
    (a := (a : ℂ)) (by simpa using ha) (b : ℂ)
  let c : ℂ := Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2)
  have hleft :
      (∑' z : ℤ, Complex.exp (-(A : ℂ) * ((z : ℂ) - (x : ℂ)) ^ 2)) =
        c * ∑' z : ℤ,
          Complex.exp (-Real.pi * (a : ℂ) * (z : ℂ) ^ 2 +
            2 * Real.pi * (b : ℂ) * (z : ℂ)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro z
    rw [← Complex.exp_add]
    congr 1
    simp only [c, a, b]
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  have hright :
      c * (1 / (a : ℂ) ^ (1 / 2 : ℂ) *
          ∑' k : ℤ, Complex.exp (-Real.pi / (a : ℂ) *
            ((k : ℂ) + Complex.I * (b : ℂ)) ^ 2)) =
        1 / (a : ℂ) ^ (1 / 2 : ℂ) *
          ∑' k : ℤ, Complex.exp
            ((-(Real.pi ^ 2 / A) * (k : ℝ) ^ 2 : ℝ) -
              (2 * Real.pi * (k : ℝ) * x : ℝ) * Complex.I) := by
    rw [← mul_assoc, mul_comm c (1 / (a : ℂ) ^ (1 / 2 : ℂ)), mul_assoc]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [← Complex.exp_add]
    congr 1
    simp only [c, a, b]
    push_cast
    field_simp [Real.pi_ne_zero, ne_of_gt hA]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hcomplex :
      (∑' z : ℤ, Complex.exp (-(A : ℂ) * ((z : ℂ) - (x : ℂ)) ^ 2)) =
        1 / (a : ℂ) ^ (1 / 2 : ℂ) *
          ∑' k : ℤ, Complex.exp
            ((-(Real.pi ^ 2 / A) * (k : ℝ) ^ 2 : ℝ) -
              (2 * Real.pi * (k : ℝ) * x : ℝ) * Complex.I) := by
    rw [hleft, hP, hright]
  have hprimalR : Summable (fun z : ℤ ↦
      Real.exp (-A * ((z : ℝ) - x) ^ 2)) := by
    simpa only [Real.log_exp] using shiftedTheta_summable
      (p := Real.exp A) (x := x) (Real.one_lt_exp_iff.mpr hA)
  have hprimalTerm (z : ℤ) :
      Complex.exp (-(A : ℂ) * ((z : ℂ) - (x : ℂ)) ^ 2) =
        (Real.exp (-A * ((z : ℝ) - x) ^ 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  have hprimalC : Summable (fun z : ℤ ↦
      Complex.exp (-(A : ℂ) * ((z : ℂ) - (x : ℂ)) ^ 2)) := by
    have hcast : Summable (fun z : ℤ ↦
        (Real.exp (-A * ((z : ℝ) - x) ^ 2) : ℂ)) :=
      Complex.summable_ofReal.mpr hprimalR
    exact hcast.congr (fun z ↦ (hprimalTerm z).symm)
  have hdual : Summable (fun k : ℤ ↦ Complex.exp
      ((-(Real.pi ^ 2 / A) * (k : ℝ) ^ 2 : ℝ) -
        (2 * Real.pi * (k : ℝ) * x : ℝ) * Complex.I)) := by
    have hg := summable_int_gaussian (A := Real.pi ^ 2 / A) (by positivity)
    refine hg.of_norm_bounded (fun k ↦ ?_)
    rw [Complex.norm_exp]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, sub_zero,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), le_refl]
  have hdualRe (k : ℤ) :
      (Complex.exp
        ((-(Real.pi ^ 2 / A) * (k : ℝ) ^ 2 : ℝ) -
          (2 * Real.pi * (k : ℝ) * x : ℝ) * Complex.I)).re =
        Real.exp (-(Real.pi ^ 2 / A) * (k : ℝ) ^ 2) *
          Real.cos (2 * Real.pi * (k : ℝ) * x) := by
    let u : ℝ := -(Real.pi ^ 2 / A) * (k : ℝ) ^ 2
    let v : ℝ := 2 * Real.pi * (k : ℝ) * x
    change (Complex.exp ((u : ℂ) - (v : ℂ) * Complex.I)).re =
      Real.exp u * Real.cos v
    simp only [Complex.exp_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, mul_one, add_zero, sub_zero, zero_sub,
      Real.cos_neg]
  have hpref : 1 / (a : ℂ) ^ (1 / 2 : ℂ) =
      ((1 / a ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    symm
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow ha.le]
    norm_num
  rw [hpref] at hcomplex
  have hre := congrArg Complex.re hcomplex
  rw [Complex.re_tsum hprimalC, Complex.mul_re, Complex.re_tsum hdual] at hre
  simpa only [hprimalTerm, Complex.ofReal_re, Complex.ofReal_im, hdualRe,
    zero_mul, sub_zero, a] using hre

/-- The translated theta series is maximized at an integral translate.
@isnad1 id=le.1h2v.s4.12ad5cee8d54 from=translated src=- shape=c9e0acd6 vocab=752ced33
-/
lemma shiftedTheta_le {p x : ℝ} (hp : 1 < p) :
    shiftedTheta p x ≤ gaussianTheta p := by
  have hA : 0 < Real.log p := Real.log_pos hp
  have hzero : (∑' z : ℤ, Real.exp (-Real.log p * (z : ℝ) ^ 2)) =
      1 / (Real.log p / Real.pi) ^ (1 / 2 : ℝ) *
        ∑' k : ℤ, Real.exp (-(Real.pi ^ 2 / Real.log p) * (k : ℝ) ^ 2) := by
    simpa using shifted_gaussian_fourier hA 0
  rw [shiftedTheta, gaussianTheta, shifted_gaussian_fourier hA x, hzero]
  have hweight : Summable (fun k : ℤ ↦
      Real.exp (-(Real.pi ^ 2 / Real.log p) * (k : ℝ) ^ 2)) :=
    summable_int_gaussian (by positivity)
  have hcos : Summable (fun k : ℤ ↦
      Real.exp (-(Real.pi ^ 2 / Real.log p) * (k : ℝ) ^ 2) *
        Real.cos (2 * Real.pi * (k : ℝ) * x)) := by
    exact hweight.of_norm_bounded (fun k ↦ by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      simpa using mul_le_of_le_one_right (Real.exp_nonneg _)
        (Real.abs_cos_le_one (2 * Real.pi * (k : ℝ) * x)))
  have hpoint : ∀ k : ℤ,
      Real.exp (-(Real.pi ^ 2 / Real.log p) * (k : ℝ) ^ 2) *
          Real.cos (2 * Real.pi * (k : ℝ) * x) ≤
        Real.exp (-(Real.pi ^ 2 / Real.log p) * (k : ℝ) ^ 2) := by
    intro k
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.cos_le_one (2 * Real.pi * (k : ℝ) * x))
      (Real.exp_nonneg ((-(Real.pi ^ 2 / Real.log p)) * (k : ℝ) ^ 2))
  have hsum := hcos.tsum_le_tsum hpoint hweight
  have hpref : 0 ≤ 1 / (Real.log p / Real.pi) ^ (1 / 2 : ℝ) := by positivity
  simpa using mul_le_mul_of_nonneg_left hsum hpref

private lemma cos_two_pi_lt_one_of_not_integer {x : ℝ}
    (hx : ¬ ∃ z : ℤ, (z : ℝ) = x) :
    Real.cos (2 * Real.pi * x) < 1 := by
  refine lt_of_le_of_ne (Real.cos_le_one _) ?_
  intro hcos
  obtain ⟨z, hz⟩ := (Real.cos_eq_one_iff _).mp hcos
  apply hx
  refine ⟨z, ?_⟩
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  apply mul_left_cancel₀ htwoPi
  calc
    2 * Real.pi * (z : ℝ) = (z : ℝ) * (2 * Real.pi) := by ring
    _ = 2 * Real.pi * x := by simpa [mul_assoc] using hz

/--
@isnad1 id=lt.2h2v.s5.f7794c3b3d36 from=translated src=- shape=7d6f5183 vocab=d939fc88
-/
lemma shiftedTheta_lt_of_not_integer {p x : ℝ} (hp : 1 < p)
    (hx : ¬ ∃ z : ℤ, (z : ℝ) = x) :
    shiftedTheta p x < gaussianTheta p := by
  have hA : 0 < Real.log p := Real.log_pos hp
  have hzero : (∑' z : ℤ, Real.exp (-Real.log p * (z : ℝ) ^ 2)) =
      1 / (Real.log p / Real.pi) ^ (1 / 2 : ℝ) *
        ∑' k : ℤ, Real.exp (-(Real.pi ^ 2 / Real.log p) * (k : ℝ) ^ 2) := by
    simpa using shifted_gaussian_fourier hA 0
  rw [shiftedTheta, gaussianTheta, shifted_gaussian_fourier hA x, hzero]
  let w : ℤ → ℝ := fun k ↦
    Real.exp (-(Real.pi ^ 2 / Real.log p) * (k : ℝ) ^ 2)
  have hw : Summable w := summable_int_gaussian (by positivity)
  have hwcos : Summable (fun k : ℤ ↦
      w k * Real.cos (2 * Real.pi * (k : ℝ) * x)) := by
    exact hw.of_norm_bounded (fun k ↦ by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      simpa [w] using mul_le_of_le_one_right (Real.exp_nonneg _)
        (Real.abs_cos_le_one (2 * Real.pi * (k : ℝ) * x)))
  have hpoint : ∀ k : ℤ,
      w k * Real.cos (2 * Real.pi * (k : ℝ) * x) ≤ w k := fun k ↦
    by
      dsimp only [w]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (Real.cos_le_one (2 * Real.pi * (k : ℝ) * x))
        (Real.exp_nonneg ((-(Real.pi ^ 2 / Real.log p)) * (k : ℝ) ^ 2))
  have hstrict : w 1 * Real.cos (2 * Real.pi * ((1 : ℤ) : ℝ) * x) < w 1 := by
    have hc := cos_two_pi_lt_one_of_not_integer hx
    have := mul_lt_mul_of_pos_left hc (Real.exp_pos
      (-(Real.pi ^ 2 / Real.log p) * ((1 : ℤ) : ℝ) ^ 2))
    simpa [w, mul_assoc] using this
  have hsum := hwcos.tsum_lt_tsum hpoint hstrict hw
  have hpref : 0 < 1 / (Real.log p / Real.pi) ^ (1 / 2 : ℝ) := by positivity
  simpa [w] using mul_lt_mul_of_pos_left hsum hpref

/--
@isnad1 id=eq.2h2v.s5.eaf832267a34 from=translated src=- shape=ab27d6b1 vocab=d939fc88
-/
lemma shiftedTheta_eq_of_integer {p x : ℝ} (hp : 1 < p)
    (hx : ∃ z : ℤ, (z : ℝ) = x) :
    shiftedTheta p x = gaussianTheta p := by
  obtain ⟨z, rfl⟩ := hx
  have hA : 0 < Real.log p := Real.log_pos hp
  have hzero : (∑' y : ℤ, Real.exp (-Real.log p * (y : ℝ) ^ 2)) =
      1 / (Real.log p / Real.pi) ^ (1 / 2 : ℝ) *
        ∑' k : ℤ, Real.exp (-(Real.pi ^ 2 / Real.log p) * (k : ℝ) ^ 2) := by
    simpa using shifted_gaussian_fourier hA 0
  rw [shiftedTheta, gaussianTheta, shifted_gaussian_fourier hA (z : ℝ), hzero]
  apply congrArg (fun t : ℝ ↦
    1 / (Real.log p / Real.pi) ^ (1 / 2 : ℝ) * t)
  apply tsum_congr
  intro k
  have hcos := Real.cos_int_mul_two_pi (k * z)
  have : Real.cos (2 * Real.pi * (k : ℝ) * (z : ℝ)) = 1 := by
    convert hcos using 1 <;> push_cast <;> ring
  rw [this, mul_one]

/-- Equality in the shifted-theta estimate holds exactly at integral shifts.
@isnad1 id=iff.1h2v.s5.264eb0354c8b from=translated src=- shape=05e08d57 vocab=d939fc88
-/
lemma shiftedTheta_eq_iff {p x : ℝ} (hp : 1 < p) :
    shiftedTheta p x = gaussianTheta p ↔ ∃ z : ℤ, (z : ℝ) = x := by
  constructor
  · intro h
    by_contra hx
    exact (shiftedTheta_lt_of_not_integer hp hx).ne h
  · exact shiftedTheta_eq_of_integer hp

/-- The finite analytic sum which occurs after the group-theoretic packing
argument.  Keeping it in exponential normal form makes all logarithmic
identities exact and robust.-/
noncomputable def finiteThetaSum (p L : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (Nat.floor L + 1),
    (gammaR p r)⁻¹ * Real.exp (Real.log p * (r : ℝ) * (L - r))

/-- Strict analytic upper bound for the finite sum.  The strictness comes from
the omitted tail of the reciprocal Euler product, so it remains strict even
when the shifted theta series itself is at a maximizing integral translate.
@isnad1 id=lt.2h2v.s6.75870f914bc2 from=translated src=- shape=68c3b254 vocab=62e9fa6b
-/
lemma finiteThetaSum_lt {p L : ℝ} (hp : 2 ≤ p) (hL : 0 ≤ L) :
    finiteThetaSum p L <
      sharpConstant p * Real.exp (Real.log p * L ^ 2 / 4) := by
  have hp1 : 1 < p := by linarith
  have hlog : 0 < Real.log p := Real.log_pos hp1
  let N := Nat.floor L + 1
  let center : ℝ := L / 2
  let g : ℤ → ℝ := fun z ↦ Real.exp (-Real.log p * ((z : ℝ) - center) ^ 2)
  have hg : Summable g := shiftedTheta_summable hp1
  have hfirst : finiteThetaSum p L <
      eulerC p * ∑ r ∈ Finset.range N,
        Real.exp (Real.log p * (r : ℝ) * (L - r)) := by
    unfold finiteThetaSum
    simp only [N]
    rw [Finset.mul_sum]
    refine Finset.sum_lt_sum (fun r hr ↦ ?_) ?_
    · exact mul_le_mul_of_nonneg_right (gammaR_inv_lt_eulerC hp r).le
        (Real.exp_nonneg _)
    · refine ⟨0, by simp, ?_⟩
      exact mul_lt_mul_of_pos_right (gammaR_inv_lt_eulerC hp 0) (Real.exp_pos _)
  have hcomplete :
      (∑ r ∈ Finset.range N,
        Real.exp (Real.log p * (r : ℝ) * (L - r))) =
        Real.exp (Real.log p * L ^ 2 / 4) *
          ∑ r ∈ Finset.range N, g (r : ℤ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← Real.exp_add]
    congr 1
    simp only [g, center, Int.cast_natCast]
    ring
  have hfinite_gauss : (∑ r ∈ Finset.range N, g (r : ℤ)) ≤ ∑' z : ℤ, g z := by
    let emb : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
    let s : Finset ℤ := (Finset.range N).map emb
    have hs : (∑ r ∈ Finset.range N, g (r : ℤ)) = ∑ z ∈ s, g z := by
      simp [s, emb]
    rw [hs]
    exact hg.sum_le_tsum s (fun z hz ↦ (Real.exp_pos _).le)
  have htheta : (∑' z : ℤ, g z) ≤ gaussianTheta p := by
    simpa [g, center, shiftedTheta] using shiftedTheta_le (p := p) (x := center) hp1
  calc
    finiteThetaSum p L
        < eulerC p * ∑ r ∈ Finset.range N,
            Real.exp (Real.log p * (r : ℝ) * (L - r)) := hfirst
    _ = eulerC p * (Real.exp (Real.log p * L ^ 2 / 4) *
          ∑ r ∈ Finset.range N, g (r : ℤ)) := by rw [hcomplete]
    _ ≤ eulerC p * (Real.exp (Real.log p * L ^ 2 / 4) * gaussianTheta p) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hfinite_gauss.trans htheta) (Real.exp_nonneg _))
        (eulerC_pos hp).le
    _ = sharpConstant p * Real.exp (Real.log p * L ^ 2 / 4) := by
      simp [sharpConstant]
      ring

end SharpIntermediateSubgroupBounds
