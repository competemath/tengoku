import Tengoku.Pi2Lean.Row12.NativeSeries
import Tengoku.Seed.MeasureTheory.Integral.DominatedConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.coefficient_eq_uniformMoment` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.angularWeight_nonneg` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.angularMajorant_summable` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.angularLoaded_summable` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.term_hasSum_uniformIntegral` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.term_tsum_uniformIntegral` (it only prints; the queue checks the axioms of every declaration). -/

open MeasureTheory Set intervalIntegral
open scoped Interval

namespace Row12

/--
@isnad1 id=eq.0h1v.s6.9674560a13fc from=translated src=- shape=9ea51e18 vocab=b7fc5020
-/
theorem coefficient_eq_uniformMoment (n : ℕ) :
    coefficient n = rho ^ n * (6*(n : ℝ)+1) * coefficient3 n ^ 2 * uniformMoment (3*n) := by
  have hrp : rho ^ n = (6 : ℝ) ^ (6*n) / (10 : ℝ) ^ (6*n) := by
    rw [pow_mul, pow_mul, ← div_pow]
    norm_num [rho]
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : 6*(n : ℝ)+1 ≠ 0 := by positivity
  rw [mul_assoc (rho ^ n * (6*(n : ℝ)+1)), coefficient3_sq_mul_uniformMoment, hrp]
  unfold coefficient
  field_simp [hfac, hn]

noncomputable def angularWeight (n : ℕ) : ℝ := (6*(n : ℝ)+1) * weight n

noncomputable def angularLoaded (q : ℝ) : ℝ :=
  ∑' n : ℕ, coefficient3 n ^ 2 * angularWeight n * q ^ n

/--
@isnad1 id=le.0h1v.s3.72e1df4dde56 from=translated src=- shape=b9369acb vocab=b3be67eb
-/
theorem angularWeight_nonneg (n : ℕ) : 0 ≤ angularWeight n := by
  unfold angularWeight weight
  positivity

/--
@isnad1 id=summable.1h1v.s5.39364c2d9fde from=translated src=- shape=377dcba5 vocab=4f21ffb3
-/
theorem angularMajorant_summable {q : ℝ} (hq : |q| < 1) :
    Summable (fun n : ℕ => angularWeight n * q ^ n) := by
  have h3 := (summable_pow_mul_geometric_of_norm_lt_one 3 hq).mul_left (3192 : ℝ)
  have h2 := (summable_pow_mul_geometric_of_norm_lt_one 2 hq).mul_left (1288 : ℝ)
  have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 hq).mul_left (180 : ℝ)
  have h0 := (summable_geometric_of_norm_lt_one hq).mul_left (9 : ℝ)
  exact (((h3.add h2).add h1).add h0).congr (fun n => by
    simp only [angularWeight, weight, pow_one]
    ring)

/--
@isnad1 id=summable.2h1v.s6.7e406ee69c35 from=translated src=- shape=db21445c vocab=d62488b3
-/
theorem angularLoaded_summable {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => coefficient3 n ^ 2 * angularWeight n * q ^ n) := by
  have hq : |q| < 1 := by rwa [abs_of_nonneg hq0]
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg (sq_nonneg _) (angularWeight_nonneg n))
      (pow_nonneg hq0 n)) _ (angularMajorant_summable hq)
  intro n
  have ha : coefficient3 n ^ 2 ≤ 1 := pow_le_one₀ (coefficient3_nonneg n) (coefficient3_le_one n)
  calc
    coefficient3 n ^ 2 * angularWeight n * q ^ n ≤ 1 * angularWeight n * q ^ n := by
      gcongr
      exact angularWeight_nonneg n
    _ = angularWeight n * q ^ n := by ring

/--
@isnad1 id=hassum.0h0v.s6.1a011382f614 from=translated src=- shape=c9783c0d vocab=dd340ced
-/
theorem term_hasSum_uniformIntegral :
    HasSum term (∫ u : ℝ in 0..1, angularLoaded (rho*(1-u^2)^3)) := by
  have hr0 : 0 ≤ rho := by norm_num [rho]
  have hr1 : rho < 1 := by norm_num [rho]
  let B : ℕ → ℝ := fun n => coefficient3 n ^ 2 * angularWeight n * rho ^ n
  have hB : Summable B := angularLoaded_summable hr0 hr1
  have hx (u : ℝ) (hu : u ∈ Ι (0 : ℝ) 1) : 0 ≤ 1-u^2 ∧ 1-u^2 ≤ 1 := by
    rw [uIoc_of_le zero_le_one] at hu
    constructor
    · exact sub_nonneg.mpr (pow_le_one₀ hu.1.le hu.2)
    · nlinarith [sq_nonneg u]
  have hq (u : ℝ) (hu : u ∈ Ι (0 : ℝ) 1) :
      0 ≤ rho*(1-u^2)^3 ∧ rho*(1-u^2)^3 < 1 := by
    constructor
    · exact mul_nonneg hr0 (pow_nonneg (hx u hu).1 3)
    · have hp : (1-u^2)^3 ≤ 1 := pow_le_one₀ (hx u hu).1 (hx u hu).2
      exact ((mul_le_mul_of_nonneg_left hp hr0).trans_eq (mul_one rho)).trans_lt hr1
  have hint (n : ℕ) : IntervalIntegrable
      (fun u : ℝ => coefficient3 n ^ 2 * angularWeight n * (rho*(1-u^2)^3)^n) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := volume)
    (F := fun n u => coefficient3 n ^ 2 * angularWeight n * (rho*(1-u^2)^3)^n)
    (f := fun u => angularLoaded (rho*(1-u^2)^3))
    (fun n _ => B n)
    (fun n => (hint n).aestronglyMeasurable_restrict_uIoc)
    (fun n => Filter.Eventually.of_forall (fun u hu => by
      rw [Real.norm_of_nonneg (mul_nonneg
        (mul_nonneg (sq_nonneg _) (angularWeight_nonneg n)) (pow_nonneg (hq u hu).1 n))]
      have hle : rho*(1-u^2)^3 ≤ rho := by
        exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (hx u hu).1 (hx u hu).2) hr0).trans_eq (mul_one rho)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hq u hu).1 hle n)
        (mul_nonneg (sq_nonneg _) (angularWeight_nonneg n))))
    (Filter.Eventually.of_forall (fun _ _ => hB))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ∑' n : ℕ, B n) volume 0 1)
    (Filter.Eventually.of_forall (fun u hu => (angularLoaded_summable (hq u hu).1 (hq u hu).2).hasSum))
  apply hsum.congr_fun
  intro n
  have he : (fun u : ℝ => coefficient3 n ^ 2 * angularWeight n * (rho*(1-u^2)^3)^n) =
      (fun u : ℝ => (coefficient3 n ^ 2 * angularWeight n * rho ^ n) * (1-u^2)^(3*n)) := by
    funext u
    rw [mul_pow, ← pow_mul]
    ring
  rw [he, intervalIntegral.integral_const_mul]
  change term n = (coefficient3 n ^ 2 * angularWeight n * rho ^ n) * uniformMoment (3*n)
  rw [term_eq_coefficient_mul_weight, coefficient_eq_uniformMoment]
  unfold angularWeight
  ring

/--
@isnad1 id=eq.0h0v.s6.48d2c66b390b from=translated src=- shape=52d3579d vocab=6c39b397
-/
theorem term_tsum_uniformIntegral :
    (∑' n : ℕ, term n) = ∫ u : ℝ in 0..1, angularLoaded (rho*(1-u^2)^3) :=
  term_hasSum_uniformIntegral.tsum_eq

end Row12

