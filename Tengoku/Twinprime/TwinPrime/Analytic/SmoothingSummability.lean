import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusSmoothing
import Tengoku.Twinprime.TwinPrime.HardyLittlewood
import Tengoku.Seed.NumberTheory.EulerProduct.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Absolute summability and the Euler product of the smoothing correction

The local prime-power formulas give a summable bound for the excess of each
absolute Euler factor over one. Finite smooth-number sums then prove absolute
summability without an analytic cancellation hypothesis.
-/

noncomputable section

open Finset ArithmeticFunction Filter Topology

namespace TwinPrime.Analytic

set_option maxHeartbeats 600000

/-- A multiplicative function is norm summable when its absolute local Euler
factors have a summable nonnegative excess over one.
@isnad1 id=summable.4h2v.s7.20bf19f63ebe from=translated src=- shape=4094565c vocab=6bf5fc40
-/
theorem summable_norm_of_primePower_bound (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g)
    (hlocal : ∀ p : ℕ, p.Prime →
      Summable (fun k : ℕ => ‖f (p ^ k)‖) ∧
        (∑' k : ℕ, ‖f (p ^ k)‖) ≤ 1 + g p) :
    Summable (fun n : ℕ => ‖f n‖) := by
  apply summable_of_sum_range_le (fun n => norm_nonneg (f n))
    (c := Real.exp (∑' n, g n))
  intro N
  have hsmooth := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := fun n => ‖f n‖) (by simp [hf.map_one])
    (fun {m n} hmn => by rw [hf.map_mul_of_coprime hmn, norm_mul])
    (fun {p} hp => by simpa only [norm_norm] using (hlocal p hp).1) N
  have hsum : HasSum ((Nat.smoothNumbers N).indicator (fun n => ‖f n‖))
      (∏ p ∈ N.primesBelow, ∑' k : ℕ, ‖f (p ^ k)‖) :=
    hasSum_subtype_iff_indicator.mp hsmooth.2
  have heq : (∑ n ∈ range N, ‖f n‖) =
      ∑ n ∈ range N, (Nat.smoothNumbers N).indicator (fun n => ‖f n‖) n := by
    apply sum_congr rfl
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [Set.indicator]
    · rw [Set.indicator_of_mem
        (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn0) (mem_range.mp hn))]
  rw [heq]
  calc
    _ ≤ ∏ p ∈ N.primesBelow, ∑' k : ℕ, ‖f (p ^ k)‖ := by
      exact sum_le_hasSum _ (fun n _ => Set.indicator_nonneg (fun n _ => norm_nonneg _) _) hsum
    _ ≤ ∏ p ∈ N.primesBelow, (1 + g p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact tsum_nonneg (fun k => norm_nonneg _)
      · intro p hp
        exact (hlocal p (Nat.prime_of_mem_primesBelow hp)).2
    _ ≤ Real.exp (∑ p ∈ N.primesBelow, g p) := Real.prod_one_add_le_exp_sum _ hg0
    _ ≤ Real.exp (∑' p, g p) :=
      Real.exp_le_exp.mpr (hg.sum_le_tsum _ (fun p _ => hg0 p))

/--
@isnad1 id=hassum.0h0v.s5.036e278c4757 from=translated src=- shape=595a022f vocab=bfbbed14
-/
theorem hasSum_norm_smoothingCorrection_two_pow :
    HasSum (fun k : ℕ => ‖smoothingCorrection (2 ^ k)‖) 2 := by
  have h := hasSum_geometric_of_norm_lt_one (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)
  convert! h using 1
  · ext k
    rw [smoothingCorrection_two_pow, Real.norm_of_nonneg (by positivity), div_pow, one_pow]
  · norm_num

/--
@isnad1 id=hassum.0h0v.s5.a1ba2d73a883 from=translated src=- shape=b5bbd223 vocab=c9c3913d
-/
theorem hasSum_smoothingCorrection_two_pow :
    HasSum (fun k : ℕ => smoothingCorrection (2 ^ k)) 2 := by
  convert! hasSum_norm_smoothingCorrection_two_pow using 1
  ext k
  rw [smoothingCorrection_two_pow, Real.norm_of_nonneg (by positivity)]

/--
@isnad1 id=hassum.2h1v.s6.b2bd81b9260a from=translated src=- shape=64fb33ed vocab=426c3816
-/
theorem hasSum_smoothingCorrection_odd_prime_pow_succ (p : ℕ)
    (hp : p.Prime) (hpodd : Odd p) :
    HasSum (fun k : ℕ => smoothingCorrection (p ^ (k + 1)))
      (-1 / ((p : ℝ) - 1) ^ 2) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hgeom := (hasSum_geometric_of_norm_lt_one
    (show ‖(1 / (p : ℝ))‖ < 1 by
      rw [Real.norm_of_nonneg (by positivity)]
      exact (div_lt_one (by positivity)).mpr hpR)).mul_left
        (-1 / ((p : ℝ) * ((p : ℝ) - 1)))
  convert! hgeom using 1
  · ext k
    rw [smoothingCorrection_odd_prime_pow p k hp hpodd, pow_succ, div_pow, one_pow]
    field_simp
  · field_simp

/--
@isnad1 id=hassum.2h1v.s6.a95de5b11faa from=translated src=- shape=003cab92 vocab=f5cafcef
-/
theorem hasSum_smoothingCorrection_odd_prime_pow (p : ℕ)
    (hp : p.Prime) (hpodd : Odd p) :
    HasSum (fun k : ℕ => smoothingCorrection (p ^ k))
      (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have h := (hasSum_nat_add_iff (f := fun k : ℕ => smoothingCorrection (p ^ k)) 1).mp
    (hasSum_smoothingCorrection_odd_prime_pow_succ p hp hpodd)
  simpa only [sum_range_one, pow_zero, smoothingCorrection_one, neg_div,
    neg_add_eq_sub, add_comm, sub_eq_add_neg] using h

/--
@isnad1 id=hassum.2h1v.s6.30472a62ea16 from=translated src=- shape=4845d56f vocab=9b224c9e
-/
theorem hasSum_norm_smoothingCorrection_odd_prime_pow (p : ℕ)
    (hp : p.Prime) (hpodd : Odd p) :
    HasSum (fun k : ℕ => ‖smoothingCorrection (p ^ k)‖)
      (1 + 1 / ((p : ℝ) - 1) ^ 2) := by
  have hneg := (hasSum_smoothingCorrection_odd_prime_pow_succ p hp hpodd).neg
  have hnorm : HasSum (fun k : ℕ => ‖smoothingCorrection (p ^ (k + 1))‖)
      (1 / ((p : ℝ) - 1) ^ 2) := by
    convert! hneg using 1
    · ext k
      rw [smoothingCorrection_odd_prime_pow p k hp hpodd]
      have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      rw [Real.norm_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by norm_num)
        (mul_nonneg (pow_nonneg (by positivity) _) (by linarith)))]
    · ring
  have h := (hasSum_nat_add_iff (f := fun k : ℕ => ‖smoothingCorrection (p ^ k)‖) 1).mp hnorm
  simpa only [sum_range_one, pow_zero, smoothingCorrection_one, norm_one, add_comm] using h

/--
@isnad1 id=summable.0h0v.s4.282ef34af9fd from=translated src=- shape=b957a2d0 vocab=915f790b
-/
theorem summable_norm_smoothingCorrection :
    Summable (fun n : ℕ => ‖smoothingCorrection n‖) := by
  have hg : Summable (fun n : ℕ => 4 / (n : ℝ) ^ 2) := by
    simpa only [mul_one_div] using
      ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two).mul_left 4
  apply summable_norm_of_primePower_bound smoothingCorrection
    isMultiplicative_smoothingCorrection (fun n => 4 / (n : ℝ) ^ 2)
    (fun n => by positivity) hg
  intro p hp
  rcases hp.eq_two_or_odd with htwo | hodd
  · subst p
    exact ⟨hasSum_norm_smoothingCorrection_two_pow.summable, by
      rw [hasSum_norm_smoothingCorrection_two_pow.tsum_eq]
      norm_num⟩
  · have hodd : Odd p := Nat.odd_iff.mpr hodd
    refine ⟨(hasSum_norm_smoothingCorrection_odd_prime_pow p hp hodd).summable, ?_⟩
    rw [(hasSum_norm_smoothingCorrection_odd_prime_pow p hp hodd).tsum_eq]
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    apply add_le_add_right
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith

/--
@isnad1 id=summable.0h0v.s4.c250e8c314ff from=translated src=- shape=ddcca31f vocab=299d63fb
-/
theorem summable_smoothingCorrection : Summable smoothingCorrection :=
  summable_norm_smoothingCorrection.of_norm

/-- The exact local factors, including the separate contribution of the prime two.
@isnad1 id=eq.0h1v.s6.96fe8d7b2e6d from=translated src=- shape=48ab0b7f vocab=bb73eaa6
-/
theorem smoothingCorrection_eulerFactor (p : ℕ) :
    ({q : ℕ | q.Prime}.mulIndicator
      (fun q => ∑' k : ℕ, smoothingCorrection (q ^ k))) p =
      (if p = 2 then 2 else 1) * twinConstantFactor p := by
  by_cases hp : p.Prime
  · rw [Set.mulIndicator_of_mem (show p ∈ {q : ℕ | q.Prime} from hp)]
    by_cases hp2 : p = 2
    · subst p
      rw [hasSum_smoothingCorrection_two_pow.tsum_eq]
      norm_num [twinConstantFactor]
    · have hodd : Odd p := hp.odd_of_ne_two hp2
      have hgt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
      rw [(hasSum_smoothingCorrection_odd_prime_pow p hp hodd).tsum_eq]
      simp [hp2, twinConstantFactor, hp, hgt]
  · rw [Set.mulIndicator_of_notMem (show p ∉ {q : ℕ | q.Prime} from hp)]
    have hp2 : p ≠ 2 := by rintro rfl; exact hp Nat.prime_two
    simp [hp2, twinConstantFactor, hp]

/-- The correction has total mass exactly twice the twin-prime constant.
@isnad1 id=eq.0h0v.s5.8bf0a709758f from=translated src=- shape=9b90c598 vocab=193a7bc0
-/
theorem tsum_smoothingCorrection :
    (∑' n : ℕ, smoothingCorrection n) = 2 * twinPrimeConstant := by
  have heuler := EulerProduct.eulerProduct_hasProd_mulIndicator
    isMultiplicative_smoothingCorrection.map_one
    isMultiplicative_smoothingCorrection.map_mul_of_coprime
    summable_norm_smoothingCorrection
    (ArithmeticFunction.map_zero (f := smoothingCorrection))
  have hfactor := (hasProd_ite_eq (2 : ℕ) (2 : ℝ)).mul
    multipliable_twinConstantFactor.hasProd
  change HasProd (fun p : ℕ => (if p = 2 then 2 else 1) * twinConstantFactor p)
    (2 * twinPrimeConstant) at hfactor
  have heq := heuler.congr_fun (fun p => (smoothingCorrection_eulerFactor p).symm)
  exact heq.unique hfactor

/-- The correction weighted by the square root of its argument.-/
def sqrtWeightedSmoothingCorrection : ArithmeticFunction ℝ :=
  ⟨fun n => smoothingCorrection n * Real.sqrt n, by simp⟩

/--
@isnad1 id=eq.0h1v.s5.becabea42f34 from=translated src=- shape=9a598b35 vocab=5bcc45fa
-/
@[simp] theorem sqrtWeightedSmoothingCorrection_apply (n : ℕ) :
    sqrtWeightedSmoothingCorrection n = smoothingCorrection n * Real.sqrt n := rfl

/--
@isnad1 id=ismultip.0h0v.s2.dbde6f107389 from=translated src=- shape=25b03439 vocab=188a1c2d
-/
theorem isMultiplicative_sqrtWeightedSmoothingCorrection :
    sqrtWeightedSmoothingCorrection.IsMultiplicative := by
  refine ⟨by simp, fun {m n} hmn => ?_⟩
  simp only [sqrtWeightedSmoothingCorrection_apply,
    isMultiplicative_smoothingCorrection.map_mul_of_coprime hmn, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg m)]
  ring

private theorem sqrt_nat_pow (p k : ℕ) :
    Real.sqrt ((p : ℝ) ^ k) = Real.sqrt p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg p) k), ih, pow_succ]

/--
@isnad1 id=eq.0h1v.s6.1926fa2b9057 from=translated src=- shape=d3c04fe8 vocab=d04b6e79
-/
theorem norm_sqrtWeightedSmoothingCorrection_two_pow (k : ℕ) :
    ‖sqrtWeightedSmoothingCorrection (2 ^ k)‖ = (1 / Real.sqrt 2) ^ k := by
  simp only [sqrtWeightedSmoothingCorrection_apply, smoothingCorrection_two_pow,
    Nat.cast_pow, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / 2 ^ k),
    sqrt_nat_pow, norm_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc
    1 / (2 : ℝ) ^ k * Real.sqrt 2 ^ k = (Real.sqrt 2 / 2) ^ k := by rw [div_pow]; ring
    _ = _ := by rw [Real.sqrt_div_self']

/--
@isnad1 id=eq.2h2v.s6.dc05482f712c from=translated src=- shape=3b353770 vocab=338b256c
-/
theorem norm_sqrtWeightedSmoothingCorrection_odd_prime_pow (p k : ℕ)
    (hp : p.Prime) (hpodd : Odd p) :
    ‖sqrtWeightedSmoothingCorrection (p ^ (k + 1))‖ =
      (1 / Real.sqrt p) ^ (k + 1) / ((p : ℝ) - 1) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [sqrtWeightedSmoothingCorrection_apply, norm_mul,
    smoothingCorrection_odd_prime_pow p k hp hpodd,
    Real.norm_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg p) _) (by linarith))),
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Nat.cast_pow, sqrt_nat_pow]
  calc
    _ = (Real.sqrt p ^ (k + 1) / (p : ℝ) ^ (k + 1)) / ((p : ℝ) - 1) := by field_simp
    _ = _ := by rw [← div_pow, Real.sqrt_div_self']

/--
@isnad1 id=hassum.0h0v.s6.ce20d84ad760 from=translated src=- shape=58109ae9 vocab=0ca9d9f1
-/
theorem hasSum_norm_sqrtWeightedSmoothingCorrection_two_pow :
    HasSum (fun k : ℕ => ‖sqrtWeightedSmoothingCorrection (2 ^ k)‖)
      (Real.sqrt 2 / (Real.sqrt 2 - 1)) := by
  have hq : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  have h := hasSum_geometric_of_lt_one (by positivity : 0 ≤ 1 / Real.sqrt 2)
    ((div_lt_one (by positivity)).mpr hq)
  convert! h using 1
  · ext k; exact norm_sqrtWeightedSmoothingCorrection_two_pow k
  · have hq0 : Real.sqrt 2 ≠ 0 := by positivity
    have hq1 : Real.sqrt 2 - 1 ≠ 0 := by linarith
    field_simp

/--
@isnad1 id=hassum.2h1v.s6.e35f1ed18553 from=translated src=- shape=5909105b vocab=f87d3d90
-/
theorem hasSum_norm_sqrtWeightedSmoothingCorrection_odd_prime_pow (p : ℕ)
    (hp : p.Prime) (hpodd : Odd p) :
    HasSum (fun k : ℕ => ‖sqrtWeightedSmoothingCorrection (p ^ k)‖)
      (1 + 1 / (((p : ℝ) - 1) * (Real.sqrt p - 1))) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq : (1 : ℝ) < Real.sqrt p := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hpR)
  have hgeom := (hasSum_geometric_of_lt_one
    (by positivity : 0 ≤ 1 / Real.sqrt p)
    ((div_lt_one (by positivity)).mpr hq)).mul_left
      ((1 / Real.sqrt p) / ((p : ℝ) - 1))
  have htail : HasSum (fun k : ℕ => ‖sqrtWeightedSmoothingCorrection (p ^ (k + 1))‖)
      (1 / (((p : ℝ) - 1) * (Real.sqrt p - 1))) := by
    convert! hgeom using 1
    · ext k
      rw [norm_sqrtWeightedSmoothingCorrection_odd_prime_pow p k hp hpodd, pow_succ]
      ring
    · have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hq0 : Real.sqrt p ≠ 0 := by positivity
      have hq1 : Real.sqrt p - 1 ≠ 0 := by linarith
      field_simp
  have h := (hasSum_nat_add_iff
    (f := fun k : ℕ => ‖sqrtWeightedSmoothingCorrection (p ^ k)‖) 1).mp htail
  simpa only [sum_range_one, pow_zero, sqrtWeightedSmoothingCorrection_apply,
    smoothingCorrection_one, Nat.cast_one, Real.sqrt_one, mul_one, norm_one, add_comm] using h

/--
@isnad1 id=summable.0h0v.s4.0a1dfec0a061 from=translated src=- shape=b957a2d0 vocab=ecce2e89
-/
theorem summable_norm_sqrtWeightedSmoothingCorrection :
    Summable (fun n : ℕ => ‖sqrtWeightedSmoothingCorrection n‖) := by
  have hpseries : Summable (fun n : ℕ => 8 / ((n : ℝ) * Real.sqrt n)) := by
    have h := ((Real.summable_one_div_nat_rpow (p := 3 / 2)).mpr (by norm_num)).mul_left 8
    convert! h using 1
    ext n
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add_of_nonneg (Nat.cast_nonneg n) (by norm_num) (by norm_num),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    ring
  have hg : Summable (fun n : ℕ =>
      (if n = 2 then 3 else 0) + 8 / ((n : ℝ) * Real.sqrt n)) :=
    (hasSum_ite_eq (2 : ℕ) (3 : ℝ)).summable.add hpseries
  apply summable_norm_of_primePower_bound sqrtWeightedSmoothingCorrection
    isMultiplicative_sqrtWeightedSmoothingCorrection _ (fun n => by positivity) hg
  intro p hp
  by_cases hp2 : p = 2
  · subst p
    refine ⟨hasSum_norm_sqrtWeightedSmoothingCorrection_two_pow.summable, ?_⟩
    rw [hasSum_norm_sqrtWeightedSmoothingCorrection_two_pow.tsum_eq]
    have hq : (4 / 3 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
    have hq1 : 0 < Real.sqrt 2 - 1 := by linarith
    have hfour : Real.sqrt 2 / (Real.sqrt 2 - 1) ≤ 4 :=
      (div_le_iff₀ hq1).mpr (by linarith)
    norm_num only [ite_eq_left, Nat.cast_ofNat]
    have hpos : (0 : ℝ) ≤ 8 / (2 * Real.sqrt 2) := by positivity
    linarith
  · have hodd := hp.odd_of_ne_two hp2
    refine ⟨(hasSum_norm_sqrtWeightedSmoothingCorrection_odd_prime_pow p hp hodd).summable, ?_⟩
    rw [(hasSum_norm_sqrtWeightedSmoothingCorrection_odd_prime_pow p hp hodd).tsum_eq,
      ite_eq_right hp2, zero_add]
    apply add_le_add_right
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hq : (4 / 3 : ℝ) ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by linarith)
    have hp1 : 0 < (p : ℝ) - 1 := by linarith
    have hq1 : 0 < Real.sqrt p - 1 := by linarith
    have hmul := mul_le_mul
      (show (p : ℝ) ≤ 2 * ((p : ℝ) - 1) by linarith)
      (show Real.sqrt p ≤ 4 * (Real.sqrt p - 1) by linarith)
      (Real.sqrt_nonneg p) (show 0 ≤ 2 * ((p : ℝ) - 1) by linarith)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- A positive power moment, strong enough to control large-divisor tails.
@isnad1 id=summable.0h0v.s5.cabea9e836f0 from=translated src=- shape=b7186469 vocab=10bdf531
-/
theorem summable_sqrt_mul_abs_smoothingCorrection :
    Summable (fun n : ℕ => Real.sqrt n * |smoothingCorrection n|) := by
  convert! summable_norm_sqrtWeightedSmoothingCorrection using 1
  ext n
  simp [norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_comm]

/-- The logarithmic moment used in dominated convergence for the unsmoothed sum.
@isnad1 id=summable.0h0v.s6.4cd906506b88 from=translated src=- shape=06c26084 vocab=45cc98ed
-/
theorem summable_log_sq_mul_abs_smoothingCorrection :
    Summable (fun n : ℕ => (Real.log ((n : ℝ) + 1)) ^ 2 * |smoothingCorrection n|) := by
  have hsmall := ((isLittleO_log_rpow_rpow_atTop 2 (s := 1 / 2)
    (by norm_num)).comp_tendsto
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)).eventuallyLE
  apply Summable.of_norm_bounded_eventually (summable_sqrt_mul_abs_smoothingCorrection.mul_left 2)
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog : (Real.log ((n : ℝ) + 1)) ^ 2 ≤ Real.sqrt ((n : ℝ) + 1) := by
    simpa only [Function.comp_def, Real.rpow_two, ← Real.sqrt_eq_rpow, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.log ((n : ℝ) + 1))),
      abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt n := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      nlinarith
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _))]
  calc
    _ ≤ (2 * Real.sqrt n) * |smoothingCorrection n| :=
      mul_le_mul_of_nonneg_right (hlog.trans hsqrt) (abs_nonneg _)
    _ = _ := by ring

end TwinPrime.Analytic
