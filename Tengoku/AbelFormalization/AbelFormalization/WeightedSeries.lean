import Tengoku.Seed.RingTheory.MvPowerSeries.Basic
import Tengoku.Seed.Analysis.Normed.Ring.InfiniteSum
import Tengoku.Seed.Analysis.Normed.Field.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Weighted absolute coefficient sums

Nonnegative polyradii define multiplicative weights on multiindices. The
corresponding absolutely summable coefficient series are closed under the
formal Cauchy product, with the expected submultiplicative bound.
-/

noncomputable section

namespace AbelFormalization

open Finset

variable {σ : Type*}

/-- The monomial weight associated with a family of real radii.-/
def multiRadiusWeight (ρ : σ → ℝ) (d : σ →₀ ℕ) : ℝ :=
  d.prod (fun i n => ρ i ^ n)

/--
@isnad1 id=eq.0h2v.s5.55526e3bc816 from=translated src=- shape=4b63daf7 vocab=7d6413f8
-/
@[simp]
theorem multiRadiusWeight_zero (ρ : σ → ℝ) : multiRadiusWeight ρ 0 = 1 :=
  Finsupp.prod_zero_index

/--
@isnad1 id=eq.0h4v.s6.4143444bd7cb from=translated src=- shape=390d8631 vocab=a564ddfa
-/
theorem multiRadiusWeight_add (ρ : σ → ℝ) (d e : σ →₀ ℕ) :
    multiRadiusWeight ρ (d + e) = multiRadiusWeight ρ d * multiRadiusWeight ρ e :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

/--
@isnad1 id=le.1h3v.s5.684420bdb605 from=translated src=- shape=637b077f vocab=64725baa
-/
theorem multiRadiusWeight_nonneg {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (d : σ →₀ ℕ) :
    0 ≤ multiRadiusWeight ρ d :=
  Finset.prod_nonneg (fun i _ => pow_nonneg (hρ i) _)

/--
@isnad1 id=lt.1h3v.s5.2d039965d43e from=translated src=- shape=637b077f vocab=0318663d
-/
theorem multiRadiusWeight_pos {ρ : σ → ℝ} (hρ : ∀ i, 0 < ρ i) (d : σ →₀ ℕ) :
    0 < multiRadiusWeight ρ d :=
  Finset.prod_pos (fun i _ => pow_pos (hρ i) _)

/-- Absolute summability of the coefficients with the specified monomial weights.-/
def WeightedCoeffSummable (ρ : σ → ℝ) (f : MvPowerSeries σ ℝ) : Prop :=
  Summable (fun d => ‖MvPowerSeries.coeff d f‖ * multiRadiusWeight ρ d)

/-- The weighted absolute coefficient sum. It is a norm on the summable
subspace when all radii are positive.-/
def weightedCoeffNorm (ρ : σ → ℝ) (f : MvPowerSeries σ ℝ) : ℝ :=
  ∑' d, ‖MvPowerSeries.coeff d f‖ * multiRadiusWeight ρ d

/--
@isnad1 id=le.1h3v.s5.f35542415d1f from=translated src=- shape=d578531f vocab=87fa19c3
-/
theorem weightedCoeffNorm_nonneg {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    (f : MvPowerSeries σ ℝ) : 0 ≤ weightedCoeffNorm ρ f :=
  tsum_nonneg (fun d => mul_nonneg (norm_nonneg _) (multiRadiusWeight_nonneg hρ d))

/--
@isnad1 id=weighted.0h2v.s4.944b6d78cea2 from=translated src=- shape=e1e4f760 vocab=ed3926f6
-/
@[simp]
theorem weightedCoeffSummable_zero (ρ : σ → ℝ) :
    WeightedCoeffSummable ρ (0 : MvPowerSeries σ ℝ) := by
  simp [WeightedCoeffSummable]

/--
@isnad1 id=eq.0h2v.s4.5ee07d9b865b from=translated src=- shape=912654f8 vocab=6c71d31d
-/
@[simp]
theorem weightedCoeffNorm_zero (ρ : σ → ℝ) :
    weightedCoeffNorm ρ (0 : MvPowerSeries σ ℝ) = 0 := by
  simp [weightedCoeffNorm]

/--
@isnad1 id=weighted.0h2v.s4.4b8dba1873f6 from=translated src=- shape=e1e4f760 vocab=ed3926f6
-/
theorem weightedCoeffSummable_one (ρ : σ → ℝ) :
    WeightedCoeffSummable ρ (1 : MvPowerSeries σ ℝ) := by
  classical
  apply summable_of_ne_finset_zero (s := {0})
  intro d hd
  have hd' : d ≠ 0 := by simpa only [mem_singleton] using hd
  simp [MvPowerSeries.coeff_one, hd']

/--
@isnad1 id=eq.0h2v.s4.03609bbf3b36 from=translated src=- shape=912654f8 vocab=6c71d31d
-/
@[simp]
theorem weightedCoeffNorm_one (ρ : σ → ℝ) :
    weightedCoeffNorm ρ (1 : MvPowerSeries σ ℝ) = 1 := by
  classical
  unfold weightedCoeffNorm
  rw [tsum_eq_single 0 (fun d hd => by simp [MvPowerSeries.coeff_one, hd])]
  simp [MvPowerSeries.coeff_one]

/--
@isnad1 id=weighted.1h3v.s5.5f7843dffc78 from=translated src=- shape=595bf105 vocab=d8d79901
-/
theorem weightedCoeffSummable_neg {ρ : σ → ℝ} {f : MvPowerSeries σ ℝ}
    (hf : WeightedCoeffSummable ρ f) : WeightedCoeffSummable ρ (-f) := by
  simpa only [WeightedCoeffSummable, map_neg, norm_neg] using hf

/--
@isnad1 id=eq.0h3v.s5.b86cae05f390 from=translated src=- shape=f6e11fb3 vocab=d13f50d1
-/
@[simp]
theorem weightedCoeffNorm_neg (ρ : σ → ℝ) (f : MvPowerSeries σ ℝ) :
    weightedCoeffNorm ρ (-f) = weightedCoeffNorm ρ f := by
  simp only [weightedCoeffNorm, map_neg, norm_neg]

/--
@isnad1 id=weighted.1h4v.s5.665a87e73afa from=translated src=- shape=d0575ed0 vocab=d9fff8f6
-/
theorem weightedCoeffSummable_smul {ρ : σ → ℝ} {f : MvPowerSeries σ ℝ}
    (c : ℝ) (hf : WeightedCoeffSummable ρ f) : WeightedCoeffSummable ρ (c • f) := by
  simpa only [WeightedCoeffSummable, MvPowerSeries.coeff_smul, norm_mul, mul_assoc]
    using hf.mul_left ‖c‖

/--
@isnad1 id=eq.0h4v.s6.fd1115f547b1 from=translated src=- shape=d0956871 vocab=43f67391
-/
@[simp]
theorem weightedCoeffNorm_smul (ρ : σ → ℝ) (c : ℝ) (f : MvPowerSeries σ ℝ) :
    weightedCoeffNorm ρ (c • f) = ‖c‖ * weightedCoeffNorm ρ f := by
  simp only [weightedCoeffNorm, MvPowerSeries.coeff_smul, norm_mul, mul_assoc, tsum_mul_left]

/--
@isnad1 id=weighted.0h3v.s5.eb410502bd2a from=translated src=- shape=82fba8bb vocab=158f88be
-/
theorem weightedCoeffSummable_C (ρ : σ → ℝ) (c : ℝ) :
    WeightedCoeffSummable ρ (MvPowerSeries.C c) := by
  simpa only [MvPowerSeries.smul_eq_C_mul, mul_one] using
    weightedCoeffSummable_smul c (weightedCoeffSummable_one ρ)

/--
@isnad1 id=eq.0h3v.s5.da8570d6874f from=translated src=- shape=697d7a01 vocab=709a49ee
-/
@[simp]
theorem weightedCoeffNorm_C (ρ : σ → ℝ) (c : ℝ) :
    weightedCoeffNorm ρ (MvPowerSeries.C c) = ‖c‖ := by
  simpa only [MvPowerSeries.smul_eq_C_mul, mul_one, weightedCoeffNorm_one] using
    weightedCoeffNorm_smul ρ c (1 : MvPowerSeries σ ℝ)

/--
@isnad1 id=weighted.3h4v.s6.99619ab12039 from=translated src=- shape=59274098 vocab=9e3c4235
-/
theorem weightedCoeffSummable_add {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {f g : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f)
    (hg : WeightedCoeffSummable ρ g) : WeightedCoeffSummable ρ (f + g) := by
  apply (hf.add hg).of_nonneg_of_le
    (fun d => mul_nonneg (norm_nonneg _) (multiRadiusWeight_nonneg hρ d))
  intro d
  rw [map_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (multiRadiusWeight_nonneg hρ d)

/--
@isnad1 id=le.3h4v.s6.9259c7495060 from=translated src=- shape=ae58b8ef vocab=5f1e25fb
-/
theorem weightedCoeffNorm_add_le {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {f g : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f)
    (hg : WeightedCoeffSummable ρ g) :
    weightedCoeffNorm ρ (f + g) ≤ weightedCoeffNorm ρ f + weightedCoeffNorm ρ g := by
  rw [weightedCoeffNorm, weightedCoeffNorm, weightedCoeffNorm, ← hf.tsum_add hg]
  apply Summable.tsum_le_tsum _ (weightedCoeffSummable_add hρ hf hg) (hf.add hg)
  intro d
  rw [map_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (multiRadiusWeight_nonneg hρ d)

/-- The coefficientwise weighted Cauchy-product bound.
@isnad1 id=le.1h5v.s8.9925cd3bd21c from=translated src=- shape=42259907 vocab=5a61af8d
-/
theorem weightedCoeff_mul_le [DecidableEq σ] {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    (f g : MvPowerSeries σ ℝ) (d : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff d (f * g)‖ * multiRadiusWeight ρ d ≤
      ∑ e ∈ antidiagonal d,
        (‖MvPowerSeries.coeff e.1 f‖ * multiRadiusWeight ρ e.1) *
        (‖MvPowerSeries.coeff e.2 g‖ * multiRadiusWeight ρ e.2) := by
  classical
  rw [MvPowerSeries.coeff_mul]
  calc
    _ ≤ (∑ e ∈ antidiagonal d,
        ‖MvPowerSeries.coeff e.1 f * MvPowerSeries.coeff e.2 g‖) * multiRadiusWeight ρ d :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (multiRadiusWeight_nonneg hρ d)
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      rw [← mem_antidiagonal.mp he, multiRadiusWeight_add, norm_mul]
      ring

private theorem weightedCoeff_product_summable {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {f g : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f)
    (hg : WeightedCoeffSummable ρ g) :
    Summable (fun e : (σ →₀ ℕ) × (σ →₀ ℕ) =>
      (‖MvPowerSeries.coeff e.1 f‖ * multiRadiusWeight ρ e.1) *
      (‖MvPowerSeries.coeff e.2 g‖ * multiRadiusWeight ρ e.2)) :=
  hf.mul_of_nonneg hg
    (fun d => mul_nonneg (norm_nonneg _) (multiRadiusWeight_nonneg hρ d))
    (fun d => mul_nonneg (norm_nonneg _) (multiRadiusWeight_nonneg hρ d))

private theorem weightedCoeff_antidiagonal_summable [DecidableEq σ]
    {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {f g : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f)
    (hg : WeightedCoeffSummable ρ g) :
    Summable (fun d : σ →₀ ℕ => ∑ e ∈ antidiagonal d,
      (‖MvPowerSeries.coeff e.1 f‖ * multiRadiusWeight ρ e.1) *
      (‖MvPowerSeries.coeff e.2 g‖ * multiRadiusWeight ρ e.2)) :=
  summable_sum_mul_antidiagonal_of_summable_mul
    (f := fun d : σ →₀ ℕ => ‖MvPowerSeries.coeff d f‖ * multiRadiusWeight ρ d)
    (g := fun d : σ →₀ ℕ => ‖MvPowerSeries.coeff d g‖ * multiRadiusWeight ρ d)
    (weightedCoeff_product_summable hρ hf hg)

/-- Weighted absolute summability is preserved by the formal Cauchy product.
@isnad1 id=weighted.3h4v.s5.66e68ed2acf3 from=translated src=- shape=59274098 vocab=3e1f5fae
-/
theorem weightedCoeffSummable_mul {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {f g : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f)
    (hg : WeightedCoeffSummable ρ g) : WeightedCoeffSummable ρ (f * g) := by
  classical
  exact (weightedCoeff_antidiagonal_summable hρ hf hg).of_nonneg_of_le
    (fun d => mul_nonneg (norm_nonneg _) (multiRadiusWeight_nonneg hρ d))
    (weightedCoeff_mul_le hρ f g)

/-- The weighted absolute coefficient norm is submultiplicative.
@isnad1 id=le.3h4v.s6.abd575bc8b20 from=translated src=- shape=ae58b8ef vocab=1c75b330
-/
theorem weightedCoeffNorm_mul_le {ρ : σ → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {f g : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f)
    (hg : WeightedCoeffSummable ρ g) :
    weightedCoeffNorm ρ (f * g) ≤ weightedCoeffNorm ρ f * weightedCoeffNorm ρ g := by
  classical
  have hprod := weightedCoeff_product_summable hρ hf hg
  have he := Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (f := fun d : σ →₀ ℕ => ‖MvPowerSeries.coeff d f‖ * multiRadiusWeight ρ d)
    (g := fun d : σ →₀ ℕ => ‖MvPowerSeries.coeff d g‖ * multiRadiusWeight ρ d)
    hf hg hprod
  rw [weightedCoeffNorm, weightedCoeffNorm, weightedCoeffNorm, he]
  exact Summable.tsum_le_tsum (weightedCoeff_mul_le hρ f g)
    (weightedCoeffSummable_mul hρ hf hg)
    (weightedCoeff_antidiagonal_summable hρ hf hg)

end AbelFormalization
