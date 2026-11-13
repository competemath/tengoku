import Tengoku.Seed.Analysis.SpecialFunctions.Log.Summable
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Chapter 2 — Part I: First proof of Jacobi's triple product (functional equation)

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 2, pp. 5–10.)

Chapter 2 proves Jacobi's triple product identity by exhibiting a function
that satisfies a functional equation `F(qz) = (1 + z) F(z)` and pinning it
down via growth/uniqueness arguments.

Truncated forms of the product and bilateral series are defined here as
recursive `def`s; the infinite forms `jacobiInfiniteProduct` and
`jacobiInfiniteSeries` use Mathlib's `tprod` and `tsum`. The final identity
`jacobiTripleProduct` is proved in `Chapter03.lean`, where the finite-JTP
machinery needed for the Gaussian-tail argument is available.
-/

namespace QseriesFormalization
namespace PartI
namespace Ch02

section Field

variable {R : Type*} [Field R]

/-- Finite approximation of the product side in Jacobi's triple product.-/
def jacobiProductTrunc (q z : R) : Nat → R
  | 0 => 1
  | Nat.succ n =>
      jacobiProductTrunc q z n *
        (1 - q ^ (Nat.succ n)) *
        (1 + z * q ^ n) *
        (1 + (q ^ (Nat.succ n)) / z)

/--
@isnad1 id=eq.0h3v.s5.68f5dc41a449 from=translated src=- shape=9c02e61a vocab=019d7dd4
-/
@[simp] theorem jacobiProductTrunc_zero (q z : R) : jacobiProductTrunc q z 0 = 1 := rfl

/--
@isnad1 id=eq.0h4v.s8.385cb4f30f91 from=translated src=- shape=9af2c951 vocab=34c5d82e
-/
@[simp] theorem jacobiProductTrunc_succ (q z : R) (n : Nat) :
    jacobiProductTrunc q z (Nat.succ n) =
      jacobiProductTrunc q z n *
        (1 - q ^ (Nat.succ n)) *
        (1 + z * q ^ n) *
        (1 + (q ^ (Nat.succ n)) / z) := rfl

/--
@isnad1 id=eq.0h3v.s7.e1e20b33227b from=translated src=- shape=038120ba vocab=1b998cb0
-/
theorem jacobiProductTrunc_one (q z : R) :
    jacobiProductTrunc q z 1 =
      (1 - q) * (1 + z) * (1 + q / z) := by
  simp [jacobiProductTrunc]

/-- Symmetric finite approximation of the bilateral series side.-/
def jacobiSeriesTrunc (q z : R) : Nat → R
  | 0 => 1
  | Nat.succ n =>
      jacobiSeriesTrunc q z n +
        z ^ (Nat.succ n) * q ^ (triangular (Nat.succ n)) +
        (Inv.inv z) ^ (Nat.succ n) * q ^ (triangular (Nat.succ n))

/--
@isnad1 id=eq.0h3v.s5.bb8da9aa9c17 from=translated src=- shape=9c02e61a vocab=665a4512
-/
@[simp] theorem jacobiSeriesTrunc_zero (q z : R) : jacobiSeriesTrunc q z 0 = 1 := rfl

/--
@isnad1 id=eq.0h4v.s7.a7f5b7e00118 from=translated src=- shape=2dc666c7 vocab=a67d1d19
-/
@[simp] theorem jacobiSeriesTrunc_succ (q z : R) (n : Nat) :
    jacobiSeriesTrunc q z (Nat.succ n) =
      jacobiSeriesTrunc q z n +
        z ^ (Nat.succ n) * q ^ (triangular (Nat.succ n)) +
        (Inv.inv z) ^ (Nat.succ n) * q ^ (triangular (Nat.succ n)) := rfl

/--
@isnad1 id=eq.0h3v.s6.6aabfd79f0d4 from=translated src=- shape=32b34f69 vocab=6734dfad
-/
theorem jacobiSeriesTrunc_one (q z : R) :
    jacobiSeriesTrunc q z 1 =
      1 + z * q + z⁻¹ * q := by
  simp [jacobiSeriesTrunc, triangular]

/-- Functional equation studied in Chapter 2: `F (q · z) = (1 + z) F z`.-/
def SatisfiesFunctionalEquation (F : R → R) (q : R) : Prop :=
  ∀ z : R, F (q * z) = (1 + z) * F z

end Field

section InfiniteForms

open Filter
open scoped Topology

/--
The infinite Jacobi triple product side
`∏_{n=1}^∞ (1 - q^{2n})(1 + z q^{2n-1})(1 + z⁻¹ q^{2n-1})`.
Returns 1 if the family is not multipliable, following Mathlib's `tprod`
convention.-/
noncomputable def jacobiInfiniteProduct (q z : ℂ) : ℂ :=
  ∏' n : ℕ+, (1 - q ^ (2 * n.val)) *
    (1 + z * q ^ (2 * n.val - 1)) *
    (1 + z⁻¹ * q ^ (2 * n.val - 1))

/-- The even product factor, Nat-indexed from exponent `2`.-/
def jacobiProductEvenFactor (q : ℂ) (n : ℕ) : ℂ :=
  1 - q ^ (2 * (n + 1))

/-- One odd product factor family, Nat-indexed from exponent `1`.-/
def jacobiProductOddFactor (q c : ℂ) (n : ℕ) : ℂ :=
  1 + c * q ^ (2 * (n + 1) - 1)

/-- The full Nat-indexed product factor for Chapter 2's JTP product side.-/
noncomputable def jacobiProductNatFactor (q z : ℂ) (n : ℕ) : ℂ :=
  jacobiProductEvenFactor q n * jacobiProductOddFactor q z n *
    jacobiProductOddFactor q z⁻¹ n

/-- The zero-based finite product corresponding to the infinite JTP product side.-/
noncomputable def jacobiProductPartial (q z : ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, jacobiProductNatFactor q z n

/-- N=0 sanity for `jacobiProductPartial`.
@isnad1 id=eq.0h2v.s4.d47224ce7d55 from=translated src=- shape=4f096759 vocab=22f60a61
-/
@[simp] theorem jacobiProductPartial_zero (q z : ℂ) :
    jacobiProductPartial q z 0 = 1 := by
  simp [jacobiProductPartial]

/-- Recursion: `jacobiProductPartial q z (N+1) =
jacobiProductPartial q z N * jacobiProductNatFactor q z N`.
Pulls the `Finset.prod_range_succ` step out so downstream truncation
work can recurse on `N` without re-expanding the product.
@isnad1 id=eq.0h3v.s5.5db65d662837 from=translated src=- shape=065909a1 vocab=ba49afdc
-/
theorem jacobiProductPartial_succ (q z : ℂ) (N : ℕ) :
    jacobiProductPartial q z (N + 1) =
      jacobiProductPartial q z N * jacobiProductNatFactor q z N := by
  rw [jacobiProductPartial, Finset.prod_range_succ]
  rfl

/-- The zero-based finite product is the expected product of three q-Pochhammer factors.
@isnad1 id=eq.0h3v.s7.fe508ba758e9 from=translated src=- shape=7a6fa945 vocab=14398ef2
-/
theorem jacobiProductPartial_eq_qPoch (q z : ℂ) (N : ℕ) :
    jacobiProductPartial q z N =
      qPoch (q ^ 2) (q ^ 2) N * qPoch (-(z * q)) (q ^ 2) N *
        qPoch (-(z⁻¹ * q)) (q ^ 2) N := by
  induction N with
  | zero =>
      simp [jacobiProductPartial]
  | succ N ih =>
      rw [jacobiProductPartial, Finset.prod_range_succ]
      change jacobiProductPartial q z N * jacobiProductNatFactor q z N =
        qPoch (q ^ 2) (q ^ 2) (N + 1) * qPoch (-(z * q)) (q ^ 2) (N + 1) *
          qPoch (-(z⁻¹ * q)) (q ^ 2) (N + 1)
      rw [ih]
      have heven : q ^ 2 * (q ^ 2) ^ N = q ^ (2 * (N + 1)) := by
        rw [show q ^ 2 * (q ^ 2) ^ N = (q ^ 2) ^ (N + 1) by
          rw [pow_succ]
          ring]
        rw [pow_mul]
      have hodd : z * q * (q ^ 2) ^ N = z * q ^ (2 * (N + 1) - 1) := by
        rw [show z * q * (q ^ 2) ^ N = z * (q * (q ^ 2) ^ N) by ring]
        rw [show q * (q ^ 2) ^ N = q ^ (2 * (N + 1) - 1) by
          rw [show 2 * (N + 1) - 1 = 1 + 2 * N by omega]
          rw [pow_add, pow_mul]
          simp]
      have hoddInv : z⁻¹ * q * (q ^ 2) ^ N = z⁻¹ * q ^ (2 * (N + 1) - 1) := by
        rw [show z⁻¹ * q * (q ^ 2) ^ N = z⁻¹ * (q * (q ^ 2) ^ N) by ring]
        rw [show q * (q ^ 2) ^ N = q ^ (2 * (N + 1) - 1) by
          rw [show 2 * (N + 1) - 1 = 1 + 2 * N by omega]
          rw [pow_add, pow_mul]
          simp]
      simp [jacobiProductNatFactor, jacobiProductEvenFactor, jacobiProductOddFactor,
        heven, hodd, hoddInv]
      ring

/-- The product-side definition can be read as a Nat-indexed product starting at `n = 0`.
@isnad1 id=eq.0h2v.s5.05d4f29740c0 from=translated src=- shape=25c142fc vocab=ad598c77
-/
theorem jacobiInfiniteProduct_eq_tprod_natFactor (q z : ℂ) :
    jacobiInfiniteProduct q z = ∏' n : ℕ, jacobiProductNatFactor q z n := by
  rw [jacobiInfiniteProduct]
  rw [tprod_pnat_eq_tprod_succ (f := fun m : ℕ => (1 - q ^ (2 * m)) *
    (1 + z * q ^ (2 * m - 1)) * (1 + z⁻¹ * q ^ (2 * m - 1)))]
  simp [jacobiProductNatFactor, jacobiProductEvenFactor, jacobiProductOddFactor]

/-- The bilateral series `∑_{n = -∞}^{∞} z^n q^{n^2}`.-/
noncomputable def jacobiInfiniteSeries (q z : ℂ) : ℂ :=
  ∑' n : ℤ, z ^ n * q ^ (n ^ 2)

/-- The symmetric finite partial sum of the bilateral JTP series.-/
noncomputable def jacobiSeriesSymmetricPartial (q z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), z ^ n * q ^ (n ^ 2)

/-- The pair of symmetric nonzero terms added at height `n + 1`.-/
noncomputable def jacobiSeriesSymmetricPairTerm (q z : ℂ) (n : ℕ) : ℂ :=
  z ^ (-(((n + 1 : ℕ) : ℤ))) * q ^ ((-(((n + 1 : ℕ) : ℤ))) ^ 2) +
    z ^ (((n + 1 : ℕ) : ℤ)) * q ^ ((((n + 1 : ℕ) : ℤ)) ^ 2)

/-- The sum of the norms of the two summands in a symmetric nonzero pair.-/
noncomputable def jacobiSeriesSymmetricPairNormMajorant (q z : ℂ) (n : ℕ) : ℝ :=
  ‖z ^ (-(((n + 1 : ℕ) : ℤ))) * q ^ ((-(((n + 1 : ℕ) : ℤ))) ^ 2)‖ +
    ‖z ^ (((n + 1 : ℕ) : ℤ)) * q ^ ((((n + 1 : ℕ) : ℤ)) ^ 2)‖

/-- The sum of the first `N` symmetric nonzero term pairs.-/
noncomputable def jacobiSeriesSymmetricPairPartial (q z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, jacobiSeriesSymmetricPairTerm q z n

/--
@isnad1 id=eq.0h2v.s4.00f59cb3b8ca from=translated src=- shape=4f096759 vocab=f44400f9
-/
@[simp] theorem jacobiSeriesSymmetricPairPartial_zero (q z : ℂ) :
    jacobiSeriesSymmetricPairPartial q z 0 = 0 := by
  simp [jacobiSeriesSymmetricPairPartial]

/-- The finite symmetric nonzero-pair tail from indices `M, ..., K - 1`.-/
noncomputable def jacobiSeriesSymmetricPairTail (q z : ℂ) (M K : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico M K, jacobiSeriesSymmetricPairTerm q z n

/--
@isnad1 id=eq.0h2v.s4.d63d4292ebbb from=translated src=- shape=4f096759 vocab=688a2ed8
-/
@[simp] theorem jacobiSeriesSymmetricPartial_zero (q z : ℂ) :
    jacobiSeriesSymmetricPartial q z 0 = 1 := by
  simp [jacobiSeriesSymmetricPartial]

/-- Symmetric partial sums grow by adding the next negative and positive exponent terms.
@isnad1 id=eq.0h3v.s5.e27990f45f27 from=translated src=- shape=57e7fe67 vocab=bd832f26
-/
theorem jacobiSeriesSymmetricPartial_succ (q z : ℂ) (N : ℕ) :
    jacobiSeriesSymmetricPartial q z (N + 1) =
      jacobiSeriesSymmetricPartial q z N + jacobiSeriesSymmetricPairTerm q z N := by
  simp only [jacobiSeriesSymmetricPartial, jacobiSeriesSymmetricPairTerm]
  norm_num only [Int.natCast_add, Int.natCast_one]
  rw [Finset.Icc_succ_succ N N]
  have hdisj : Disjoint (Finset.Icc (-(N : ℤ)) (N : ℤ))
      ({-((N : ℤ) + 1), (N : ℤ) + 1} : Finset ℤ) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp [Finset.mem_Icc] at ha hb
    rcases hb with hb | hb <;> omega
  rw [Finset.sum_union hdisj]
  rw [Finset.sum_pair (by omega)]

/-- A symmetric partial sum is the zero term plus the first `N` nonzero symmetric pairs.
@isnad1 id=eq.0h3v.s4.b76fd2ab4457 from=translated src=- shape=24ca8c63 vocab=8dc1d83f
-/
theorem jacobiSeriesSymmetricPartial_eq_one_add_pairPartial (q z : ℂ) (N : ℕ) :
    jacobiSeriesSymmetricPartial q z N =
      1 + jacobiSeriesSymmetricPairPartial q z N := by
  induction N with
  | zero =>
      simp [jacobiSeriesSymmetricPairPartial]
  | succ N ih =>
      rw [jacobiSeriesSymmetricPartial_succ, ih]
      simp [jacobiSeriesSymmetricPairPartial, Finset.sum_range_succ]
      ring

/--
The one-sided Jacobi series is summable for `‖q‖ < 1`.
The proof uses the quadratic exponent to dominate the terms by a geometric
series: eventually `‖z‖ * ‖q‖^n ≤ 1/2`.
@isnad1 id=summable.1h2v.s6.85ce6d8a9751 from=translated src=- shape=6757ab6d vocab=86b45335
-/
theorem summable_jacobiSeries_nat (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => z ^ n * q ^ (n * n) := by
  refine Summable.of_norm_bounded_eventually (g := fun n : ℕ => ((1 / 2 : ℝ) ^ n))
    ?hgeom ?hbound
  · exact summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  · have hqpow : Tendsto (fun n : ℕ => ‖q‖ ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq
    have hscale : Tendsto (fun n : ℕ => ‖z‖ * ‖q‖ ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hqpow :
        Tendsto (fun n : ℕ => ‖z‖ * ‖q‖ ^ n) atTop (𝓝 (‖z‖ * 0)))
    have hev_atTop : ∀ᶠ n : ℕ in atTop, ‖z‖ * ‖q‖ ^ n ≤ (1 / 2 : ℝ) :=
      hscale.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    have hev : ∀ᶠ n : ℕ in cofinite, ‖z‖ * ‖q‖ ^ n ≤ (1 / 2 : ℝ) := by
      rw [Filter.eventually_cofinite]
      rcases Filter.eventually_atTop.mp hev_atTop with ⟨N, hN⟩
      refine (Set.finite_lt_nat N).subset ?_
      intro n hn
      simp only [Set.mem_ofPred_eq] at hn ⊢
      by_contra hlt
      exact hn (hN n (le_of_not_gt hlt))
    filter_upwards [hev] with n hn
    have hbase_nonneg : 0 ≤ ‖z‖ * ‖q‖ ^ n :=
      mul_nonneg (norm_nonneg z) (pow_nonneg (norm_nonneg q) n)
    have hnorm : ‖z ^ n * q ^ (n * n)‖ = (‖z‖ * ‖q‖ ^ n) ^ n := by
      rw [norm_mul, norm_pow, norm_pow, pow_mul, mul_pow]
    rw [hnorm]
    exact pow_le_pow_left₀ hbase_nonneg hn n

/-- The bilateral Jacobi series defining `jacobiInfiniteSeries` is summable for `‖q‖ < 1`.
@isnad1 id=summable.1h2v.s6.05bb4c99ca57 from=translated src=- shape=b06bad65 vocab=06d3d4cd
-/
theorem summable_jacobiInfiniteSeries_terms (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℤ => z ^ n * q ^ (n ^ 2) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · exact (summable_jacobiSeries_nat q z hq).congr fun n => by
      have hsq : ((n : ℤ) ^ 2) = ((n * n : ℕ) : ℤ) := by
        norm_num [sq, Int.natCast_mul]
      rw [zpow_natCast, hsq, zpow_natCast]
  · exact (summable_jacobiSeries_nat q z⁻¹ hq).congr fun n => by
      have hsq : (-(n : ℤ)) ^ 2 = ((n * n : ℕ) : ℤ) := by
        norm_num [sq, Int.natCast_mul]
      rw [hsq, zpow_natCast]
      simp [zpow_neg, zpow_natCast, inv_pow]

/-- A constant multiple of a geometric sequence has summable norms.
@isnad1 id=summable.1h2v.s5.93e364479b55 from=translated src=- shape=61e051d3 vocab=86b45335
-/
theorem summable_norm_mul_geometric_complex (c r : ℂ) (hr : ‖r‖ < 1) :
    Summable fun n : ℕ => ‖c * r ^ n‖ := by
  exact summable_norm_iff.mpr ((summable_geometric_of_norm_lt_one hr).mul_left c)

private theorem summable_norm_jacobiProduct_first_tail (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun k : ℕ => ‖-q ^ (2 * (k + 1))‖ := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := summable_norm_mul_geometric_complex (-(q ^ 2)) (q ^ 2) hq2
  refine h.congr fun k => ?_
  congr 1
  rw [show -q ^ 2 * (q ^ 2) ^ k = -((q ^ 2) ^ (k + 1)) by
    rw [pow_succ]
    ring]
  rw [pow_mul]

private theorem summable_norm_jacobiProduct_odd_tail (q c : ℂ) (hq : ‖q‖ < 1) :
    Summable fun k : ℕ => ‖c * q ^ (2 * (k + 1) - 1)‖ := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := summable_norm_mul_geometric_complex (c * q) (q ^ 2) hq2
  refine h.congr fun k => ?_
  congr 1
  have hexp : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [hexp]
  rw [show c * q * (q ^ 2) ^ k = c * q ^ (2 * k + 1) by
    have hqpow : q * (q ^ 2) ^ k = q ^ (2 * k + 1) := by
      rw [← pow_mul]
      rw [show 2 * k + 1 = 1 + 2 * k by omega, pow_add]
      simp
    rw [show c * q * (q ^ 2) ^ k = c * (q * (q ^ 2) ^ k) by ring, hqpow]]

/-- The even `ℕ`-indexed product component is multipliable for `‖q‖ < 1`.
@isnad1 id=multipli.1h1v.s5.a868d25340e0 from=translated src=- shape=16505d70 vocab=91b42c27
-/
theorem multipliable_jacobiProductEvenFactor (q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => jacobiProductEvenFactor q n := by
  have h := multipliable_one_add_of_summable (summable_norm_jacobiProduct_first_tail q hq)
  simpa [jacobiProductEvenFactor, sub_eq_add_neg] using h

/-- No even product factor vanishes when `‖q‖ < 1`.
@isnad1 id=ne.1h2v.s4.feccc7740ba0 from=translated src=- shape=4d629d87 vocab=a4be0017
-/
theorem jacobiProductEvenFactor_ne_zero (q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    jacobiProductEvenFactor q n ≠ 0 := by
  intro hzero
  have hqpow_lt : ‖q ^ (2 * (n + 1))‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have h_eq : q ^ (2 * (n + 1)) = 1 := by
    have hzero' : 1 - q ^ (2 * (n + 1)) = 0 := by
      simpa [jacobiProductEvenFactor] using hzero
    linear_combination -hzero'
  rw [h_eq, norm_one] at hqpow_lt
  norm_num at hqpow_lt

/-- The finite even-factor product is the q-Pochhammer `(q²; q²)_N`.
@isnad1 id=eq.0h2v.s5.ea771cc979d9 from=translated src=- shape=09055528 vocab=7a4a5ad5
-/
theorem qPochhammer_qsq_eq_jacobiProductEvenPartial (q : ℂ) (N : ℕ) :
    qPochhammer (q ^ 2) N =
      ∏ n ∈ Finset.range N, jacobiProductEvenFactor q n := by
  induction N with
  | zero =>
      simp [jacobiProductEvenFactor]
  | succ N ih =>
      rw [qPochhammer_succ, Finset.prod_range_succ, ← ih]
      congr 1
      simp [jacobiProductEvenFactor]
      rw [pow_mul]

/-- The finite q-Pochhammer `(q²; q²)_N` tends to the even-factor product.
@isnad1 id=tendsto.1h1v.s6.a10732401dc4 from=translated src=- shape=803550d4 vocab=e8e0b052
-/
theorem tendsto_qPoch_qsq (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => qPoch (q ^ 2) (q ^ 2) N) atTop
      (𝓝 (∏' n : ℕ, jacobiProductEvenFactor q n)) := by
  have h := (multipliable_jacobiProductEvenFactor q hq).tendsto_prod_tprod_nat
  simpa [qPochhammer_qsq_eq_jacobiProductEvenPartial] using h

/-- The even-factor infinite product is nonzero for `‖q‖ < 1`.
@isnad1 id=ne.1h1v.s5.1fdd6e9a1efb from=translated src=- shape=4af82f89 vocab=b087935c
-/
theorem tprod_jacobiProductEvenFactor_ne_zero (q : ℂ) (hq : ‖q‖ < 1) :
    (∏' n : ℕ, jacobiProductEvenFactor q n) ≠ 0 := by
  refine tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -q ^ (2 * (n + 1))) ?_ ?_
  · intro n
    simpa [jacobiProductEvenFactor, sub_eq_add_neg] using
      jacobiProductEvenFactor_ne_zero q hq n
  · simpa using summable_norm_jacobiProduct_first_tail q hq

/-- Each odd `ℕ`-indexed product component is multipliable for `‖q‖ < 1`.
@isnad1 id=multipli.1h2v.s5.10f4a75d0b58 from=translated src=- shape=b3a194db vocab=4a003d0a
-/
theorem multipliable_jacobiProductOddFactor (q c : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => jacobiProductOddFactor q c n := by
  have h := multipliable_one_add_of_summable (summable_norm_jacobiProduct_odd_tail q c hq)
  simpa [jacobiProductOddFactor] using h

/-- The full Nat-indexed product factor is multipliable for `‖q‖ < 1`.
@isnad1 id=multipli.1h2v.s5.52acd20342a3 from=translated src=- shape=b3a194db vocab=0347aa6d
-/
theorem multipliable_jacobiProductNatFactor (q z : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => jacobiProductNatFactor q z n := by
  have h0 := multipliable_jacobiProductEvenFactor q hq
  have h1 := multipliable_jacobiProductOddFactor q z hq
  have h2 := multipliable_jacobiProductOddFactor q z⁻¹ hq
  exact ((h0.mul h1).mul h2).congr fun n => by
    simp [jacobiProductNatFactor, mul_assoc]

/-- The Nat-indexed product factors have product `jacobiInfiniteProduct`.
@isnad1 id=hasprod.1h2v.s5.17e0e5a1aced from=translated src=- shape=9053a6db vocab=3942791c
-/
theorem hasProd_jacobiProductNatFactor (q z : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => jacobiProductNatFactor q z n) (jacobiInfiniteProduct q z) := by
  have h := (multipliable_jacobiProductNatFactor q z hq).hasProd
  rw [jacobiInfiniteProduct_eq_tprod_natFactor q z]
  exact h

/-- The zero-based finite products converge to the infinite product side.
@isnad1 id=tendsto.1h2v.s5.906e490c292d from=translated src=- shape=06ca52cc vocab=b9e8a820
-/
theorem tendsto_jacobiProductPartial (q z : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => jacobiProductPartial q z N) atTop
      (𝓝 (jacobiInfiniteProduct q z)) := by
  have h := (hasProd_jacobiProductNatFactor q z hq).tendsto_prod_nat
  simpa [jacobiProductPartial] using h

/-- The series-side definition is the sum of a genuinely summable family.
@isnad1 id=hassum.1h2v.s6.b9ed3d947377 from=translated src=- shape=465ac76d vocab=c1012038
-/
theorem hasSum_jacobiInfiniteSeries_terms (q z : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℤ => z ^ n * q ^ (n ^ 2)) (jacobiInfiniteSeries q z) :=
  (summable_jacobiInfiniteSeries_terms q z hq).hasSum

/-- The symmetric finite partial sums converge to the bilateral series side.
@isnad1 id=tendsto.1h2v.s5.5210cde52bdf from=translated src=- shape=06ca52cc vocab=69db5966
-/
theorem tendsto_jacobiSeriesSymmetricPartial (q z : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => jacobiSeriesSymmetricPartial q z N) atTop
      (𝓝 (jacobiInfiniteSeries q z)) := by
  have hsum := hasSum_jacobiInfiniteSeries_terms q z hq
  have hsym : HasSum (fun n : ℤ => z ^ n * q ^ (n ^ 2)) (jacobiInfiniteSeries q z)
      (SummationFilter.symmetricIcc ℤ) := by
    exact hsum.mono_left (SummationFilter.symmetricIcc ℤ).le_atTop
  simpa [jacobiSeriesSymmetricPartial] using
    (SummationFilter.hasSum_symmetricIcc_iff.mp hsym)

/-- The nonzero symmetric term pairs converge to the bilateral series with the zero term removed.
@isnad1 id=tendsto.1h2v.s5.15189cbd49d3 from=translated src=- shape=96b782ec vocab=9f9605e9
-/
theorem tendsto_jacobiSeriesSymmetricPairPartial (q z : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => jacobiSeriesSymmetricPairPartial q z N) atTop
      (𝓝 (jacobiInfiniteSeries q z - 1)) := by
  have h : Tendsto (fun N : ℕ => jacobiSeriesSymmetricPartial q z N - (1 : ℂ)) atTop
      (𝓝 (jacobiInfiniteSeries q z - 1)) :=
    (tendsto_jacobiSeriesSymmetricPartial q z hq).sub tendsto_const_nhds
  have hcongr : (fun N : ℕ => jacobiSeriesSymmetricPartial q z N - 1) =
      fun N : ℕ => jacobiSeriesSymmetricPairPartial q z N := by
    funext N
    rw [jacobiSeriesSymmetricPartial_eq_one_add_pairPartial]
    ring
  simpa [hcongr] using h

/-- The negative-index half of the symmetric nonzero pair terms is summable for `‖q‖ < 1`.
@isnad1 id=summable.1h2v.s6.b71d8cb6f803 from=translated src=- shape=1a0a8d3d vocab=7aec973f
-/
theorem summable_jacobiSeriesSymmetricPairTerm_neg (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ =>
      z ^ (-(((n + 1 : ℕ) : ℤ))) * q ^ ((-(((n + 1 : ℕ) : ℤ))) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr (summable_jacobiSeries_nat q z⁻¹ hq)
  refine h.congr fun n => ?_
  rw [← zpow_natCast (z⁻¹) (n + 1), inv_zpow']
  rw [show ((n + 1) * (n + 1)) = (n + 1) ^ 2 by ring]
  rw [← zpow_natCast q ((n + 1) ^ 2)]
  rw [show ((-(((n + 1 : ℕ) : ℤ))) ^ 2) = (((n + 1) ^ 2 : ℕ) : ℤ) by
    norm_num [sq, Int.natCast_mul]
    ring]

/-- The positive-index half of the symmetric nonzero pair terms is summable for `‖q‖ < 1`.
@isnad1 id=summable.1h2v.s6.fabc25ef84fb from=translated src=- shape=96faa459 vocab=52e409df
-/
theorem summable_jacobiSeriesSymmetricPairTerm_pos (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ =>
      z ^ (((n + 1 : ℕ) : ℤ)) * q ^ ((((n + 1 : ℕ) : ℤ)) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr (summable_jacobiSeries_nat q z hq)
  refine h.congr fun n => ?_
  rw [← zpow_natCast z (n + 1)]
  rw [show ((n + 1) * (n + 1)) = (n + 1) ^ 2 by ring]
  rw [← zpow_natCast q ((n + 1) ^ 2)]
  rw [show ((((n + 1 : ℕ) : ℤ)) ^ 2) = (((n + 1) ^ 2 : ℕ) : ℤ) by
    norm_num [sq, Int.natCast_mul]]

/-- The sequence of symmetric nonzero Jacobi series pairs is summable for `‖q‖ < 1`.
@isnad1 id=summable.1h2v.s5.be0f43e302dc from=translated src=- shape=b3a194db vocab=b98c7109
-/
theorem summable_jacobiSeriesSymmetricPairTerm (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => jacobiSeriesSymmetricPairTerm q z n := by
  have hneg := summable_jacobiSeriesSymmetricPairTerm_neg q z hq
  have hpos := summable_jacobiSeriesSymmetricPairTerm_pos q z hq
  simpa [jacobiSeriesSymmetricPairTerm] using hneg.add hpos

/-- The norm majorant of the symmetric pair terms is summable for `‖q‖ < 1`.
@isnad1 id=summable.1h2v.s5.f36acee5112f from=translated src=- shape=6861bfd4 vocab=0b4ecf23
-/
theorem summable_jacobiSeriesSymmetricPairNormMajorant (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => jacobiSeriesSymmetricPairNormMajorant q z n := by
  have hneg := (summable_jacobiSeriesSymmetricPairTerm_neg q z hq).norm
  have hpos := (summable_jacobiSeriesSymmetricPairTerm_pos q z hq).norm
  simpa [jacobiSeriesSymmetricPairNormMajorant] using hneg.add hpos

/-- The infinite sum of symmetric nonzero pairs is the bilateral series with the zero term removed.
@isnad1 id=hassum.1h2v.s5.4dfd10d520d3 from=translated src=- shape=7e9e6eae vocab=3e4ca0dd
-/
theorem hasSum_jacobiSeriesSymmetricPairTerm (q z : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => jacobiSeriesSymmetricPairTerm q z n)
      (jacobiInfiniteSeries q z - 1) := by
  have hsumm := summable_jacobiSeriesSymmetricPairTerm q z hq
  exact (hsumm.hasSum_iff_tendsto_nat).mpr (by
    simpa [jacobiSeriesSymmetricPairPartial] using
      tendsto_jacobiSeriesSymmetricPairPartial q z hq)

/--
The symmetric pair tail beginning at pair index `M` is exactly the bilateral
series tail outside the symmetric partial `[-M, M]`.
@isnad1 id=hassum.1h3v.s6.778b51120059 from=translated src=- shape=ee5699f9 vocab=b6b626d6
-/
theorem hasSum_jacobiSeriesSymmetricPairTerm_tail (q z : ℂ) (hq : ‖q‖ < 1) (M : ℕ) :
    HasSum (fun n : ℕ => jacobiSeriesSymmetricPairTerm q z (n + M))
      (jacobiInfiniteSeries q z - jacobiSeriesSymmetricPartial q z M) := by
  have hfull := hasSum_jacobiSeriesSymmetricPairTerm q z hq
  have htail :
      HasSum (fun n : ℕ => jacobiSeriesSymmetricPairTerm q z (n + M))
        ((jacobiInfiniteSeries q z - 1) -
          ∑ n ∈ Finset.range M, jacobiSeriesSymmetricPairTerm q z n) :=
    (hasSum_nat_add_iff' M).mpr hfull
  convert htail using 1
  rw [jacobiSeriesSymmetricPartial_eq_one_add_pairPartial]
  simp [jacobiSeriesSymmetricPairPartial]
  ring

/-- Tsum form of the symmetric pair tail outside `[-M, M]`.
@isnad1 id=eq.1h3v.s6.36dfea63b8a1 from=translated src=- shape=4e8676ab vocab=976f0057
-/
theorem tsum_jacobiSeriesSymmetricPairTerm_tail (q z : ℂ) (hq : ‖q‖ < 1) (M : ℕ) :
    (∑' n : ℕ, jacobiSeriesSymmetricPairTerm q z (n + M)) =
      jacobiInfiniteSeries q z - jacobiSeriesSymmetricPartial q z M :=
  (hasSum_jacobiSeriesSymmetricPairTerm_tail q z hq M).tsum_eq

/-- The difference between the product side and series side of JTP.-/
noncomputable def jacobiDifference (q z : ℂ) : ℂ :=
  jacobiInfiniteProduct q z - jacobiInfiniteSeries q z

private theorem jacobiInfiniteProduct_zero_factor (z : ℂ) (n : ℕ+) :
    (1 - (0 : ℂ) ^ (2 * n.val)) *
      (1 + z * (0 : ℂ) ^ (2 * n.val - 1)) *
      (1 + z⁻¹ * (0 : ℂ) ^ (2 * n.val - 1)) = 1 := by
  have hnpos : 0 < n.val := n.property
  have heven : 2 * n.val ≠ 0 := by omega
  have hodd : 2 * n.val - 1 ≠ 0 := by omega
  simp [heven, hodd]

/-- At `q = 0`, the product side of Jacobi's triple product is identically `1`.
@isnad1 id=eq.0h1v.s4.cf7761d10be1 from=translated src=- shape=fe2c2146 vocab=094fd298
-/
theorem jacobiInfiniteProduct_zero (z : ℂ) : jacobiInfiniteProduct 0 z = 1 := by
  rw [jacobiInfiniteProduct]
  rw [show (fun n : ℕ+ => (1 - (0 : ℂ) ^ (2 * n.val)) *
      (1 + z * (0 : ℂ) ^ (2 * n.val - 1)) *
      (1 + z⁻¹ * (0 : ℂ) ^ (2 * n.val - 1))) = (fun _ : ℕ+ => (1 : ℂ)) by
    funext n
    exact jacobiInfiniteProduct_zero_factor z n]
  exact tprod_one

/-- At `q = 0`, the bilateral series side of Jacobi's triple product is `1`.
@isnad1 id=eq.0h1v.s4.a40f97312b9f from=translated src=- shape=fe2c2146 vocab=34159227
-/
theorem jacobiInfiniteSeries_zero (z : ℂ) : jacobiInfiniteSeries 0 z = 1 := by
  rw [jacobiInfiniteSeries]
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro n hn
    have hs : n ^ 2 ≠ 0 := pow_ne_zero 2 hn
    rw [zero_zpow (n ^ 2) hs]
    simp

/-- The Jacobi triple product identity is closed in the degenerate case `q = 0`.
@isnad1 id=eq.0h1v.s4.a103f37b01be from=translated src=- shape=77071b92 vocab=73240c87
-/
theorem jacobiTripleProduct_q_zero (z : ℂ) :
    jacobiInfiniteProduct 0 z = jacobiInfiniteSeries 0 z := by
  rw [jacobiInfiniteProduct_zero, jacobiInfiniteSeries_zero]

end InfiniteForms

end Ch02
end PartI
end QseriesFormalization
