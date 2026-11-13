import Tengoku.Seed.Topology.Algebra.InfiniteSum.NatInt
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Chapter04

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Formal power-series shells for the mod-5 JTP pentagonal specialisations

This pending file isolates the formal objects for Hirschhorn's two
mod-5 Jacobi-triple-product specialisations.  The full analytic-to-formal
coefficient bridge is not asserted here; all declarations below are fully
proved.
-/

namespace QseriesFormalization
namespace Pending
namespace JTPFormalPSPentagonal

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

/-! ## Formal AP products -/

/-- The formal factor `1 - X^(r + m n)`.-/
noncomputable def apFactorPS (R : Type*) [CommRing R] (r m n : ℕ) : R⟦X⟧ :=
  (1 : R⟦X⟧) - PowerSeries.X ^ (r + m * n)

/--
@isnad1 id=eq.0h4v.s6.b42bdd96f890 from=translated src=- shape=d2d5151e vocab=021e45be
-/
@[simp] theorem apFactorPS_def (R : Type*) [CommRing R] (r m n : ℕ) :
    apFactorPS R r m n = (1 : R⟦X⟧) - PowerSeries.X ^ (r + m * n) := rfl

/-- The formal AP product `(q^r;q^m)_∞ = ∏_{n≥0} (1 - X^(r+mn))`.-/
noncomputable def qPochAPPS (R : Type*) [CommRing R] [TopologicalSpace R]
    (r m : ℕ) : R⟦X⟧ :=
  ∏' n : ℕ, apFactorPS R r m n

/-- The AP product is multipliable when the step is positive.
@isnad1 id=multipli.1h3v.s5.175152c945b3 from=translated src=- shape=8008d52d vocab=94d5e224
-/
theorem multipliable_apFactorPS (R : Type*) [CommRing R] [TopologicalSpace R]
    (r m : ℕ) (hm : 0 < m) :
    Multipliable fun n : ℕ => apFactorPS R r m n := by
  nontriviality R
  simp_rw [apFactorPS, sub_eq_add_neg]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun k =>
    Filter.eventually_atTop.mpr ⟨k + 1, ?_⟩
  intro n hn
  rw [PowerSeries.order_neg, PowerSeries.order_X_pow]
  norm_cast
  have hm1 : 1 ≤ m := Nat.succ_le_iff.mpr hm
  calc
    k < n := by omega
    _ ≤ m * n := Nat.le_mul_of_pos_left n hm1
    _ ≤ r + m * n := Nat.le_add_left _ _

/-- HasProd form of `qPochAPPS`.
@isnad1 id=hasprod.1h3v.s5.be768beeffd2 from=translated src=- shape=33f0ca45 vocab=89397029
-/
theorem hasProd_qPochAPPS (R : Type*) [CommRing R] [TopologicalSpace R]
    (r m : ℕ) (hm : 0 < m) :
    HasProd (fun n : ℕ => apFactorPS R r m n) (qPochAPPS R r m) :=
  (multipliable_apFactorPS R r m hm).hasProd

/-- `(q,q^4,q^5;q^5)_∞` as a formal power series.-/
noncomputable def pentagonalProduct014PS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 1 5 * qPochAPPS R 4 5 * qPochAPPS R 5 5

/-- `(q^2,q^3,q^5;q^5)_∞` as a formal power series.-/
noncomputable def pentagonalProduct023PS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 2 5 * qPochAPPS R 3 5 * qPochAPPS R 5 5

/-- The per-`n` triple factor for `(q,q^4,q^5;q^5)_∞`.-/
noncomputable def pentagonalTripleFactor014PS (R : Type*) [CommRing R] (n : ℕ) : R⟦X⟧ :=
  apFactorPS R 1 5 n * apFactorPS R 4 5 n * apFactorPS R 5 5 n

/-- The per-`n` triple factor for `(q^2,q^3,q^5;q^5)_∞`.-/
noncomputable def pentagonalTripleFactor023PS (R : Type*) [CommRing R] (n : ℕ) : R⟦X⟧ :=
  apFactorPS R 2 5 n * apFactorPS R 3 5 n * apFactorPS R 5 5 n

/-- HasProd form of the first mod-5 triple product.
@isnad1 id=hasprod.0h1v.s5.b7477ab2bf96 from=translated src=- shape=3a3ee85b vocab=8f8f840a
-/
theorem hasProd_pentagonalTripleFactor014PS
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    HasProd (fun n : ℕ => pentagonalTripleFactor014PS R n)
      (pentagonalProduct014PS R) := by
  unfold pentagonalProduct014PS pentagonalTripleFactor014PS
  exact ((hasProd_qPochAPPS R 1 5 (by norm_num)).mul
    (hasProd_qPochAPPS R 4 5 (by norm_num))).mul
    (hasProd_qPochAPPS R 5 5 (by norm_num))

/-- HasProd form of the second mod-5 triple product.
@isnad1 id=hasprod.0h1v.s5.ff5fb13c2051 from=translated src=- shape=3a3ee85b vocab=062d8507
-/
theorem hasProd_pentagonalTripleFactor023PS
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    HasProd (fun n : ℕ => pentagonalTripleFactor023PS R n)
      (pentagonalProduct023PS R) := by
  unfold pentagonalProduct023PS pentagonalTripleFactor023PS
  exact ((hasProd_qPochAPPS R 2 5 (by norm_num)).mul
    (hasProd_qPochAPPS R 3 5 (by norm_num))).mul
    (hasProd_qPochAPPS R 5 5 (by norm_num))

/-- Tprod form of the first mod-5 triple product.
@isnad1 id=eq.0h1v.s5.97233515b83f from=translated src=- shape=b4dc0957 vocab=70cb8435
-/
theorem pentagonalProduct014PS_eq_tprod
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    pentagonalProduct014PS R = ∏' n : ℕ, pentagonalTripleFactor014PS R n :=
  (hasProd_pentagonalTripleFactor014PS R).tprod_eq.symm

/-- Tprod form of the second mod-5 triple product.
@isnad1 id=eq.0h1v.s5.06890a278dd9 from=translated src=- shape=b4dc0957 vocab=1b7a1242
-/
theorem pentagonalProduct023PS_eq_tprod
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    pentagonalProduct023PS R = ∏' n : ℕ, pentagonalTripleFactor023PS R n :=
  (hasProd_pentagonalTripleFactor023PS R).tprod_eq.symm

/-! ## Formal bilateral series coefficients -/

/-- The integer exponent `(5k² - 3k)/2`, coerced to `Nat`.-/
def pentagonal014Exp (k : ℤ) : ℕ :=
  (k * (5 * k - 3) / 2).toNat

/-- The integer exponent `(5k² - k)/2`, coerced to `Nat`.-/
def pentagonal023Exp (k : ℤ) : ℕ :=
  (k * (5 * k - 1) / 2).toNat

/-- The sign `(-1)^k`, represented over an arbitrary commutative ring.-/
def negOnePowInt (R : Type*) [CommRing R] (k : ℤ) : R :=
  (-1 : R) ^ k.natAbs

/-- Coefficient of `X^n` in the first bilateral pentagonal AP series.-/
noncomputable def pentagonal014Coeff (R : Type*) [CommRing R] (n : ℕ) : R :=
  ∑ k ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ),
    if pentagonal014Exp k = n then negOnePowInt R k else 0

/-- Coefficient of `X^n` in the second bilateral pentagonal AP series.-/
noncomputable def pentagonal023Coeff (R : Type*) [CommRing R] (n : ℕ) : R :=
  ∑ k ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ),
    if pentagonal023Exp k = n then negOnePowInt R k else 0

/-- Formal series `∑_{k∈ℤ} (-1)^k X^((5k²-3k)/2)`.-/
noncomputable def pentagonal014SeriesPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk (pentagonal014Coeff R)

/-- Formal series `∑_{k∈ℤ} (-1)^k X^((5k²-k)/2)`.-/
noncomputable def pentagonal023SeriesPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk (pentagonal023Coeff R)

/--
@isnad1 id=eq.0h2v.s7.cfb0c6d61627 from=translated src=- shape=0b039adb vocab=a71cfef9
-/
@[simp] theorem coeff_pentagonal014SeriesPS
    (R : Type*) [CommRing R] (n : ℕ) :
    (pentagonal014SeriesPS R).coeff n = pentagonal014Coeff R n := by
  unfold pentagonal014SeriesPS
  rw [PowerSeries.coeff_mk]

/--
@isnad1 id=eq.0h2v.s7.e666751ad08f from=translated src=- shape=0b039adb vocab=cb2c1a0e
-/
@[simp] theorem coeff_pentagonal023SeriesPS
    (R : Type*) [CommRing R] (n : ℕ) :
    (pentagonal023SeriesPS R).coeff n = pentagonal023Coeff R n := by
  unfold pentagonal023SeriesPS
  rw [PowerSeries.coeff_mk]

/-! ## Bilateral theta analytic-to-formal bridge -/

/--
@isnad1 id=le.0h1v.s5.7e4e6605ee88 from=translated src=- shape=81d07cb0 vocab=cf232d13
-/
lemma pentagonal014Exp_nonneg_int (k : ℤ) :
    0 ≤ k * (5 * k - 3) / 2 := by
  have hnum : 0 ≤ k * (5 * k - 3) := by
    by_cases hk : 0 ≤ k
    · by_cases hk0 : k = 0
      · simp [hk0]
      · have hkpos : 1 ≤ k := by omega
        have hfac : 0 ≤ 5 * k - 3 := by nlinarith
        exact mul_nonneg hk hfac
    · have hk_nonpos : k ≤ 0 := by omega
      have hfac : 5 * k - 3 ≤ 0 := by nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos hk_nonpos hfac
  exact Int.ediv_nonneg hnum (by norm_num)

/--
@isnad1 id=le.0h1v.s5.6b3e61732d1a from=translated src=- shape=81d07cb0 vocab=cf232d13
-/
lemma pentagonal023Exp_nonneg_int (k : ℤ) :
    0 ≤ k * (5 * k - 1) / 2 := by
  have hnum : 0 ≤ k * (5 * k - 1) := by
    by_cases hk : 0 ≤ k
    · by_cases hk0 : k = 0
      · simp [hk0]
      · have hkpos : 1 ≤ k := by omega
        have hfac : 0 ≤ 5 * k - 1 := by nlinarith
        exact mul_nonneg hk hfac
    · have hk_nonpos : k ≤ 0 := by omega
      have hfac : 5 * k - 1 ≤ 0 := by nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos hk_nonpos hfac
  exact Int.ediv_nonneg hnum (by norm_num)

/--
@isnad1 id=eq.0h1v.s5.b50ea09c6895 from=translated src=- shape=d128f69b vocab=f78def84
-/
lemma int_coe_pentagonal014Exp (k : ℤ) :
    (pentagonal014Exp k : ℤ) = k * (5 * k - 3) / 2 := by
  unfold pentagonal014Exp
  exact Int.toNat_of_nonneg (pentagonal014Exp_nonneg_int k)

/--
@isnad1 id=eq.0h1v.s5.799b97ead51e from=translated src=- shape=d128f69b vocab=4c5d5b45
-/
lemma int_coe_pentagonal023Exp (k : ℤ) :
    (pentagonal023Exp k : ℤ) = k * (5 * k - 1) / 2 := by
  unfold pentagonal023Exp
  exact Int.toNat_of_nonneg (pentagonal023Exp_nonneg_int k)

/--
@isnad1 id=le.1h1v.s5.213f062cb170 from=translated src=- shape=b14928e1 vocab=cf232d13
-/
lemma pentagonal014Exp_bound_pos (k : ℤ) (hk : 0 ≤ k) :
    k ≤ k * (5 * k - 3) / 2 := by
  rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)]
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hkpos : 1 ≤ k := by omega
    nlinarith

/--
@isnad1 id=le.1h1v.s6.24e908f3feb6 from=translated src=- shape=c6ac9fd9 vocab=c68a68f0
-/
lemma pentagonal014Exp_bound_neg (k : ℤ) (hk : k ≤ 0) :
    -k ≤ k * (5 * k - 3) / 2 := by
  rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)]
  nlinarith

/--
@isnad1 id=le.1h1v.s5.cee95be60b9f from=translated src=- shape=b14928e1 vocab=cf232d13
-/
lemma pentagonal023Exp_bound_pos (k : ℤ) (hk : 0 ≤ k) :
    k ≤ k * (5 * k - 1) / 2 := by
  rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)]
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hkpos : 1 ≤ k := by omega
    nlinarith

/--
@isnad1 id=le.1h1v.s6.4d7e7ae7de53 from=translated src=- shape=c6ac9fd9 vocab=c68a68f0
-/
lemma pentagonal023Exp_bound_neg (k : ℤ) (hk : k ≤ 0) :
    -k ≤ k * (5 * k - 1) / 2 := by
  rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)]
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hkneg : k ≤ -1 := by omega
    nlinarith

noncomputable def pentagonal014ThetaTerm (q : ℂ) (k : ℤ) : ℂ :=
  negOnePowInt ℂ k * q ^ pentagonal014Exp k

noncomputable def pentagonal023ThetaTerm (q : ℂ) (k : ℤ) : ℂ :=
  negOnePowInt ℂ k * q ^ pentagonal023Exp k

noncomputable def pentagonal014ThetaNat (q : ℂ) : ℂ :=
  ∑' k : ℤ, pentagonal014ThetaTerm q k

noncomputable def pentagonal023ThetaNat (q : ℂ) : ℂ :=
  ∑' k : ℤ, pentagonal023ThetaTerm q k

noncomputable def pentagonal014Analytic (q : ℂ) : ℂ :=
  ∑' k : ℤ, (-1 : ℂ) ^ k * q ^ (k * (5 * k - 3) / 2)

noncomputable def pentagonal023Analytic (q : ℂ) : ℂ :=
  ∑' k : ℤ, (-1 : ℂ) ^ k * q ^ (k * (5 * k - 1) / 2)

noncomputable def pentagonal014SeriesFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (pentagonal014Coeff ℂ)

noncomputable def pentagonal023SeriesFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (pentagonal023Coeff ℂ)

/-! ## Analytic identities already closed in Chapter 4, in target exponent orientation -/

/-! ## Product-side analytic functions, with the puncture at `q = 0` filled -/

/-- The analytic product `(q,q^4,q^5;q^5)_∞`.-/
noncomputable def pentagonal014ProductAnalytic (q : ℂ) : ℂ :=
  (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 5 n) *
    (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 4 n) *
    (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 1 n)

/-- The analytic product `(q^2,q^3,q^5;q^5)_∞`.-/
noncomputable def pentagonal023ProductAnalytic (q : ℂ) : ℂ :=
  (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 5 n) *
    (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 3 n) *
    (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 2 n)

/--
@isnad1 id=lt.1h1v.s4.0cdaffe50f68 from=translated src=- shape=c87724ab vocab=d9c78bcd
-/
lemma pentagonal014Exp_pos_of_ne_zero {k : ℤ} (hk : k ≠ 0) :
    0 < pentagonal014Exp k := by
  by_cases hk_nonneg : 0 ≤ k
  · have hk_one : (1 : ℤ) ≤ k := by omega
    have hle_int : (1 : ℤ) ≤ (pentagonal014Exp k : ℤ) := by
      rw [int_coe_pentagonal014Exp]
      exact le_trans hk_one (pentagonal014Exp_bound_pos k hk_nonneg)
    have hle_nat : 1 ≤ pentagonal014Exp k := by exact_mod_cast hle_int
    omega
  · have hk_nonpos : k ≤ 0 := by omega
    have hk_one : (1 : ℤ) ≤ -k := by omega
    have hle_int : (1 : ℤ) ≤ (pentagonal014Exp k : ℤ) := by
      rw [int_coe_pentagonal014Exp]
      exact le_trans hk_one (pentagonal014Exp_bound_neg k hk_nonpos)
    have hle_nat : 1 ≤ pentagonal014Exp k := by exact_mod_cast hle_int
    omega

/--
@isnad1 id=lt.1h1v.s4.352f8e5f877f from=translated src=- shape=c87724ab vocab=1f3e556d
-/
lemma pentagonal023Exp_pos_of_ne_zero {k : ℤ} (hk : k ≠ 0) :
    0 < pentagonal023Exp k := by
  by_cases hk_nonneg : 0 ≤ k
  · have hk_one : (1 : ℤ) ≤ k := by omega
    have hle_int : (1 : ℤ) ≤ (pentagonal023Exp k : ℤ) := by
      rw [int_coe_pentagonal023Exp]
      exact le_trans hk_one (pentagonal023Exp_bound_pos k hk_nonneg)
    have hle_nat : 1 ≤ pentagonal023Exp k := by exact_mod_cast hle_int
    omega
  · have hk_nonpos : k ≤ 0 := by omega
    have hk_one : (1 : ℤ) ≤ -k := by omega
    have hle_int : (1 : ℤ) ≤ (pentagonal023Exp k : ℤ) := by
      rw [int_coe_pentagonal023Exp]
      exact le_trans hk_one (pentagonal023Exp_bound_neg k hk_nonpos)
    have hle_nat : 1 ≤ pentagonal023Exp k := by exact_mod_cast hle_int
    omega

/-! ## Final uniqueness step, conditional on the product-coefficient Taylor bridge -/

noncomputable def pentagonal014ProductCoeffFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (pentagonalProduct014PS ℂ).coeff n)

noncomputable def pentagonal023ProductCoeffFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (pentagonalProduct023PS ℂ).coeff n)

/-! ### Product-coefficient finite partial bridges -/

/--
@isnad1 id=eq.1h6v.s8.1d7a04883373 from=translated src=- shape=1eaa2abd vocab=3ca5dc1c
-/
lemma coeff_mul_apFactorPS_eq_of_lt
    (R : Type*) [CommRing R] (P : R⟦X⟧) (k r m N : ℕ)
    (hk : k < r + m * N) :
    (P * apFactorPS R r m N).coeff k = P.coeff k := by
  rw [apFactorPS, mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow']
  simp [Nat.not_le_of_gt hk]

/--
@isnad1 id=eq.1h3v.s8.9b224fc8e608 from=translated src=- shape=df1fdf2e vocab=57aa158b
-/
theorem partial_prod_pentagonalTripleFactor014PS_coeff_stable
    (R : Type*) [CommRing R] (k N : ℕ) (hN : k ≤ N) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range (N + 1), pentagonalTripleFactor014PS R n) =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n) := by
  rw [Finset.prod_range_succ]
  change PowerSeries.coeff k
      ((∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n) *
        (apFactorPS R 1 5 N * apFactorPS R 4 5 N * apFactorPS R 5 5 N)) =
    PowerSeries.coeff k (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n)
  let P : R⟦X⟧ := ∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n
  calc
    PowerSeries.coeff k
        (P * (apFactorPS R 1 5 N * apFactorPS R 4 5 N * apFactorPS R 5 5 N))
        = PowerSeries.coeff k
          (((P * apFactorPS R 1 5 N) * apFactorPS R 4 5 N) *
            apFactorPS R 5 5 N) := by
          ring_nf
    _ = PowerSeries.coeff k ((P * apFactorPS R 1 5 N) * apFactorPS R 4 5 N) :=
          coeff_mul_apFactorPS_eq_of_lt R
            ((P * apFactorPS R 1 5 N) * apFactorPS R 4 5 N) k 5 5 N (by omega)
    _ = PowerSeries.coeff k (P * apFactorPS R 1 5 N) :=
          coeff_mul_apFactorPS_eq_of_lt R (P * apFactorPS R 1 5 N) k 4 5 N
            (by omega)
    _ = PowerSeries.coeff k P :=
          coeff_mul_apFactorPS_eq_of_lt R P k 1 5 N (by omega)

/--
@isnad1 id=eq.1h3v.s8.bae9f6ed615b from=translated src=- shape=df1fdf2e vocab=61de5827
-/
theorem partial_prod_pentagonalTripleFactor023PS_coeff_stable
    (R : Type*) [CommRing R] (k N : ℕ) (hN : k ≤ N) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range (N + 1), pentagonalTripleFactor023PS R n) =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n) := by
  rw [Finset.prod_range_succ]
  change PowerSeries.coeff k
      ((∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n) *
        (apFactorPS R 2 5 N * apFactorPS R 3 5 N * apFactorPS R 5 5 N)) =
    PowerSeries.coeff k (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n)
  let P : R⟦X⟧ := ∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n
  calc
    PowerSeries.coeff k
        (P * (apFactorPS R 2 5 N * apFactorPS R 3 5 N * apFactorPS R 5 5 N))
        = PowerSeries.coeff k
          (((P * apFactorPS R 2 5 N) * apFactorPS R 3 5 N) *
            apFactorPS R 5 5 N) := by
          ring_nf
    _ = PowerSeries.coeff k ((P * apFactorPS R 2 5 N) * apFactorPS R 3 5 N) :=
          coeff_mul_apFactorPS_eq_of_lt R
            ((P * apFactorPS R 2 5 N) * apFactorPS R 3 5 N) k 5 5 N (by omega)
    _ = PowerSeries.coeff k (P * apFactorPS R 2 5 N) :=
          coeff_mul_apFactorPS_eq_of_lt R (P * apFactorPS R 2 5 N) k 3 5 N
            (by omega)
    _ = PowerSeries.coeff k P :=
          coeff_mul_apFactorPS_eq_of_lt R P k 2 5 N (by omega)

/--
@isnad1 id=eq.2h4v.s8.28b729679c06 from=translated src=- shape=6f1d1426 vocab=49078ff1
-/
theorem partial_prod_pentagonalTripleFactor014PS_coeff_eq
    (R : Type*) [CommRing R] (k N M : ℕ) (hkN : k ≤ N) (hNM : N ≤ M) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range M, pentagonalTripleFactor014PS R n) =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n) := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M _ ih =>
      rw [partial_prod_pentagonalTripleFactor014PS_coeff_stable R k M (by omega), ih]

/--
@isnad1 id=eq.2h4v.s8.7ac24fc01d2b from=translated src=- shape=6f1d1426 vocab=3bf6143e
-/
theorem partial_prod_pentagonalTripleFactor023PS_coeff_eq
    (R : Type*) [CommRing R] (k N M : ℕ) (hkN : k ≤ N) (hNM : N ≤ M) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range M, pentagonalTripleFactor023PS R n) =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n) := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M _ ih =>
      rw [partial_prod_pentagonalTripleFactor023PS_coeff_stable R k M (by omega), ih]

/--
@isnad1 id=eq.0h2v.s8.5631c1b82374 from=translated src=- shape=9fe041cf vocab=1d4c8780
-/
theorem coeff_pentagonalProduct014PS_eq_coeff_partial
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (k : ℕ) :
    (pentagonalProduct014PS R).coeff k =
      (∏ n ∈ Finset.range (k + 1), pentagonalTripleFactor014PS R n).coeff k := by
  have h_tendsto : Tendsto
      (fun N : ℕ => ∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n) atTop
      (𝓝 (pentagonalProduct014PS R)) :=
    (hasProd_pentagonalTripleFactor014PS R).tendsto_prod_nat
  have h_coeff_tendsto : Tendsto
      (fun N : ℕ => PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n)) atTop
      (𝓝 (PowerSeries.coeff k (pentagonalProduct014PS R))) :=
    ((PowerSeries.WithPiTopology.continuous_coeff R k).tendsto _).comp h_tendsto
  have h_const_tendsto : Tendsto
      (fun N : ℕ => PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n)) atTop
      (𝓝 (PowerSeries.coeff k
        (∏ n ∈ Finset.range (k + 1), pentagonalTripleFactor014PS R n))) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨k + 1, fun N hN =>
      (partial_prod_pentagonalTripleFactor014PS_coeff_eq R k (k + 1) N (by omega) hN).symm⟩
  exact tendsto_nhds_unique h_coeff_tendsto h_const_tendsto

/--
@isnad1 id=eq.0h2v.s8.cd73947f7894 from=translated src=- shape=9fe041cf vocab=8952faeb
-/
theorem coeff_pentagonalProduct023PS_eq_coeff_partial
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (k : ℕ) :
    (pentagonalProduct023PS R).coeff k =
      (∏ n ∈ Finset.range (k + 1), pentagonalTripleFactor023PS R n).coeff k := by
  have h_tendsto : Tendsto
      (fun N : ℕ => ∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n) atTop
      (𝓝 (pentagonalProduct023PS R)) :=
    (hasProd_pentagonalTripleFactor023PS R).tendsto_prod_nat
  have h_coeff_tendsto : Tendsto
      (fun N : ℕ => PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n)) atTop
      (𝓝 (PowerSeries.coeff k (pentagonalProduct023PS R))) :=
    ((PowerSeries.WithPiTopology.continuous_coeff R k).tendsto _).comp h_tendsto
  have h_const_tendsto : Tendsto
      (fun N : ℕ => PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n)) atTop
      (𝓝 (PowerSeries.coeff k
        (∏ n ∈ Finset.range (k + 1), pentagonalTripleFactor023PS R n))) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨k + 1, fun N hN =>
      (partial_prod_pentagonalTripleFactor023PS_coeff_eq R k (k + 1) N (by omega) hN).symm⟩
  exact tendsto_nhds_unique h_coeff_tendsto h_const_tendsto

/--
@isnad1 id=le.2h6v.s7.0ccf94e6f149 from=translated src=- shape=33256cef vocab=0f9f0d41
-/
lemma norm_coeff_mul_apFactorPS_complex_le
    (P : ℂ⟦X⟧) (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ k : ℕ, ‖P.coeff k‖ ≤ B) (k r m N : ℕ) :
    ‖(P * apFactorPS ℂ r m N).coeff k‖ ≤ 2 * B := by
  rw [apFactorPS, mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow']
  by_cases hle : r + m * N ≤ k
  · rw [ite_eq_left hle]
    calc
      ‖P.coeff k - P.coeff (k - (r + m * N))‖
          ≤ ‖P.coeff k‖ + ‖P.coeff (k - (r + m * N))‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hP k) (hP (k - (r + m * N)))
      _ = 2 * B := by ring
  · rw [ite_eq_right hle, sub_zero]
    linarith [hP k]

/--
@isnad1 id=le.2h4v.s7.35d047ad0393 from=translated src=- shape=2f263e74 vocab=51a59f8b
-/
lemma norm_coeff_mul_pentagonalTripleFactor014PS_complex_le
    (P : ℂ⟦X⟧) (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ k : ℕ, ‖P.coeff k‖ ≤ B) (k N : ℕ) :
    ‖(P * pentagonalTripleFactor014PS ℂ N).coeff k‖ ≤ 8 * B := by
  have hP1 : ∀ k : ℕ, ‖(P * apFactorPS ℂ 1 5 N).coeff k‖ ≤ 2 * B :=
    fun k => norm_coeff_mul_apFactorPS_complex_le P B hB hP k 1 5 N
  have hP2 : ∀ k : ℕ,
      ‖((P * apFactorPS ℂ 1 5 N) * apFactorPS ℂ 4 5 N).coeff k‖ ≤
        2 * (2 * B) :=
    fun k => norm_coeff_mul_apFactorPS_complex_le
      (P * apFactorPS ℂ 1 5 N) (2 * B) (by nlinarith) hP1 k 4 5 N
  calc
    ‖(P * pentagonalTripleFactor014PS ℂ N).coeff k‖ =
        ‖(((P * apFactorPS ℂ 1 5 N) * apFactorPS ℂ 4 5 N) *
          apFactorPS ℂ 5 5 N).coeff k‖ := by
        congr 1
        rw [pentagonalTripleFactor014PS]
        ring_nf
    _ ≤ 2 * (2 * (2 * B)) :=
        norm_coeff_mul_apFactorPS_complex_le
          ((P * apFactorPS ℂ 1 5 N) * apFactorPS ℂ 4 5 N)
          (2 * (2 * B)) (by nlinarith) hP2 k 5 5 N
    _ = 8 * B := by ring

/--
@isnad1 id=le.2h4v.s7.223e06874126 from=translated src=- shape=2f263e74 vocab=eee85d25
-/
lemma norm_coeff_mul_pentagonalTripleFactor023PS_complex_le
    (P : ℂ⟦X⟧) (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ k : ℕ, ‖P.coeff k‖ ≤ B) (k N : ℕ) :
    ‖(P * pentagonalTripleFactor023PS ℂ N).coeff k‖ ≤ 8 * B := by
  have hP1 : ∀ k : ℕ, ‖(P * apFactorPS ℂ 2 5 N).coeff k‖ ≤ 2 * B :=
    fun k => norm_coeff_mul_apFactorPS_complex_le P B hB hP k 2 5 N
  have hP2 : ∀ k : ℕ,
      ‖((P * apFactorPS ℂ 2 5 N) * apFactorPS ℂ 3 5 N).coeff k‖ ≤
        2 * (2 * B) :=
    fun k => norm_coeff_mul_apFactorPS_complex_le
      (P * apFactorPS ℂ 2 5 N) (2 * B) (by nlinarith) hP1 k 3 5 N
  calc
    ‖(P * pentagonalTripleFactor023PS ℂ N).coeff k‖ =
        ‖(((P * apFactorPS ℂ 2 5 N) * apFactorPS ℂ 3 5 N) *
          apFactorPS ℂ 5 5 N).coeff k‖ := by
        congr 1
        rw [pentagonalTripleFactor023PS]
        ring_nf
    _ ≤ 2 * (2 * (2 * B)) :=
        norm_coeff_mul_apFactorPS_complex_le
          ((P * apFactorPS ℂ 2 5 N) * apFactorPS ℂ 3 5 N)
          (2 * (2 * B)) (by nlinarith) hP2 k 5 5 N
    _ = 8 * B := by ring

end JTPFormalPSPentagonal
end Pending
end QseriesFormalization
