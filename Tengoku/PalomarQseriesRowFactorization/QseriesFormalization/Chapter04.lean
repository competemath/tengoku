import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Basic
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Chapter02
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Chapter03

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Chapter 4 — Part I: Some applications of Jacobi's triple product

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 4, pp. 21–30.)

This chapter spins off four named identities from the Jacobi triple
product (Theorem 4.1, Euler's pentagonal theorem, Theorem 4.3, the
quintuple product identity).  The Jacobi triple product is now available;
the remaining infinite applications need the specialization and rewriting
layers connecting those products and bilateral sums to Chan's displayed forms.
-/

namespace QseriesFormalization
namespace PartI
namespace Ch04

open QseriesFormalization.PartI.Ch02 (jacobiInfiniteProduct jacobiInfiniteSeries jacobiTripleProduct)
open QseriesFormalization.PartI.Ch03 (finiteJTPRHS finite_jacobi_triple_product)
open Filter

open scoped Topology

section Field

variable {R : Type*} [Field R]

/-- Finite Euler product `(q; q)_n` (alias of `qPochhammer`).-/
def eulerProductTrunc (q : R) (n : Nat) : R :=
  qPochhammer q n

/--
@isnad1 id=eq.0h3v.s6.22f5f99f17d9 from=translated src=- shape=e6b43771 vocab=739f19f0
-/
@[simp] theorem eulerProductTrunc_succ (q : R) (n : Nat) :
    eulerProductTrunc q (Nat.succ n) =
      eulerProductTrunc q n * (1 - q ^ (Nat.succ n)) := by
  rfl

/-- Theorem 4.1: left side.-/
noncomputable def theorem41LHS (q : ℂ) (a : Nat) : ℂ :=
  jacobiInfiniteProduct (q ^ 2) (-(q ^ a))

/-- Exponent `5n - 2 - 2a` from the first product in Chan Theorem 4.1.-/
def theorem41SecondExponent (a n : Nat) : Nat :=
  Int.toNat (5 * (n : Int) - 2 - 2 * (a : Int))

/-- Exponent `5n - 3 + 2a` from the first product in Chan Theorem 4.1.-/
def theorem41ThirdExponent (a n : Nat) : Nat :=
  Int.toNat (5 * (n : Int) - 3 + 2 * (a : Int))

/-- Exponent `j(5j+1)/2 - 2aj` from the bilateral sum in Chan Theorem 4.1.-/
def theorem41Index (a : Nat) (j : Int) : Nat :=
  Int.toNat ((j * (5 * j + 1)) / 2 - 2 * (a : Int) * j)

/--
Theorem 4.1 LHS truncated:
`∏_{n=1}^{N} (1 - q^{5n})(1 - q^{5n-2-2a})(1 - q^{5n-3+2a})`.-/
noncomputable def theorem41LHSTrunc (q : R) (a : Nat) : Nat → R
  | 0 => 1
  | Nat.succ n =>
      theorem41LHSTrunc q a n *
        (1 - q ^ (5 * Nat.succ n)) *
        (1 - q ^ theorem41SecondExponent a (Nat.succ n)) *
        (1 - q ^ theorem41ThirdExponent a (Nat.succ n))

/-- Theorem 4.1 RHS truncated: `∑_{j=-N}^{N} (-1)^j q^{j(5j+1)/2 - 2aj}`.-/
noncomputable def theorem41RHSTrunc (q : R) (a N : Nat) : R :=
  bilateralSum (fun j : Int => (-1 : R) ^ j.toNat * q ^ theorem41Index a j) N

/- The infinite Theorem 4.1 equality is now reduced to specializing JTP and
rewriting the resulting product and bilateral series into Chan's displayed form. -/

/-- Euler's pentagonal theorem (Theorem 4.2): product side.-/
noncomputable def eulerPentagonalProduct (q : ℂ) : ℂ :=
  jacobiInfiniteProduct q (-1)

/-- Nat-indexed product factor for the `z = -1` JTP specialization.-/
noncomputable def eulerPentagonalJacobiProductFactor (q : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (2 * (n + 1))) *
    (1 - q ^ (2 * (n + 1) - 1)) *
    (1 - q ^ (2 * (n + 1) - 1))

/-- The Jacobi-series side obtained from the `z = -1` specialization.-/
noncomputable def eulerPentagonalJacobiSeries (q : ℂ) : ℂ :=
  jacobiInfiniteSeries q (-1)

/-- The `z = -1` Jacobi triple product specialization used in Chapter 4.
@isnad1 id=eq.1h1v.s4.d51bc95c781a from=translated src=- shape=1e000bbb vocab=41e5e8d8
-/
theorem eulerPentagonalProduct_eq_jacobiSeries (q : ℂ) (hq : ‖q‖ < 1) :
    eulerPentagonalProduct q = eulerPentagonalJacobiSeries q := by
  exact jacobiTripleProduct q (-1) hq (by norm_num)

/--
The three residue-class product factor obtained in Euler's pentagonal theorem
from the JTP substitution `Q^2 = q^3`, `z = -Q/q^2`.-/
noncomputable def eulerPentagonalCubicProductFactor (q : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (3 * (n + 1))) *
    (1 - q ^ (3 * (n + 1) - 2)) *
    (1 - q ^ (3 * (n + 1) - 1))

private lemma int_two_dvd_mul_succ (l : Int) : (2 : Int) ∣ l * (l + 1) := by
  rcases Int.even_or_odd l with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (l + 1), by rw [hm]; ring⟩
  · exact ⟨l * (m + 1), by rw [hm]; ring⟩

/-! ## Mod-5 residue factors for Rogers-Ramanujan (Ch7 dependency)

The classical R-R proof needs:
`(q;q)_∞ = ∏_{k=1..5} (q^k;q^5)_∞`.

Each factor `(q^k;q^5)_∞` = `∏'_n (1 - q^(k + 5n))` for `n ≥ 0`. -/

/-- `(q^k; q^5)_∞` truncated factor: `1 - q^k · q^(5n) = 1 - q^(k + 5n)`.-/
def rrMod5Factor (q : ℂ) (k : ℕ) (n : ℕ) : ℂ :=
  1 - q ^ (k + 5 * n)

/--
@isnad1 id=eq.0h3v.s5.b83b3f92a554 from=translated src=- shape=3cc1bba9 vocab=201ec7b4
-/
@[simp] theorem rrMod5Factor_def (q : ℂ) (k n : ℕ) :
    rrMod5Factor q k n = 1 - q ^ (k + 5 * n) := rfl

/-- For ‖q‖ < 1 and k ≥ 1: `Summable fun n => ‖-q^k · (q^5)^n‖`.-/
private theorem summable_norm_rrMod5_tail (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    Summable fun n : ℕ => ‖-q ^ k * (q ^ 5) ^ n‖ := by
  have hq5 : ‖q ^ 5‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  exact Ch02.summable_norm_mul_geometric_complex (-(q ^ k)) (q ^ 5) hq5

/-- The k-th mod-5 residue factor family is multipliable for ‖q‖ < 1.
@isnad1 id=multipli.1h2v.s5.fbd27b39f890 from=translated src=- shape=b51d030d vocab=cb1c78db
-/
theorem multipliable_rrMod5Factor (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    Multipliable fun n : ℕ => rrMod5Factor q k n := by
  have h := multipliable_one_add_of_summable (summable_norm_rrMod5_tail q hq k)
  refine h.congr fun n => ?_
  simp only [rrMod5Factor]
  rw [show q ^ (k + 5 * n) = q ^ k * (q ^ 5) ^ n by
    rw [pow_add, pow_mul]]
  ring

/-- Each rrMod5Factor is nonzero for `‖q‖ < 1` and `k ≥ 1`.
@isnad1 id=ne.2h3v.s5.8458301276a6 from=translated src=- shape=bd8a2856 vocab=ac92cf45
-/
theorem rrMod5Factor_ne_zero (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    rrMod5Factor q k n ≠ 0 := by
  intro hzero
  have h_eq : q ^ (k + 5 * n) = 1 := by
    have : 1 - q ^ (k + 5 * n) = 0 := by simpa [rrMod5Factor] using hzero
    linear_combination -this
  have h_norm_one : ‖q ^ (k + 5 * n)‖ = 1 := by rw [h_eq, norm_one]
  rw [norm_pow] at h_norm_one
  have hq_nn : 0 ≤ ‖q‖ := norm_nonneg _
  have hexp_pos : 0 < k + 5 * n := by omega
  have h_lt : ‖q‖ ^ (k + 5 * n) < 1 :=
    pow_lt_one₀ hq_nn hq hexp_pos.ne'
  linarith

/-! ### Rogers-Ramanujan theta series via JTP at q^5

S₁(q) := ∑'_{j : ℤ} (-1)^j · q^(j(5j+1)/2) — JTP series at Q := Y^5, z := -Y (Y² = q).
S₂(q) := ∑'_{j : ℤ} (-1)^j · q^(j(5j+3)/2) — JTP series at Q := Y^5, z := -Y^3 (Y² = q).
-/

/-- The infinite product of the k-th mod-5 residue factor is nonzero for `‖q‖ < 1`, `k ≥ 1`.
@isnad1 id=ne.2h2v.s5.176f13c680d3 from=translated src=- shape=ebc8e80c vocab=44717e89
-/
theorem tprod_rrMod5Factor_ne_zero (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) (hk : 1 ≤ k) :
    (∏' n : ℕ, rrMod5Factor q k n) ≠ 0 := by
  have h_eq_form : (∏' n : ℕ, rrMod5Factor q k n) =
      ∏' n : ℕ, (1 + -(q ^ k * (q ^ 5) ^ n)) := by
    refine tprod_congr fun n => ?_
    simp only [rrMod5Factor]
    rw [show q ^ (k + 5 * n) = q ^ k * (q ^ 5) ^ n by rw [pow_add, pow_mul]]
    ring
  rw [h_eq_form]
  refine tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -(q ^ k * (q ^ 5) ^ n)) ?_ ?_
  · intro n
    have h_ne := rrMod5Factor_ne_zero q hq k hk n
    have h_eq : (1 + -(q ^ k * (q ^ 5) ^ n) : ℂ) = rrMod5Factor q k n := by
      simp only [rrMod5Factor]
      rw [show q ^ (k + 5 * n) = q ^ k * (q ^ 5) ^ n by rw [pow_add, pow_mul]]
      ring
    rw [h_eq]
    exact h_ne
  · have h := summable_norm_rrMod5_tail q hq k
    refine h.congr fun n => ?_
    simp [norm_neg, norm_mul]

/-- Finite identity: `(q;q)_{5N} = ∏_{n<N} (1-q^(5n+1))(1-q^(5n+2))(1-q^(5n+3))(1-q^(5n+4))(1-q^(5n+5))`.-/
private theorem mod5_product_partial_eq (q : ℂ) (N : ℕ) :
    qPochhammer q (5 * N) =
      ∏ n ∈ Finset.range N,
        ((1 - q ^ (5 * n + 1)) * (1 - q ^ (5 * n + 2)) *
         (1 - q ^ (5 * n + 3)) * (1 - q ^ (5 * n + 4)) *
         (1 - q ^ (5 * n + 5))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, ← ih]
    have h5 : 5 * (N + 1) = 5 * N + 5 := by ring
    rw [h5]
    -- Decompose qPochhammer q (5*N + 5) = qPochhammer q (5*N) * 5 factors.
    have h_unfold :
        qPochhammer q (5 * N + 5) =
          qPochhammer q (5 * N) *
          (1 - q ^ (5 * N + 1)) * (1 - q ^ (5 * N + 2)) *
          (1 - q ^ (5 * N + 3)) * (1 - q ^ (5 * N + 4)) *
          (1 - q ^ (5 * N + 5)) := by
      have e1 : 5 * N + 1 = (5 * N) + 1 := rfl
      have e2 : 5 * N + 2 = ((5 * N) + 1) + 1 := by omega
      have e3 : 5 * N + 3 = (((5 * N) + 1) + 1) + 1 := by omega
      have e4 : 5 * N + 4 = ((((5 * N) + 1) + 1) + 1) + 1 := by omega
      have e5 : 5 * N + 5 = (((((5 * N) + 1) + 1) + 1) + 1) + 1 := by omega
      rw [e5, qPochhammer_succ, ← e4]
      rw [show (5 * N + 4 : ℕ) = ((5 * N + 3) + 1 : ℕ) from by omega, qPochhammer_succ]
      rw [show (5 * N + 3 : ℕ) = ((5 * N + 2) + 1 : ℕ) from by omega, qPochhammer_succ]
      rw [show (5 * N + 2 : ℕ) = ((5 * N + 1) + 1 : ℕ) from by omega, qPochhammer_succ]
      rw [show (5 * N + 1 : ℕ) = ((5 * N) + 1 : ℕ) from rfl, qPochhammer_succ]
    rw [h_unfold]
    ring

/-- Nat-indexed Euler product factor `1 - q^(n+1)`.-/
def eulerPentagonalProductFactor (q : ℂ) (n : ℕ) : ℂ :=
  1 - q ^ (n + 1)

/-- Euler's infinite product side, Nat-indexed from exponent `1`.-/
noncomputable def eulerPentagonalInfiniteProduct (q : ℂ) : ℂ :=
  ∏' n : ℕ, eulerPentagonalProductFactor q n

private theorem summable_norm_eulerPentagonalProduct_tail (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-q ^ (n + 1)‖ := by
  have h := Ch02.summable_norm_mul_geometric_complex (-q) q hq
  refine h.congr fun n => ?_
  congr 1
  rw [show -q * q ^ n = -q ^ (n + 1) by
    rw [pow_succ']
    ring]

/-- The Nat-indexed Euler product is multipliable for `‖q‖ < 1`.
@isnad1 id=multipli.1h1v.s5.aa3c51105a2a from=translated src=- shape=16505d70 vocab=d99b1674
-/
theorem multipliable_eulerPentagonalProductFactor (q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => eulerPentagonalProductFactor q n := by
  have h := multipliable_one_add_of_summable (summable_norm_eulerPentagonalProduct_tail q hq)
  simpa [eulerPentagonalProductFactor, sub_eq_add_neg] using h

/-- Finite partial products of the Nat-indexed Euler product are q-Pochhammer symbols.
@isnad1 id=eq.0h2v.s4.3c7b98f6b4cb from=translated src=- shape=42b0b6bd vocab=6fb5130f
-/
theorem eulerPentagonalProductFactor_partial_eq_qPochhammer (q : ℂ) (N : ℕ) :
    (∏ n ∈ Finset.range N, eulerPentagonalProductFactor q n) = qPochhammer q N := by
  induction N with
  | zero =>
      simp [eulerPentagonalProductFactor]
  | succ N ih =>
      rw [Finset.prod_range_succ, ih, qPochhammer_succ]
      simp [eulerPentagonalProductFactor]

/-- The finite q-Pochhammer products tend to Euler's infinite product.
@isnad1 id=tendsto.1h1v.s5.01509fa0dc60 from=translated src=- shape=fd26aeda vocab=6459c455
-/
theorem tendsto_eulerPentagonalProductTrunc (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => qPochhammer q N) atTop
      (𝓝 (eulerPentagonalInfiniteProduct q)) := by
  have h := (multipliable_eulerPentagonalProductFactor q hq).tendsto_prod_tprod_nat
  simpa [eulerPentagonalInfiniteProduct,
    eulerPentagonalProductFactor_partial_eq_qPochhammer] using h

/-- The partial qPochhammer at `5N` converges to `(q;q)_∞`.
@isnad1 id=tendsto.1h1v.s5.8b20757d2040 from=translated src=- shape=08db7156 vocab=9e2ad7b4
-/
theorem tendsto_qPochhammer_5N (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => qPochhammer q (5 * N)) atTop
      (𝓝 (eulerPentagonalInfiniteProduct q)) := by
  have h_main := tendsto_eulerPentagonalProductTrunc q hq
  have h_5N : Tendsto (fun N : ℕ => 5 * N) atTop atTop := by
    refine tendsto_atTop_mono (fun N => ?_) tendsto_id
    show N ≤ 5 * N
    omega
  exact h_main.comp h_5N

/-- Euler's infinite product equals the mod-5 regrouped product.
@isnad1 id=eq.1h1v.s7.e52800872881 from=translated src=- shape=44374e7b vocab=82508549
-/
theorem eulerPentagonalInfiniteProduct_eq_mod5_regroup (q : ℂ) (hq : ‖q‖ < 1) :
    eulerPentagonalInfiniteProduct q =
      (∏' n : ℕ, rrMod5Factor q 1 n) * (∏' n : ℕ, rrMod5Factor q 2 n) *
      (∏' n : ℕ, rrMod5Factor q 3 n) * (∏' n : ℕ, rrMod5Factor q 4 n) *
      (∏' n : ℕ, rrMod5Factor q 5 n) := by
  have hLHS_tendsto := tendsto_qPochhammer_5N q hq
  have hRHS_tendsto :
      Tendsto (fun N : ℕ =>
        (∏ n ∈ Finset.range N, rrMod5Factor q 1 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 2 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 3 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 4 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 5 n))
        atTop
        (𝓝 ((∏' n, rrMod5Factor q 1 n) * (∏' n, rrMod5Factor q 2 n) *
            (∏' n, rrMod5Factor q 3 n) * (∏' n, rrMod5Factor q 4 n) *
            (∏' n, rrMod5Factor q 5 n))) :=
    (((((multipliable_rrMod5Factor q hq 1).tendsto_prod_tprod_nat.mul
        (multipliable_rrMod5Factor q hq 2).tendsto_prod_tprod_nat).mul
        (multipliable_rrMod5Factor q hq 3).tendsto_prod_tprod_nat).mul
        (multipliable_rrMod5Factor q hq 4).tendsto_prod_tprod_nat).mul
        (multipliable_rrMod5Factor q hq 5).tendsto_prod_tprod_nat)
  -- Bridge the two Tendsto's: the partial qPochhammer equals the 5-separate prods.
  have h_partial_eq : ∀ N : ℕ,
      qPochhammer q (5 * N) =
        (∏ n ∈ Finset.range N, rrMod5Factor q 1 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 2 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 3 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 4 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 5 n) := by
    intro N
    rw [mod5_product_partial_eq q N]
    -- Now goal: ∏ n, (5-factor product) = ∏ ... rrMod5 1 · ∏ ... rrMod5 2 · ... · ∏ ... rrMod5 5
    have h_factor_eq : ∀ n : ℕ,
        (1 - q ^ (5 * n + 1)) * (1 - q ^ (5 * n + 2)) *
        (1 - q ^ (5 * n + 3)) * (1 - q ^ (5 * n + 4)) *
        (1 - q ^ (5 * n + 5)) =
        rrMod5Factor q 1 n * rrMod5Factor q 2 n *
        rrMod5Factor q 3 n * rrMod5Factor q 4 n *
        rrMod5Factor q 5 n := by
      intro n
      simp only [rrMod5Factor]
      ring
    rw [Finset.prod_congr rfl (fun n _ => h_factor_eq n)]
    simp only [Finset.prod_mul_distrib]
  have hRHS_alt :
      Tendsto (fun N : ℕ => qPochhammer q (5 * N)) atTop
        (𝓝 ((∏' n, rrMod5Factor q 1 n) * (∏' n, rrMod5Factor q 2 n) *
            (∏' n, rrMod5Factor q 3 n) * (∏' n, rrMod5Factor q 4 n) *
            (∏' n, rrMod5Factor q 5 n))) := by
    refine hRHS_tendsto.congr' ?_
    refine Filter.Eventually.of_forall fun N => ?_
    exact (h_partial_eq N).symm
  exact tendsto_nhds_unique hLHS_tendsto hRHS_alt

/-- `(q;q)_∞ ≠ 0` for `‖q‖ < 1` (via the mod-5 regrouping, each factor nonzero).
@isnad1 id=ne.1h1v.s4.9a20f1f536fc from=translated src=- shape=ccb3be71 vocab=74850de2
-/
theorem eulerPentagonalInfiniteProduct_ne_zero (q : ℂ) (hq : ‖q‖ < 1) :
    eulerPentagonalInfiniteProduct q ≠ 0 := by
  rw [eulerPentagonalInfiniteProduct_eq_mod5_regroup q hq]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
  · exact tprod_rrMod5Factor_ne_zero q hq 1 (by norm_num)
  · exact tprod_rrMod5Factor_ne_zero q hq 2 (by norm_num)
  · exact tprod_rrMod5Factor_ne_zero q hq 3 (by norm_num)
  · exact tprod_rrMod5Factor_ne_zero q hq 4 (by norm_num)
  · exact tprod_rrMod5Factor_ne_zero q hq 5 (by norm_num)

/-- Truncated product side `∏_{n=1}^{N} (1 - q^n)` (Chan Theorem 4.2 LHS).-/
def eulerPentagonalProductTrunc (q : R) (N : Nat) : R :=
  qPochhammer q N

/-- Pentagonal-number index `j ↦ j(3j+1)/2` (Int → Nat for use as exponent).-/
def pentagonalIndex (j : Int) : Nat :=
  Int.toNat (j * (3 * j + 1) / 2)

/-- Truncated bilateral sum `∑_{j=-N}^{N} (-1)^j q^{j(3j+1)/2}` (Chan Theorem 4.2 RHS).-/
noncomputable def eulerPentagonalSeriesTrunc (q : R) (N : Nat) : R :=
  bilateralSum (fun j : Int => (-1 : R) ^ j.toNat * q ^ pentagonalIndex j) N

/-- The first nontrivial Euler product truncation is `1 - q`.
@isnad1 id=eq.0h2v.s5.5244a620fa0f from=translated src=- shape=003ae1f3 vocab=a1cc9b04
-/
theorem eulerPentagonalProductTrunc_one (q : R) :
    eulerPentagonalProductTrunc q 1 = 1 - q := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

/- The infinite Euler pentagonal theorem is proved above as
`eulerPentagonalInfiniteProduct_eq_tsum`. -/

/-- Theorem 4.3 LHS truncated: `(q; q)_N^3`.-/
noncomputable def theorem43LHSTrunc (q : R) (N : Nat) : R :=
  eulerPentagonalProductTrunc q N ^ 3

/-- Theorem 4.3 RHS truncated: `∑_{n=0}^{N} (-1)^n (2n+1) q^{n(n+1)/2}`.-/
noncomputable def theorem43RHSTrunc (q : R) (N : Nat) : R :=
  natSum (fun n : Nat => (-1 : R) ^ n * (2 * n + 1 : R) * q ^ triangular n) N

/- The infinite Theorem 4.3 identity is deferred until its JTP specialization
and rewriting layer is formalized. -/

/-- Integer powers, interpreted in the ambient field.-/
noncomputable def intPow (x : R) (k : Int) : R :=
  if 0 ≤ k then x ^ k.toNat else (Inv.inv x) ^ (-k).toNat

/-- Exponent `3n^2 + n` in the Eq. (2.12) form of the quintuple product identity.-/
def quintupleQuadraticIndex (n : Int) : Nat :=
  Int.toNat (3 * n * n + n)

/--
Quintuple product LHS truncated in Chan's Eq. (2.12) form, with factors
for `n = 0, ..., N - 1`.-/
noncomputable def quintupleProductLHSTrunc (q z : R) : Nat → R
  | 0 => 1
  | Nat.succ n =>
      quintupleProductLHSTrunc q z n *
        (1 - q ^ (2 * n + 2)) *
        (1 - z * q ^ (2 * n + 1)) *
        (1 - (Inv.inv z) * q ^ (2 * n + 1)) *
        (1 - z ^ 2 * q ^ (4 * n)) *
        (1 - (Inv.inv z) ^ 2 * q ^ (4 * n + 4))

/-- Nat-indexed quintuple product factor in Chan's Eq. (2.12) form.-/
noncomputable def quintupleProductFactor (q z : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (2 * n + 2)) *
    (1 - z * q ^ (2 * n + 1)) *
    (1 - z⁻¹ * q ^ (2 * n + 1)) *
    (1 - z ^ 2 * q ^ (4 * n)) *
    (1 - z⁻¹ ^ 2 * q ^ (4 * n + 4))

/-- Infinite product side of the quintuple product identity.-/
noncomputable def quintupleProductLHS (q z : ℂ) : ℂ :=
  ∏' n : ℕ, quintupleProductFactor q z n

/-- Finite products of the Nat-indexed quintuple factors match the recursive truncation.
@isnad1 id=eq.0h3v.s4.70db91b60678 from=translated src=- shape=f0558f03 vocab=919a6300
-/
theorem quintupleProductFactor_partial_eq_trunc (q z : ℂ) (N : ℕ) :
    (∏ n ∈ Finset.range N, quintupleProductFactor q z n) =
      quintupleProductLHSTrunc q z N := by
  induction N with
  | zero =>
      simp [quintupleProductFactor, quintupleProductLHSTrunc]
  | succ N ih =>
      rw [Finset.prod_range_succ, ih]
      simp [quintupleProductFactor, quintupleProductLHSTrunc]
      ring

private theorem summable_norm_quintupleProduct_tail0 (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-q ^ (2 * n + 2)‖ := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(q ^ 2)) (q ^ 2) hq2
  refine h.congr fun n => ?_
  congr 1
  rw [show -(q ^ 2) * (q ^ 2) ^ n = -q ^ (2 * n + 2) by
    rw [← pow_mul]
    rw [show 2 * n + 2 = 2 + 2 * n by omega]
    rw [pow_add]
    ring]

private theorem summable_norm_quintupleProduct_tail1 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z * q ^ (2 * n + 1))‖ := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(z * q)) (q ^ 2) hq2
  refine h.congr fun n => ?_
  congr 1
  rw [show -(z * q) * (q ^ 2) ^ n = -(z * q ^ (2 * n + 1)) by
    rw [← pow_mul]
    rw [show 2 * n + 1 = 1 + 2 * n by omega]
    rw [pow_add]
    ring]

private theorem summable_norm_quintupleProduct_tail2 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z⁻¹ * q ^ (2 * n + 1))‖ := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(z⁻¹ * q)) (q ^ 2) hq2
  refine h.congr fun n => ?_
  congr 1
  rw [show -(z⁻¹ * q) * (q ^ 2) ^ n = -(z⁻¹ * q ^ (2 * n + 1)) by
    rw [← pow_mul]
    rw [show 2 * n + 1 = 1 + 2 * n by omega]
    rw [pow_add]
    ring]

private theorem summable_norm_quintupleProduct_tail3 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z ^ 2 * q ^ (4 * n))‖ := by
  have hq4 : ‖q ^ 4‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(z ^ 2)) (q ^ 4) hq4
  refine h.congr fun n => ?_
  congr 1
  rw [show -(z ^ 2) * (q ^ 4) ^ n = -(z ^ 2 * q ^ (4 * n)) by
    rw [← pow_mul]
    ring]

private theorem summable_norm_quintupleProduct_tail4 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z⁻¹ ^ 2 * q ^ (4 * n + 4))‖ := by
  have hq4 : ‖q ^ 4‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(z⁻¹ ^ 2 * q ^ 4)) (q ^ 4) hq4
  refine h.congr fun n => ?_
  congr 1
  rw [show -(z⁻¹ ^ 2 * q ^ 4) * (q ^ 4) ^ n =
      -(z⁻¹ ^ 2 * q ^ (4 * n + 4)) by
    rw [← pow_mul]
    rw [show 4 * n + 4 = 4 + 4 * n by omega]
    rw [pow_add]
    ring]

/-- The quintuple product side is multipliable for `‖q‖ < 1`.
@isnad1 id=multipli.1h2v.s5.1cf0761d2f48 from=translated src=- shape=b3a194db vocab=953ac638
-/
theorem multipliable_quintupleProductFactor (q z : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => quintupleProductFactor q z n := by
  have h0 : Multipliable fun n : ℕ => 1 - q ^ (2 * n + 2) := by
    have h := multipliable_one_add_of_summable (summable_norm_quintupleProduct_tail0 q hq)
    simpa [sub_eq_add_neg] using h
  have h1 : Multipliable fun n : ℕ => 1 - z * q ^ (2 * n + 1) := by
    have h := multipliable_one_add_of_summable (summable_norm_quintupleProduct_tail1 q z hq)
    simpa [sub_eq_add_neg] using h
  have h2 : Multipliable fun n : ℕ => 1 - z⁻¹ * q ^ (2 * n + 1) := by
    have h := multipliable_one_add_of_summable (summable_norm_quintupleProduct_tail2 q z hq)
    simpa [sub_eq_add_neg] using h
  have h3 : Multipliable fun n : ℕ => 1 - z ^ 2 * q ^ (4 * n) := by
    have h := multipliable_one_add_of_summable (summable_norm_quintupleProduct_tail3 q z hq)
    simpa [sub_eq_add_neg] using h
  have h4 : Multipliable fun n : ℕ => 1 - z⁻¹ ^ 2 * q ^ (4 * n + 4) := by
    have h := multipliable_one_add_of_summable (summable_norm_quintupleProduct_tail4 q z hq)
    simpa [sub_eq_add_neg] using h
  exact ((((h0.mul h1).mul h2).mul h3).mul h4).congr fun n => by
    simp [quintupleProductFactor, mul_assoc]

/-- The recursive quintuple product truncations tend to the infinite product side.
@isnad1 id=tendsto.1h2v.s5.f1f39975ce9c from=translated src=- shape=68d7b6b4 vocab=ae25c258
-/
theorem tendsto_quintupleProductLHSTrunc (q z : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => quintupleProductLHSTrunc q z N) atTop
      (𝓝 (quintupleProductLHS q z)) := by
  have h := (multipliable_quintupleProductFactor q z hq).tendsto_prod_tprod_nat
  simpa [quintupleProductLHS, quintupleProductFactor_partial_eq_trunc] using h

/--
Nat-indexed factor for Chan Theorem 4.4, written with zero-based index:
`(1 - q^(n+1))(1 - z q^(n+1))(1 - z⁻¹ q^n)
 (1 - z^2 q^(2n+1))(1 - z⁻¹^2 q^(2n+1))`.-/
noncomputable def theorem44ProductFactor (q z : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (n + 1)) *
    (1 - z * q ^ (n + 1)) *
    (1 - z⁻¹ * q ^ n) *
    (1 - z ^ 2 * q ^ (2 * n + 1)) *
    (1 - z⁻¹ ^ 2 * q ^ (2 * n + 1))

/-- Product side of Chan Theorem 4.4.-/
noncomputable def theorem44ProductLHS (q z : ℂ) : ℂ :=
  ∏' n : ℕ, theorem44ProductFactor q z n

/-- Zero-based finite partial product for Chan Theorem 4.4's product side.-/
noncomputable def theorem44ProductPartial (q z : ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, theorem44ProductFactor q z n

/-- The `z`-exponent appearing when the two Theorem 4.4 Jacobi sums are multiplied.-/
def theorem44DoubleSumZIndex (m n : Int) : Int :=
  2 * n - m

/-- The `(-1)`-exponent appearing when the two Theorem 4.4 Jacobi sums are multiplied.-/
def theorem44DoubleSumSignIndex (m n : Int) : Int :=
  m + n

/--
Six times the `q`-exponent in the product of the two Theorem 4.4 Jacobi
summands. This avoids integer-division bookkeeping in the regrouping layer.-/
def theorem44DoubleSumSixExponent (m n : Int) : Int :=
  3 * m * (m - 1) + 6 * n ^ 2

/-- Six times the coefficient-side `q`-exponent in Chan Eq. (4.21).-/
def theorem44CoeffSixExponent (k l : Int) : Int :=
  k * (k + 1) + 2 * l * (l - 1)

/-- The coefficient-side sixfold exponent is always nonnegative.
@isnad1 id=le.0h2v.s3.65f00345abe4 from=translated src=- shape=a120b2a8 vocab=230ebc79
-/
theorem theorem44CoeffSixExponent_nonneg (k l : Int) :
    0 ≤ theorem44CoeffSixExponent k l := by
  have hk : 0 ≤ k * (k + 1) := by
    by_cases h : 0 ≤ k
    · exact mul_nonneg h (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have hl : 0 ≤ l * (l - 1) := by
    by_cases h : 1 ≤ l
    · exact mul_nonneg (by omega) (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  unfold theorem44CoeffSixExponent
  nlinarith

/-- The coefficient-side sixfold exponent is always even.
@isnad1 id=dvd.0h2v.s3.bf4770ea63e9 from=translated src=- shape=a120b2a8 vocab=42a1a6a5
-/
theorem two_dvd_theorem44CoeffSixExponent (k l : Int) :
    (2 : Int) ∣ theorem44CoeffSixExponent k l := by
  rcases int_two_dvd_mul_succ k with ⟨a, ha⟩
  refine ⟨a + l * (l - 1), ?_⟩
  unfold theorem44CoeffSixExponent
  rw [ha]
  ring

/--
Under Chan's residue condition `3 ∣ l+k`, the coefficient-side sixfold
exponent is divisible by `6`, so it represents an honest integer exponent.
@isnad1 id=dvd.1h2v.s5.9364ac17c543 from=translated src=- shape=210aa0fa vocab=0dd78aa1
-/
theorem six_dvd_theorem44CoeffSixExponent_of_residue
    (k l : Int) (h : (3 : Int) ∣ l + k) :
    (6 : Int) ∣ theorem44CoeffSixExponent k l := by
  rcases h with ⟨a, ha⟩
  have hl : l = 3 * a - k := by omega
  rcases int_two_dvd_mul_succ k with ⟨b, hb⟩
  refine ⟨b + 3 * a ^ 2 - 2 * a * k - a, ?_⟩
  calc
    theorem44CoeffSixExponent k l =
        3 * (k * (k + 1)) + 18 * a ^ 2 - 12 * a * k - 6 * a := by
      unfold theorem44CoeffSixExponent
      rw [hl]
      ring
    _ = 6 * (b + 3 * a ^ 2 - 2 * a * k - a) := by
      rw [hb]
      ring

/-- Actual natural-number `q`-exponent attached to Chan's coefficient term.-/
def theorem44CoeffExponentIndex (k l : Int) : Nat :=
  Int.toNat (theorem44CoeffSixExponent k l / 6)

/-- The natural coefficient exponent recovers the sixfold exponent under the residue condition.
@isnad1 id=eq.1h2v.s5.b457bf1caffc from=translated src=- shape=1644dc79 vocab=2faf7d7c
-/
theorem theorem44CoeffExponentIndex_spec
    (k l : Int) (h : (3 : Int) ∣ l + k) :
    6 * ((theorem44CoeffExponentIndex k l : Nat) : Int) =
      theorem44CoeffSixExponent k l := by
  have hnonneg : 0 ≤ theorem44CoeffSixExponent k l :=
    theorem44CoeffSixExponent_nonneg k l
  have hdiv : (6 : Int) ∣ theorem44CoeffSixExponent k l :=
    six_dvd_theorem44CoeffSixExponent_of_residue k l h
  have hquot_nonneg : 0 ≤ theorem44CoeffSixExponent k l / 6 :=
    Int.ediv_nonneg hnonneg (by norm_num)
  unfold theorem44CoeffExponentIndex
  rw [Int.toNat_of_nonneg hquot_nonneg]
  rw [show 6 * (theorem44CoeffSixExponent k l / 6) =
      (theorem44CoeffSixExponent k l / 6) * 6 by ring]
  exact Int.ediv_mul_cancel hdiv

/-- Substituting `m = 2n - k` makes the product term contribute to `z^k`.
@isnad1 id=eq.0h2v.s4.77a480462fd4 from=translated src=- shape=7c02320f vocab=6ab9998a
-/
theorem theorem44DoubleSumZIndex_reindex (k n : Int) :
    theorem44DoubleSumZIndex (2 * n - k) n = k := by
  unfold theorem44DoubleSumZIndex
  ring

/-- Under `m = 2n-k`, the sign exponent is `l = 3n-k`.
@isnad1 id=eq.0h2v.s5.b65ce6b2bf23 from=translated src=- shape=427d96f7 vocab=44653a75
-/
theorem theorem44DoubleSumSignIndex_reindex (k n : Int) :
    theorem44DoubleSumSignIndex (2 * n - k) n = 3 * n - k := by
  unfold theorem44DoubleSumSignIndex
  ring

/-- The reindexed coefficient variable `l = 3n-k` satisfies Chan's residue constraint.
@isnad1 id=dvd.0h2v.s5.eb92577c2ac1 from=translated src=- shape=902509b7 vocab=ec041f02
-/
theorem theorem44CoeffResidueCondition_reindex (k n : Int) :
    (3 : Int) ∣ (3 * n - k) + k := by
  use n
  ring

/-- Coefficient sixfold exponent in the `k = 3r`, `l = 3j` residue class.
@isnad1 id=eq.0h2v.s7.23366862519a from=translated src=- shape=92497bdf vocab=b17e2e54
-/
theorem theorem44CoeffSixExponent_residue_zero (r j : Int) :
    theorem44CoeffSixExponent (3 * r) (3 * j) =
      3 * r * (3 * r + 1) + 6 * j * (3 * j - 1) := by
  unfold theorem44CoeffSixExponent
  ring

/-- Coefficient sixfold exponent in the `k = -3r-1`, `l = 3j+1` residue class.
@isnad1 id=eq.0h2v.s7.b3eeb8fdc940 from=translated src=- shape=383735d1 vocab=1c1c64c6
-/
theorem theorem44CoeffSixExponent_residue_one (r j : Int) :
    theorem44CoeffSixExponent (-(3 * r) - 1) (3 * j + 1) =
      3 * r * (3 * r + 1) + 6 * j * (3 * j + 1) := by
  unfold theorem44CoeffSixExponent
  ring

/-- Coefficient sixfold exponent in the `k = 3r-2`, `l = 3j+2` residue class.
@isnad1 id=eq.0h2v.s7.74a49090f7c9 from=translated src=- shape=0b270f76 vocab=b17e2e54
-/
theorem theorem44CoeffSixExponent_residue_two (r j : Int) :
    theorem44CoeffSixExponent (3 * r - 2) (3 * j + 2) =
      (3 * r - 2) * (3 * r - 1) + 2 * (3 * j + 2) * (3 * j + 1) := by
  unfold theorem44CoeffSixExponent
  ring

/-- The `k = 3r`, `l = 3j` class satisfies the coefficient residue constraint.
@isnad1 id=dvd.0h2v.s5.e126d6e0ef26 from=translated src=- shape=62d66fee vocab=a56bc09a
-/
theorem theorem44CoeffResidueCondition_zero (r j : Int) :
    (3 : Int) ∣ (3 * j) + (3 * r) := by
  use j + r
  ring

/-- The `k = -3r-1`, `l = 3j+1` class satisfies the coefficient residue constraint.
@isnad1 id=dvd.0h2v.s6.7845489ed68e from=translated src=- shape=bd458c90 vocab=a5585f6b
-/
theorem theorem44CoeffResidueCondition_one (r j : Int) :
    (3 : Int) ∣ (3 * j + 1) + (-(3 * r) - 1) := by
  use j - r
  ring

/-- The `k = 3r-2`, `l = 3j+2` class satisfies the coefficient residue constraint.
@isnad1 id=dvd.0h2v.s6.4bb098ba009d from=translated src=- shape=376f8cba vocab=ec041f02
-/
theorem theorem44CoeffResidueCondition_two (r j : Int) :
    (3 : Int) ∣ (3 * j + 2) + (3 * r - 2) := by
  use j + r
  ring

/-- For `k = 3r`, Chan's residue constraint forces `l = 3j`.
@isnad1 id=iff.0h2v.s5.7909f4f49e2e from=translated src=- shape=bc13ba13 vocab=a56bc09a
-/
theorem theorem44CoeffResidueCondition_zero_iff (r l : Int) :
    ((3 : Int) ∣ l + 3 * r) ↔ ∃ j : Int, l = 3 * j := by
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    refine ⟨a - r, ?_⟩
    omega
  · rintro ⟨j, rfl⟩
    use j + r
    ring

/-- For `k = -3r-1`, Chan's residue constraint forces `l = 3j+1`.
@isnad1 id=iff.0h2v.s6.dfcae8eccfc8 from=translated src=- shape=28fba4e3 vocab=a5585f6b
-/
theorem theorem44CoeffResidueCondition_one_iff (r l : Int) :
    ((3 : Int) ∣ l + (-(3 * r) - 1)) ↔ ∃ j : Int, l = 3 * j + 1 := by
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    refine ⟨a + r, ?_⟩
    omega
  · rintro ⟨j, rfl⟩
    use j - r
    ring

/-- For `k = 3r-2`, Chan's residue constraint forces `l = 3j+2`.
@isnad1 id=iff.0h2v.s6.1553de848248 from=translated src=- shape=996d4566 vocab=ec041f02
-/
theorem theorem44CoeffResidueCondition_two_iff (r l : Int) :
    ((3 : Int) ∣ l + (3 * r - 2)) ↔ ∃ j : Int, l = 3 * j + 2 := by
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    refine ⟨a - r, ?_⟩
    omega
  · rintro ⟨j, rfl⟩
    use j + r
    ring

/-- Natural coefficient exponent in the `k = 3r`, `l = 3j` residue class.
@isnad1 id=eq.0h2v.s7.10e7f75da85b from=translated src=- shape=3b9c2e46 vocab=21a79fd2
-/
theorem theorem44CoeffExponentIndex_residue_zero_spec (r j : Int) :
    6 * ((theorem44CoeffExponentIndex (3 * r) (3 * j) : Nat) : Int) =
      3 * r * (3 * r + 1) + 6 * j * (3 * j - 1) := by
  rw [theorem44CoeffExponentIndex_spec (3 * r) (3 * j)
    (theorem44CoeffResidueCondition_zero r j)]
  exact theorem44CoeffSixExponent_residue_zero r j

/-- Natural coefficient exponent in the `k = -3r-1`, `l = 3j+1` residue class.
@isnad1 id=eq.0h2v.s7.18b1e548f591 from=translated src=- shape=0c69f6ea vocab=3ff2dca1
-/
theorem theorem44CoeffExponentIndex_residue_one_spec (r j : Int) :
    6 * ((theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1) : Nat) : Int) =
      3 * r * (3 * r + 1) + 6 * j * (3 * j + 1) := by
  rw [theorem44CoeffExponentIndex_spec (-(3 * r) - 1) (3 * j + 1)
    (theorem44CoeffResidueCondition_one r j)]
  exact theorem44CoeffSixExponent_residue_one r j

/-- Natural coefficient exponent in the `k = 3r-2`, `l = 3j+2` residue class.
@isnad1 id=eq.0h2v.s7.a3fbd90f5196 from=translated src=- shape=059250db vocab=21a79fd2
-/
theorem theorem44CoeffExponentIndex_residue_two_spec (r j : Int) :
    6 * ((theorem44CoeffExponentIndex (3 * r - 2) (3 * j + 2) : Nat) : Int) =
      (3 * r - 2) * (3 * r - 1) + 2 * (3 * j + 2) * (3 * j + 1) := by
  rw [theorem44CoeffExponentIndex_spec (3 * r - 2) (3 * j + 2)
    (theorem44CoeffResidueCondition_two r j)]
  exact theorem44CoeffSixExponent_residue_two r j

private theorem int_two_dvd_mul_three_add_one (r : Int) :
    (2 : Int) ∣ r * (3 * r + 1) := by
  rcases int_two_dvd_mul_succ r with ⟨a, ha⟩
  refine ⟨a + r ^ 2, ?_⟩
  calc
    r * (3 * r + 1) = r * (r + 1) + 2 * r ^ 2 := by ring
    _ = 2 * a + 2 * r ^ 2 := by rw [show r * (r + 1) = 2 * a by simpa [mul_comm] using ha]
    _ = 2 * (a + r ^ 2) := by ring

/-- The `k = 3r`, `l = 3j` natural exponent in Chan's divided form.
@isnad1 id=eq.0h2v.s6.79e14806676f from=translated src=- shape=34a04ed6 vocab=44303556
-/
theorem theorem44CoeffExponentIndex_residue_zero_eq (r j : Int) :
    ((theorem44CoeffExponentIndex (3 * r) (3 * j) : Nat) : Int) =
      r * (3 * r + 1) / 2 + j * (3 * j - 1) := by
  apply (mul_right_injective₀ (show (6 : Int) ≠ 0 by norm_num))
  have hr : (2 : Int) ∣ r * (3 * r + 1) :=
    int_two_dvd_mul_three_add_one r
  have hhalf : 6 * (r * (3 * r + 1) / 2) = 3 * (r * (3 * r + 1)) := by
    rw [show 6 * (r * (3 * r + 1) / 2) =
        3 * ((r * (3 * r + 1) / 2) * 2) by ring]
    rw [Int.ediv_mul_cancel hr]
  calc
    6 * ((theorem44CoeffExponentIndex (3 * r) (3 * j) : Nat) : Int) =
        3 * r * (3 * r + 1) + 6 * j * (3 * j - 1) :=
          theorem44CoeffExponentIndex_residue_zero_spec r j
    _ = 6 * (r * (3 * r + 1) / 2 + j * (3 * j - 1)) := by
      rw [show 6 * (r * (3 * r + 1) / 2 + j * (3 * j - 1)) =
          6 * (r * (3 * r + 1) / 2) + 6 * (j * (3 * j - 1)) by ring]
      rw [hhalf]
      ring

/-- The `k = -3r-1`, `l = 3j+1` natural exponent in Chan's divided form.
@isnad1 id=eq.0h2v.s7.5f5bd6b7f075 from=translated src=- shape=d6e89583 vocab=c757109f
-/
theorem theorem44CoeffExponentIndex_residue_one_eq (r j : Int) :
    ((theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1) : Nat) : Int) =
      r * (3 * r + 1) / 2 + j * (3 * j + 1) := by
  apply (mul_right_injective₀ (show (6 : Int) ≠ 0 by norm_num))
  have hr : (2 : Int) ∣ r * (3 * r + 1) :=
    int_two_dvd_mul_three_add_one r
  have hhalf : 6 * (r * (3 * r + 1) / 2) = 3 * (r * (3 * r + 1)) := by
    rw [show 6 * (r * (3 * r + 1) / 2) =
        3 * ((r * (3 * r + 1) / 2) * 2) by ring]
    rw [Int.ediv_mul_cancel hr]
  calc
    6 * ((theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1) : Nat) : Int) =
        3 * r * (3 * r + 1) + 6 * j * (3 * j + 1) :=
          theorem44CoeffExponentIndex_residue_one_spec r j
    _ = 6 * (r * (3 * r + 1) / 2 + j * (3 * j + 1)) := by
      rw [show 6 * (r * (3 * r + 1) / 2 + j * (3 * j + 1)) =
          6 * (r * (3 * r + 1) / 2) + 6 * (j * (3 * j + 1)) by ring]
      rw [hhalf]
      ring

/-- Common outer factor in the two nonzero residue branches for fixed `r`.-/
noncomputable def theorem44CoeffPairedBranchOuter (q : ℂ) (r : Int) : ℂ :=
  q ^ Int.toNat (r * (3 * r + 1) / 2)

/-- Inner bracket in the paired nonzero residue branches for fixed `r,j`.-/
noncomputable def theorem44CoeffPairedBranchInner (q z : ℂ) (r j : Int) : ℂ :=
  z ^ (3 * r) * ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))) -
    z ^ (-(3 * r) - 1) * ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1)))

/-- Factorized paired nonzero residue contribution for fixed `r,j`.-/
noncomputable def theorem44CoeffPairedBranchTerm (q z : ℂ) (r j : Int) : ℂ :=
  theorem44CoeffPairedBranchOuter q r * theorem44CoeffPairedBranchInner q z r j

/-- Symmetric finite partial sum of the paired-branch inner terms over `-N ≤ j ≤ N`.-/
noncomputable def theorem44CoeffPairedBranchInnerPartial
    (q z : ℂ) (r : Int) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), theorem44CoeffPairedBranchInner q z r j

/-- Left theta-like finite partial in the paired-branch inner term.-/
noncomputable def theorem44CoeffPairedBranchInnerLeftPartial
    (q z : ℂ) (r : Int) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    z ^ (3 * r) * ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1)))

/-- Right theta-like finite partial in the paired-branch inner term.-/
noncomputable def theorem44CoeffPairedBranchInnerRightPartial
    (q z : ℂ) (r : Int) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    z ^ (-(3 * r) - 1) * ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1)))

/-- Base left theta-like finite partial, before multiplying by the fixed `z`-factor.-/
noncomputable def theorem44CoeffPairedBranchLeftThetaPartial
    (q : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    (-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))

/-- Base right theta-like finite partial, before multiplying by the fixed `z`-factor.-/
noncomputable def theorem44CoeffPairedBranchRightThetaPartial
    (q : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    (-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1))

/-- The base theta term left after the paired nonzero residue branches are combined.-/
noncomputable def theorem44CoeffPairedBranchThetaTerm (q : ℂ) (j : Int) : ℂ :=
  (-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))

/-- The infinite base theta series attached to the paired nonzero residue branches.-/
noncomputable def theorem44CoeffPairedBranchThetaSeries (q : ℂ) : ℂ :=
  ∑' j : ℤ, theorem44CoeffPairedBranchThetaTerm q j

/-- Symmetric finite partial sum of the paired-branch terms over `-N ≤ j ≤ N`.-/
noncomputable def theorem44CoeffPairedBranchTermPartial
    (q z : ℂ) (r : Int) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), theorem44CoeffPairedBranchTerm q z r j

/--
Symmetric finite partial sum of the two raw nonzero residue monomials over
`-N ≤ j ≤ N`, before packaging them as the named paired branch.-/
noncomputable def theorem44CoeffMonomialPairPartial
    (q z : ℂ) (r : Int) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    (z ^ (3 * r) *
        ((-1 : ℂ) ^ (3 * j) * q ^ theorem44CoeffExponentIndex (3 * r) (3 * j)) +
      z ^ (-(3 * r) - 1) *
        ((-1 : ℂ) ^ (3 * j + 1) *
          q ^ theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1)))

private theorem summable_norm_theorem44Product_tail0 (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-q ^ (n + 1)‖ := by
  have h := Ch02.summable_norm_mul_geometric_complex (-q) q hq
  refine h.congr fun n => ?_
  congr 1
  rw [show -q * q ^ n = -q ^ (n + 1) by
    rw [pow_succ]
    ring]

private theorem summable_norm_theorem44Product_tail1 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z * q ^ (n + 1))‖ := by
  have h := Ch02.summable_norm_mul_geometric_complex (-(z * q)) q hq
  refine h.congr fun n => ?_
  congr 1
  rw [show -(z * q) * q ^ n = -(z * q ^ (n + 1)) by
    rw [pow_succ]
    ring]

private theorem summable_norm_theorem44Product_tail2 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z⁻¹ * q ^ n)‖ := by
  have h := Ch02.summable_norm_mul_geometric_complex (-z⁻¹) q hq
  refine h.congr fun n => ?_
  congr 1
  ring

private theorem summable_norm_theorem44Product_tail3 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z ^ 2 * q ^ (2 * n + 1))‖ := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(z ^ 2 * q)) (q ^ 2) hq2
  refine h.congr fun n => ?_
  congr 1
  rw [show -(z ^ 2 * q) * (q ^ 2) ^ n = -(z ^ 2 * q ^ (2 * n + 1)) by
    rw [← pow_mul]
    rw [show 2 * n + 1 = 1 + 2 * n by omega]
    rw [pow_add]
    ring]

private theorem summable_norm_theorem44Product_tail4 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z⁻¹ ^ 2 * q ^ (2 * n + 1))‖ := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(z⁻¹ ^ 2 * q)) (q ^ 2) hq2
  refine h.congr fun n => ?_
  congr 1
  rw [show -(z⁻¹ ^ 2 * q) * (q ^ 2) ^ n =
      -(z⁻¹ ^ 2 * q ^ (2 * n + 1)) by
    rw [← pow_mul]
    rw [show 2 * n + 1 = 1 + 2 * n by omega]
    rw [pow_add]
    ring]

/-- Chan Theorem 4.4's product side is multipliable for `‖q‖ < 1`.
@isnad1 id=multipli.1h2v.s5.60a02b87268e from=translated src=- shape=b3a194db vocab=d25a8aa6
-/
theorem multipliable_theorem44ProductFactor (q z : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => theorem44ProductFactor q z n := by
  have h0 : Multipliable fun n : ℕ => 1 - q ^ (n + 1) := by
    have h := multipliable_one_add_of_summable (summable_norm_theorem44Product_tail0 q hq)
    simpa [sub_eq_add_neg] using h
  have h1 : Multipliable fun n : ℕ => 1 - z * q ^ (n + 1) := by
    have h := multipliable_one_add_of_summable (summable_norm_theorem44Product_tail1 q z hq)
    simpa [sub_eq_add_neg] using h
  have h2 : Multipliable fun n : ℕ => 1 - z⁻¹ * q ^ n := by
    have h := multipliable_one_add_of_summable (summable_norm_theorem44Product_tail2 q z hq)
    simpa [sub_eq_add_neg] using h
  have h3 : Multipliable fun n : ℕ => 1 - z ^ 2 * q ^ (2 * n + 1) := by
    have h := multipliable_one_add_of_summable (summable_norm_theorem44Product_tail3 q z hq)
    simpa [sub_eq_add_neg] using h
  have h4 : Multipliable fun n : ℕ => 1 - z⁻¹ ^ 2 * q ^ (2 * n + 1) := by
    have h := multipliable_one_add_of_summable (summable_norm_theorem44Product_tail4 q z hq)
    simpa [sub_eq_add_neg] using h
  exact ((((h0.mul h1).mul h2).mul h3).mul h4).congr fun n => by
    simp [theorem44ProductFactor, mul_assoc]

/-- The finite Theorem 4.4 product partials tend to the infinite product side.
@isnad1 id=tendsto.1h2v.s5.29a45f7c3e02 from=translated src=- shape=06ca52cc vocab=6daf84e3
-/
theorem tendsto_theorem44ProductPartial (q z : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => theorem44ProductPartial q z N) atTop
      (𝓝 (theorem44ProductLHS q z)) := by
  have h := (multipliable_theorem44ProductFactor q z hq).tendsto_prod_tprod_nat
  simpa [theorem44ProductLHS, theorem44ProductPartial] using h

/-- Exponent `n(3n+1)/2` in Chan Theorem 4.4's series side.-/
def theorem44SeriesExponentIndex (n : Int) : Nat :=
  Int.toNat (n * (3 * n + 1) / 2)

/-- Chan Theorem 4.4's displayed series term.-/
noncomputable def theorem44SeriesTerm (q z : ℂ) (n : ℤ) : ℂ :=
  q ^ theorem44SeriesExponentIndex n * (z ^ (3 * n) - z ^ (-(3 * n) - 1))

/-- Chan Theorem 4.4's displayed series side.-/
noncomputable def theorem44SeriesRHS (q z : ℂ) : ℂ :=
  ∑' n : ℤ, theorem44SeriesTerm q z n

/-- Exponent `n(3n+1)` in Theorem 4.4 after the substitution `q ↦ q^2`.-/
def theorem44SubstitutedQuadraticIndex (n : Int) : Nat :=
  Int.toNat (n * (3 * n + 1))

/-- Theorem 4.4 series term after the substitution `q ↦ q^2`, `z ↦ z/q`.-/
noncomputable def theorem44SubstitutedSeriesTerm (q z : ℂ) (n : ℤ) : ℂ :=
  q ^ theorem44SubstitutedQuadraticIndex n *
    ((z / q) ^ (3 * n) - (z / q) ^ (-(3 * n + 1)))

/-- Theorem 4.4 series side after the substitution `q ↦ q^2`, `z ↦ z/q`.-/
noncomputable def theorem44SubstitutedSeriesRHS (q z : ℂ) : ℂ :=
  ∑' n : ℤ, theorem44SubstitutedSeriesTerm q z n

/-- One summand on the RHS of the Eq. (2.12) quintuple product identity.-/
noncomputable def quintupleProductTerm (q z : R) (n : Int) : R :=
  q ^ quintupleQuadraticIndex n *
    (intPow (z / q) (3 * n) - intPow (q / z) (3 * n + 1))

/--
Complex RHS summand in Jacobi-series form:
`(z^3/q^2)^n (q^3)^{n^2} - (q/z) (q^4/z^3)^n (q^3)^{n^2}`.-/
noncomputable def quintupleProductSeriesTerm (q z : ℂ) (n : ℤ) : ℂ :=
  (z ^ 3 / q ^ 2) ^ n * (q ^ 3) ^ (n ^ 2) -
    (q / z) * ((q ^ 4 / z ^ 3) ^ n * (q ^ 3) ^ (n ^ 2))

/-- Infinite bilateral series side of the quintuple product identity.-/
noncomputable def quintupleProductRHS (q z : ℂ) : ℂ :=
  ∑' n : ℤ, quintupleProductSeriesTerm q z n

/-- First Nat-indexed JTP product factor occurring in the quintuple product proof.-/
noncomputable def quintupleJacobiLeftFactor (q z : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (6 * n + 6)) *
    (1 + z ^ 3 * q ^ (6 * n + 1)) *
    (1 + (z ^ 3)⁻¹ * q ^ (6 * n + 5))

/-- Second Nat-indexed JTP product factor occurring in the quintuple product proof.-/
noncomputable def quintupleJacobiRightFactor (q z : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (6 * n + 6)) *
    (1 + q ^ (6 * n + 7) / z ^ 3) *
    (1 + z ^ 3 * q ^ (6 * n + 3) / q ^ 4)

/-- First product-side JTP factor after the quintuple substitution.
@isnad1 id=eq.2h3v.s6.22374ec31740 from=translated src=- shape=3665fa89 vocab=978d72ca
-/
theorem jacobiProductNatFactor_quintuple_left_substitution
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (n : ℕ) :
    Ch02.jacobiProductNatFactor (q ^ 3) (z ^ 3 / q ^ 2) n =
      quintupleJacobiLeftFactor q z n := by
  simp [quintupleJacobiLeftFactor, Ch02.jacobiProductNatFactor,
    Ch02.jacobiProductEvenFactor, Ch02.jacobiProductOddFactor]
  have heven : (q ^ 3) ^ (2 * (n + 1)) = q ^ (6 * n + 6) := by
    rw [← pow_mul]
    congr 1
    omega
  have hodd1 : z ^ 3 / q ^ 2 * (q ^ 3) ^ (2 * (n + 1) - 1) =
      z ^ 3 * q ^ (6 * n + 1) := by
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
    rw [← pow_mul]
    rw [show 3 * (2 * n + 1) = 6 * n + 3 by omega]
    field_simp [hq]
    rw [show 6 * n + 3 = (6 * n + 1) + 2 by omega]
    rw [pow_add]
    ring
  have hodd2 : q ^ 2 / z ^ 3 * (q ^ 3) ^ (2 * (n + 1) - 1) =
      (z ^ 3)⁻¹ * q ^ (6 * n + 5) := by
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
    rw [← pow_mul]
    rw [show 3 * (2 * n + 1) = 6 * n + 3 by omega]
    field_simp [hz]
    rw [show 6 * n + 5 = 2 + (6 * n + 3) by omega]
    rw [pow_add]
    ring
  rw [heven, hodd1, hodd2]

/-- Second product-side JTP factor after the quintuple substitution.
@isnad1 id=eq.0h3v.s6.a68bbb0bfe1d from=translated src=- shape=ccc1bba2 vocab=0b7c004c
-/
theorem jacobiProductNatFactor_quintuple_right_substitution (q z : ℂ) (n : ℕ) :
    Ch02.jacobiProductNatFactor (q ^ 3) (q ^ 4 / z ^ 3) n =
      quintupleJacobiRightFactor q z n := by
  simp [quintupleJacobiRightFactor, Ch02.jacobiProductNatFactor,
    Ch02.jacobiProductEvenFactor, Ch02.jacobiProductOddFactor]
  have heven : (q ^ 3) ^ (2 * (n + 1)) = q ^ (6 * n + 6) := by
    rw [← pow_mul]
    congr 1
    omega
  have hodd1 : q ^ 4 / z ^ 3 * (q ^ 3) ^ (2 * (n + 1) - 1) =
      q ^ (6 * n + 7) / z ^ 3 := by
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
    rw [← pow_mul]
    rw [show 3 * (2 * n + 1) = 6 * n + 3 by omega]
    rw [show 6 * n + 7 = 4 + (6 * n + 3) by omega]
    rw [pow_add]
    ring
  have hodd2 : z ^ 3 / q ^ 4 * (q ^ 3) ^ (2 * (n + 1) - 1) =
      z ^ 3 * q ^ (6 * n + 3) / q ^ 4 := by
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
    rw [← pow_mul]
    rw [show 3 * (2 * n + 1) = 6 * n + 3 by omega]
    ring
  rw [heven, hodd1, hodd2]

/-- The explicit product-difference side obtained by applying JTP to the quintuple RHS.-/
noncomputable def quintupleProductExplicitRHS (q z : ℂ) : ℂ :=
  (∏' n : ℕ, quintupleJacobiLeftFactor q z n) -
    (q / z) * (∏' n : ℕ, quintupleJacobiRightFactor q z n)

/-- Finite partial product of the first explicit JTP factor family.-/
noncomputable def quintupleJacobiLeftPartial (q z : ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, quintupleJacobiLeftFactor q z n

/-- Finite partial product of the second explicit JTP factor family.-/
noncomputable def quintupleJacobiRightPartial (q z : ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, quintupleJacobiRightFactor q z n

/-- Finite product-difference partials for the explicit product RHS bottleneck.-/
noncomputable def quintupleProductExplicitRHSPartial (q z : ℂ) (N : ℕ) : ℂ :=
  quintupleJacobiLeftPartial q z N - (q / z) * quintupleJacobiRightPartial q z N

/--
Weighted Laurent finite sum obtained by expanding the first finite JTP sum in
the explicit quintuple RHS partial.-/
noncomputable def quintupleFiniteJTPLeftWeightedSummand (q z : ℂ) (N k : ℕ) : ℂ :=
  gaussianBinom (q ^ 6) (2 * N) k *
    (z ^ 3 / q ^ 2) ^ ((k : Int) - (N : Int)) *
      (q ^ 3) ^ (((k : Int) - (N : Int)) ^ 2)

/--
Weighted Laurent finite sum obtained by expanding the second finite JTP sum in
the explicit quintuple RHS partial.-/
noncomputable def quintupleFiniteJTPRightWeightedSummand (q z : ℂ) (N k : ℕ) : ℂ :=
  gaussianBinom (q ^ 6) (2 * N) k *
    (q ^ 4 / z ^ 3) ^ ((k : Int) - (N : Int)) *
      (q ^ 3) ^ (((k : Int) - (N : Int)) ^ 2)

/-- Combined summand for the weighted Laurent difference in the explicit RHS partial.-/
noncomputable def quintupleFiniteJTPCombinedWeightedSummand (q z : ℂ) (N k : ℕ) : ℂ :=
  quintupleFiniteJTPLeftWeightedSummand q z N k -
    (q / z) * quintupleFiniteJTPRightWeightedSummand q z N k

/-- First weighted Laurent finite sum in the explicit quintuple RHS partial.-/
noncomputable def quintupleFiniteJTPLeftWeightedSum (q z : ℂ) (N : ℕ) : ℂ :=
  natSum (quintupleFiniteJTPLeftWeightedSummand q z N) (2 * N)

/-- Second weighted Laurent finite sum in the explicit quintuple RHS partial.-/
noncomputable def quintupleFiniteJTPRightWeightedSum (q z : ℂ) (N : ℕ) : ℂ :=
  natSum (quintupleFiniteJTPRightWeightedSummand q z N) (2 * N)

/-- Combined weighted Laurent finite sum in the explicit quintuple RHS partial.-/
noncomputable def quintupleFiniteJTPCombinedWeightedSum (q z : ℂ) (N : ℕ) : ℂ :=
  natSum (quintupleFiniteJTPCombinedWeightedSummand q z N) (2 * N)

/-- Combined weighted summand after splitting the Laurent monomials into `z` and `q` powers.-/
noncomputable def quintupleFiniteJTPCombinedMonomialSummand (q z : ℂ) (N k : ℕ) : ℂ :=
  let l : Int := (k : Int) - (N : Int)
  gaussianBinom (q ^ 6) (2 * N) k *
    (z ^ (3 * l) * q ^ (3 * l ^ 2 - 2 * l) -
      z ^ (-(3 * l) - 1) * q ^ (3 * l ^ 2 + 4 * l + 1))

/-- Combined weighted Laurent finite sum in monomial-split form.-/
noncomputable def quintupleFiniteJTPCombinedMonomialSum (q z : ℂ) (N : ℕ) : ℂ :=
  natSum (quintupleFiniteJTPCombinedMonomialSummand q z N) (2 * N)

/-- The first weighted Laurent monomial split into separate `z` and `q` powers.
@isnad1 id=eq.1h3v.s7.5a1921a4bf0c from=translated src=- shape=2f03d267 vocab=52705b58
-/
theorem quintupleFiniteJTPLeftMonomial_eq_zpow_qpow
    (q z : ℂ) (hq : q ≠ 0) (l : Int) :
    (z ^ 3 / q ^ 2) ^ l * (q ^ 3) ^ (l ^ 2) =
      z ^ (3 * l) * q ^ (3 * l ^ 2 - 2 * l) := by
  rw [div_zpow]
  change (z ^ (3 : ℤ)) ^ l / (q ^ (2 : ℤ)) ^ l * (q ^ (3 : ℤ)) ^ (l ^ 2) =
      z ^ (3 * l) * q ^ (3 * l ^ 2 - 2 * l)
  rw [← zpow_mul, ← zpow_mul, ← zpow_mul]
  rw [div_eq_mul_inv]
  rw [← zpow_neg]
  rw [show z ^ (3 * l) * q ^ (-(2 * l)) * q ^ (3 * l ^ 2) =
      z ^ (3 * l) * (q ^ (-(2 * l)) * q ^ (3 * l ^ 2)) by ring_nf]
  rw [← (zpow_add₀ hq (-(2 * l)) (3 * l ^ 2))]
  congr 1
  ring_nf

/-- The scaled second weighted Laurent monomial split into separate `z` and `q` powers.
@isnad1 id=eq.2h3v.s8.3bccee235044 from=translated src=- shape=61cdf852 vocab=4788fbd3
-/
theorem quintupleFiniteJTPRightScaledMonomial_eq_zpow_qpow
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (l : Int) :
    (q / z) * ((q ^ 4 / z ^ 3) ^ l * (q ^ 3) ^ (l ^ 2)) =
      z ^ (-(3 * l) - 1) * q ^ (3 * l ^ 2 + 4 * l + 1) := by
  rw [div_zpow]
  change q / z * ((q ^ (4 : ℤ)) ^ l / (z ^ (3 : ℤ)) ^ l *
      (q ^ (3 : ℤ)) ^ (l ^ 2)) =
      z ^ (-(3 * l) - 1) * q ^ (3 * l ^ 2 + 4 * l + 1)
  rw [← zpow_mul, ← zpow_mul, ← zpow_mul]
  rw [div_eq_mul_inv]
  rw [div_eq_mul_inv]
  rw [← zpow_neg]
  rw [← zpow_neg_one z]
  rw [show q * z ^ (-1 : ℤ) * (q ^ (4 * l) * z ^ (-(3 * l)) * q ^ (3 * l ^ 2)) =
      (z ^ (-(3 * l)) * z ^ (-1 : ℤ)) *
        ((q ^ (4 * l) * q ^ (3 * l ^ 2)) * q) by ring_nf]
  rw [← (zpow_add₀ hz (-(3 * l)) (-1))]
  rw [← (zpow_add₀ hq (4 * l) (3 * l ^ 2))]
  rw [show q ^ (4 * l + 3 * l ^ 2) * q =
      q ^ (4 * l + 3 * l ^ 2) * q ^ (1 : Int) by simp]
  rw [← (zpow_add₀ hq (4 * l + 3 * l ^ 2) 1)]
  congr 1
  all_goals ring_nf

/-- Symmetric nonzero pair term in the quintuple RHS bilateral series.-/
noncomputable def quintupleProductSeriesSymmetricPairTerm (q z : ℂ) (r : ℕ) : ℂ :=
  quintupleProductSeriesTerm q z (-(((r + 1 : ℕ) : Int))) +
    quintupleProductSeriesTerm q z (((r + 1 : ℕ) : Int))

/-- Fixed symmetric nonzero pair partial in the quintuple RHS bilateral series.-/
noncomputable def quintupleProductSeriesSymmetricPairPartial
    (q z : ℂ) (M : ℕ) : ℂ :=
  ∑ r ∈ Finset.range M, quintupleProductSeriesSymmetricPairTerm q z r

/-- Fixed symmetric partial in the quintuple RHS bilateral series.-/
noncomputable def quintupleProductSeriesSymmetricPartial (q z : ℂ) (M : ℕ) : ℂ :=
  quintupleProductSeriesTerm q z 0 + quintupleProductSeriesSymmetricPairPartial q z M

/-- Finite Gaussian-weighted symmetric nonzero pair in the monomial-split combined sum.-/
noncomputable def quintupleFiniteJTPCombinedMonomialPairTerm
    (q z : ℂ) (N r : ℕ) : ℂ :=
  quintupleFiniteJTPCombinedMonomialSummand q z N (N - (r + 1)) +
    quintupleFiniteJTPCombinedMonomialSummand q z N (N + (r + 1))

/-- Fixed finite Gaussian-weighted symmetric nonzero pair partial.-/
noncomputable def quintupleFiniteJTPCombinedMonomialPairPartial
    (q z : ℂ) (N M : ℕ) : ℂ :=
  ∑ r ∈ Finset.range M, quintupleFiniteJTPCombinedMonomialPairTerm q z N r

/-- Fixed finite Gaussian-weighted symmetric partial including the center term.-/
noncomputable def quintupleFiniteJTPCombinedMonomialSymmetricPartial
    (q z : ℂ) (N M : ℕ) : ℂ :=
  quintupleFiniteJTPCombinedMonomialSummand q z N N +
    quintupleFiniteJTPCombinedMonomialPairPartial q z N M

/-- The weighted Laurent difference combines into a single inclusive `natSum`.
@isnad1 id=eq.0h3v.s5.73986bd9473a from=translated src=- shape=ae01e814 vocab=ed27c215
-/
theorem quintupleFiniteJTPWeightedSum_sub_eq_combined
    (q z : ℂ) (N : ℕ) :
    quintupleFiniteJTPLeftWeightedSum q z N -
        (q / z) * quintupleFiniteJTPRightWeightedSum q z N =
      quintupleFiniteJTPCombinedWeightedSum q z N := by
  rw [quintupleFiniteJTPLeftWeightedSum, quintupleFiniteJTPRightWeightedSum,
    quintupleFiniteJTPCombinedWeightedSum]
  induction 2 * N with
  | zero =>
      simp [quintupleFiniteJTPCombinedWeightedSummand]
  | succ M ih =>
      rw [natSum_succ, natSum_succ, natSum_succ, ← ih]
      simp [quintupleFiniteJTPCombinedWeightedSummand]
      ring_nf

/-- The combined weighted Laurent summand equals the monomial-split summand.
@isnad1 id=eq.2h4v.s5.e55128ba792e from=translated src=- shape=d2bc7810 vocab=d0c2e919
-/
theorem quintupleFiniteJTPCombinedWeightedSummand_eq_monomialSummand
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N k : ℕ) :
    quintupleFiniteJTPCombinedWeightedSummand q z N k =
      quintupleFiniteJTPCombinedMonomialSummand q z N k := by
  unfold quintupleFiniteJTPCombinedWeightedSummand
    quintupleFiniteJTPLeftWeightedSummand quintupleFiniteJTPRightWeightedSummand
    quintupleFiniteJTPCombinedMonomialSummand
  set l : Int := (k : Int) - (N : Int)
  have hleft := quintupleFiniteJTPLeftMonomial_eq_zpow_qpow q z hq l
  have hright := quintupleFiniteJTPRightScaledMonomial_eq_zpow_qpow q z hq hz l
  calc
    gaussianBinom (q ^ 6) (2 * N) k * (z ^ 3 / q ^ 2) ^ l * (q ^ 3) ^ l ^ 2 -
        q / z * (gaussianBinom (q ^ 6) (2 * N) k * (q ^ 4 / z ^ 3) ^ l *
          (q ^ 3) ^ l ^ 2) =
      gaussianBinom (q ^ 6) (2 * N) k * ((z ^ 3 / q ^ 2) ^ l * (q ^ 3) ^ l ^ 2) -
        gaussianBinom (q ^ 6) (2 * N) k *
          ((q / z) * ((q ^ 4 / z ^ 3) ^ l * (q ^ 3) ^ l ^ 2)) := by ring
    _ = gaussianBinom (q ^ 6) (2 * N) k *
        (z ^ (3 * l) * q ^ (3 * l ^ 2 - 2 * l)) -
        gaussianBinom (q ^ 6) (2 * N) k *
          (z ^ (-(3 * l) - 1) * q ^ (3 * l ^ 2 + 4 * l + 1)) := by
      rw [hleft, hright]
    _ = gaussianBinom (q ^ 6) (2 * N) k *
        (z ^ (3 * l) * q ^ (3 * l ^ 2 - 2 * l) -
          z ^ (-(3 * l) - 1) * q ^ (3 * l ^ 2 + 4 * l + 1)) := by ring

/-- The combined weighted Laurent sum equals its monomial-split form.
@isnad1 id=eq.2h3v.s5.ba9f81a82084 from=translated src=- shape=40a02e31 vocab=559dc074
-/
theorem quintupleFiniteJTPCombinedWeightedSum_eq_monomialSum
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    quintupleFiniteJTPCombinedWeightedSum q z N =
      quintupleFiniteJTPCombinedMonomialSum q z N := by
  unfold quintupleFiniteJTPCombinedWeightedSum quintupleFiniteJTPCombinedMonomialSum
  exact Ch03.natSum_congr_le (2 * N) fun k _ =>
    quintupleFiniteJTPCombinedWeightedSummand_eq_monomialSummand q z hq hz N k

/-- The first explicit JTP factor family is multipliable.
@isnad1 id=multipli.3h2v.s6.4b7faa34a4d7 from=translated src=- shape=5d40c8c0 vocab=a2b0b635
-/
theorem multipliable_quintupleJacobiLeftFactor
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    Multipliable fun n : ℕ => quintupleJacobiLeftFactor q z n := by
  have hq3norm : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
  exact (Ch02.multipliable_jacobiProductNatFactor (q ^ 3) (z ^ 3 / q ^ 2) hq3norm).congr
    fun n => jacobiProductNatFactor_quintuple_left_substitution q z hq hz n

/-- The second explicit JTP factor family is multipliable.
@isnad1 id=multipli.1h2v.s5.352d1e17f85a from=translated src=- shape=b3a194db vocab=87239914
-/
theorem multipliable_quintupleJacobiRightFactor (q z : ℂ) (hqnorm : ‖q‖ < 1) :
    Multipliable fun n : ℕ => quintupleJacobiRightFactor q z n := by
  have hq3norm : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
  exact (Ch02.multipliable_jacobiProductNatFactor (q ^ 3) (q ^ 4 / z ^ 3) hq3norm).congr
    fun n => jacobiProductNatFactor_quintuple_right_substitution q z n

/-- The first explicit JTP partial products tend to their infinite product.
@isnad1 id=tendsto.3h2v.s6.51d49ad86a95 from=translated src=- shape=c66bace0 vocab=9e53f6fb
-/
theorem tendsto_quintupleJacobiLeftPartial
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    Tendsto (fun N : ℕ => quintupleJacobiLeftPartial q z N) atTop
      (𝓝 (∏' n : ℕ, quintupleJacobiLeftFactor q z n)) := by
  have h := (multipliable_quintupleJacobiLeftFactor q z hqnorm hq hz).tendsto_prod_tprod_nat
  simpa [quintupleJacobiLeftPartial] using h

/-- The second explicit JTP partial products tend to their infinite product.
@isnad1 id=tendsto.1h2v.s6.8ba81d89916a from=translated src=- shape=64456f22 vocab=f4a1fe99
-/
theorem tendsto_quintupleJacobiRightPartial (q z : ℂ) (hqnorm : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => quintupleJacobiRightPartial q z N) atTop
      (𝓝 (∏' n : ℕ, quintupleJacobiRightFactor q z n)) := by
  have h := (multipliable_quintupleJacobiRightFactor q z hqnorm).tendsto_prod_tprod_nat
  simpa [quintupleJacobiRightPartial] using h

/-- The explicit RHS finite product-difference partials tend to the explicit RHS.
@isnad1 id=tendsto.3h2v.s6.2205dc1d8b53 from=translated src=- shape=eff83584 vocab=ee2c67da
-/
theorem tendsto_quintupleProductExplicitRHSPartial
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    Tendsto (fun N : ℕ => quintupleProductExplicitRHSPartial q z N) atTop
      (𝓝 (quintupleProductExplicitRHS q z)) := by
  have hleft := tendsto_quintupleJacobiLeftPartial q z hqnorm hq hz
  have hright := tendsto_quintupleJacobiRightPartial q z hqnorm
  have hscaled :
      Tendsto (fun N : ℕ => (q / z) * quintupleJacobiRightPartial q z N) atTop
        (𝓝 ((q / z) * (∏' n : ℕ, quintupleJacobiRightFactor q z n))) :=
    tendsto_const_nhds.mul hright
  simpa [quintupleProductExplicitRHSPartial, quintupleProductExplicitRHS] using
    hleft.sub hscaled

/--
If the finite difference between the quintuple LHS truncation and the explicit
product RHS partial tends to zero, then the explicit product identity follows.
@isnad1 id=eq.4h2v.s6.5cb8e3bad000 from=translated src=- shape=048bf4eb vocab=c2498ed2
-/
theorem quintupleProduct_explicitProduct_of_tendsto_trunc_sub_explicit
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h :
      Tendsto
        (fun N : ℕ =>
          quintupleProductLHSTrunc q z N - quintupleProductExplicitRHSPartial q z N)
        atTop (𝓝 0)) :
    quintupleProductLHS q z = quintupleProductExplicitRHS q z := by
  have hlim :
      Tendsto
        (fun N : ℕ =>
          quintupleProductLHSTrunc q z N - quintupleProductExplicitRHSPartial q z N)
        atTop (𝓝 (quintupleProductLHS q z - quintupleProductExplicitRHS q z)) :=
    (tendsto_quintupleProductLHSTrunc q z hqnorm).sub
      (tendsto_quintupleProductExplicitRHSPartial q z hqnorm hq hz)
  have hzero : quintupleProductLHS q z - quintupleProductExplicitRHS q z = 0 :=
    (tendsto_nhds_unique h hlim).symm
  exact sub_eq_zero.mp hzero

/-- Quintuple product RHS truncated: the bilateral sum over `-N ≤ n ≤ N`.-/
noncomputable def quintupleProductRHSTrunc (q z : R) (N : Nat) : R :=
  bilateralSum (quintupleProductTerm q z) N

/-- Sanity: the zero truncations unfold to the expected first terms.
@isnad1 id=and.0h3v.s6.e1d1a90a7eb1 from=translated src=- shape=2cdc2e9c vocab=553bafc5
-/
theorem quintupleProduct_truncated_zero (q z : R) :
    quintupleProductLHSTrunc q z 0 = 1 ∧
      quintupleProductRHSTrunc q z 0 = 1 - q / z := by
  constructor
  · rfl
  · simp [quintupleProductRHSTrunc, quintupleProductTerm, quintupleQuadraticIndex,
      intPow]

/- The infinite quintuple product identity is deferred to the JTP specialization
and rewriting layer used in Chan's proof. -/

/-! ### Finite JTP specialized at z = 1: Euler pentagonal general identity -/

/--
Specializing the finite Jacobi triple product at `z = 1`:
`(1; q)_n * (q; q)_n = finiteJTPRHS q 1 n`.

When `z = 1`, the factor `z⁻¹ * q = q`, so the LHS becomes
`qPoch 1 q n * qPoch q q n`.
@isnad1 id=eq.1h3v.s6.4527f738f107 from=translated src=- shape=6100f924 vocab=cf9709c4
-/
theorem finite_jtp_at_z_one (q : R) (hq : q ≠ 0) (n : Nat) :
    qPoch 1 q n * qPoch q q n = finiteJTPRHS q 1 n := by
  have h := finite_jacobi_triple_product q 1 one_ne_zero hq n
  rwa [inv_one, one_mul] at h

/--
`qPoch 1 q n = 0` for any `n ≥ 1`: the first factor `(1 - 1 * q^0) = 0`
kills the entire product.
@isnad1 id=eq.1h3v.s5.04feb5b72413 from=translated src=- shape=f058290e vocab=f84f0a30
-/
theorem qPoch_one_eq_zero (q : R) (n : Nat) (hn : 1 ≤ n) :
    qPoch (1 : R) q n = 0 := by
  cases n with
  | zero => omega
  | succ m =>
    induction m with
    | zero => simp [qPoch]
    | succ k ih =>
      rw [qPoch_succ]
      have : qPoch (1 : R) q (k + 1) = 0 := ih (by omega)
      rw [this]
      simp

/-- Succ-indexed form of `qPoch_one_eq_zero`, convenient for finite truncations.
@isnad1 id=eq.0h3v.s5.85612daf01fd from=translated src=- shape=6edd2a16 vocab=8c53096b
-/
theorem qPoch_one_succ_eq_zero (q : R) (n : Nat) :
    qPoch (1 : R) q (n + 1) = 0 :=
  qPoch_one_eq_zero q (n + 1) (by omega)

/--
The finite JTP RHS vanishes at `z = 1` for all `n ≥ 1`.  This is the
general truncated pentagonal vanishing identity: the bilateral sum
`∑_{k=0}^{2n} [2n choose k]_q · q^{(k-n)(k-n-1)/2} · (-1)^{k-n}`
equals zero for every `n ≥ 1`.
@isnad1 id=eq.2h3v.s6.ae5d4f10e560 from=translated src=- shape=355dd46e vocab=b17f9208
-/
theorem finiteJTPRHS_at_z_one_eq_zero (q : R) (hq : q ≠ 0) (n : Nat) (hn : 1 ≤ n) :
    finiteJTPRHS q 1 n = 0 := by
  have h := finite_jtp_at_z_one q hq n
  rw [qPoch_one_eq_zero q n hn, zero_mul] at h
  exact h.symm

/--
`qPoch q q n = qPochhammer q n` restated in Chapter 4 context
(already in Basic as `qPoch_q_eq_qPochhammer`).
@isnad1 id=eq.0h3v.s4.d4682b266cbb from=translated src=- shape=e5128f7a vocab=aa68661a
-/
theorem qPoch_q_eq_eulerProduct (q : R) (n : Nat) :
    qPoch q q n = eulerPentagonalProductTrunc q n := by
  simp [eulerPentagonalProductTrunc, qPoch_q_eq_qPochhammer]

/--
Restatement using the Chapter 4 Euler product notation:
`finiteJTPRHS q 1 n = 0` for `n ≥ 1`, connecting to `eulerPentagonalProductTrunc`.
@isnad1 id=eq.2h3v.s6.ae5d4f10e560 from=translated src=- shape=355dd46e vocab=b17f9208
-/
theorem euler_pentagonal_jtp_connection (q : R) (hq : q ≠ 0) (n : Nat) (hn : 1 ≤ n) :
    finiteJTPRHS q 1 n = 0 :=
  finiteJTPRHS_at_z_one_eq_zero q hq n hn

end Field

/-! ### Quintuple product identity: final assembly via Tannery-style convergence

The strategy: prove both the LHS product truncation and the qPoch⁶×combinedMonomialSum
converge to `quintupleProductLHS`, then their difference → 0, closing the identity.

Key bridge: a generic "fixed-core + uniform-tail" convergence lemma. -/

section QuintupleAssembly

open scoped Topology
open Filter

/-- Generic diagonal-convergence lemma: if `C N M → P M` for fixed M,
`P M → L`, and the tail `S N - C N M` is uniformly small for large M,
then `S N → L`.
@isnad1 id=tendsto.3h4v.s7.021392538835 from=translated src=- shape=9218f8d6 vocab=04f4dac8
-/
theorem tendsto_of_fixed_core_and_uniform_tail
    {S : ℕ → ℂ} {C : ℕ → ℕ → ℂ} {P : ℕ → ℂ} {L : ℂ}
    (hfixed : ∀ M : ℕ, Tendsto (fun N : ℕ => C N M) atTop (𝓝 (P M)))
    (hP : Tendsto P atTop (𝓝 L))
    (htail : ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ᶠ N in atTop, ‖S N - C N M‖ < ε) :
    Tendsto S atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨K₁, hK₁⟩ := Metric.tendsto_atTop.mp hP (ε / 3) hε3
  obtain ⟨K₂, hK₂⟩ := htail (ε / 3) hε3
  set M := max K₁ K₂
  have hM1 : M ≥ K₁ := le_max_left _ _
  have hM2 : M ≥ K₂ := le_max_right _ _
  have h_PM : dist (P M) L < ε / 3 := hK₁ M hM1
  have h_tail_ev := hK₂ M hM2
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (hfixed M) (ε / 3) hε3
  rw [Filter.eventually_atTop] at h_tail_ev
  obtain ⟨N₂, hN₂⟩ := h_tail_ev
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have h_core : dist (C N M) (P M) < ε / 3 := hN₁ N (by omega)
  have h_tail : ‖S N - C N M‖ < ε / 3 := hN₂ N (by omega)
  have h_dist_tail : dist (S N) (C N M) < ε / 3 := by
    rwa [Complex.dist_eq]
  linarith [dist_triangle (S N) (C N M) L,
            dist_triangle (C N M) (P M) L]

/-! ### Quintuple product: uniform tail estimate for the combined monomial sum -/

/-- The normalized full combined-monomial sum used in the finite JTP
factorization of the quintuple product.-/
noncomputable def qPoch_qsix_mul_quintupleCombinedMonomialSum (q z : ℂ) (N : ℕ) : ℂ :=
  qPoch (q ^ 6) (q ^ 6) N * quintupleFiniteJTPCombinedMonomialSum q z N

/-- The normalized fixed symmetric core of the combined-monomial sum.-/
noncomputable def qPoch_qsix_mul_quintupleCombinedMonomialCore (q z : ℂ) (N M : ℕ) : ℂ :=
  qPoch (q ^ 6) (q ^ 6) N * quintupleFiniteJTPCombinedMonomialSymmetricPartial q z N M

/-- The normalized combined-monomial tail.-/
noncomputable def qPoch_qsix_mul_quintupleCombinedMonomialTail (q z : ℂ) (N M : ℕ) : ℂ :=
  qPoch_qsix_mul_quintupleCombinedMonomialSum q z N -
    qPoch_qsix_mul_quintupleCombinedMonomialCore q z N M

/-- Split-norm majorant: ∑' (‖f(-(M+r+1))‖ + ‖f(M+r+1)‖). Easier to bound than ‖pair‖.-/
noncomputable def quintupleSplitNormMajorantTail (q z : ℂ) (M : ℕ) : ℝ :=
  ∑' r : ℕ, (‖quintupleProductSeriesTerm q z (-(↑(M + r) + 1 : ℤ))‖ +
    ‖quintupleProductSeriesTerm q z ((↑(M + r) : ℤ) + 1)‖)

/-- Split-norm majorant tails tend to zero.
@isnad1 id=tendsto.1h2v.s5.28ece984213d from=translated src=- shape=2cb040ad vocab=084dded1
-/
theorem tendsto_quintupleSplitNormMajorantTail_zero (q z : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (quintupleSplitNormMajorantTail q z) atTop (𝓝 0) := by
  set g := fun r : ℕ =>
    ‖quintupleProductSeriesTerm q z (-(↑r + 1 : ℤ))‖ +
      ‖quintupleProductSeriesTerm q z ((↑r : ℤ) + 1)‖
  have : quintupleSplitNormMajorantTail q z = fun i => ∑' k, g (k + i) := by
    ext i
    simp only [quintupleSplitNormMajorantTail, g]
    congr 1; ext k
    congr 2 <;> push_cast <;> ring
  rw [this]
  exact tendsto_sum_nat_add g

/-! Dead Route B end-cap removed: the bridge to `quintupleProductRHS` is now
done entirely via Route A (JTP product decomposition) below. The upstream
`qPoch_qsix_mul_quintupleCombinedMonomial*` and `tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomial*`
infrastructure is retained in case it's useful for future routes. -/

/-! #### Route A: Product decomposition via JTP

The quintuple product factors decompose as:
  quintupleProductFactor(n) = JacobiNatFactor(q, -z, n) × JacobiNatFactor(q², -z²/q², n) / (1-q^{4n+4})

At the infinite product level:
  quintupleProductLHS = jacobiInfiniteProduct(q, -z) × jacobiInfiniteProduct(q², -z²/q²) / (q⁴;q⁴)_∞

Then JTP converts each infinite product to a bilateral series, and the product
of two series (after mod-3 regrouping) gives ExplicitRHS. -/

/-- Sub-lemma 1: Cauchy product + shear reindex + Fubini.-/
def quintupleShearEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 + 2 * p.2, p.2)
  invFun p := (p.1 - 2 * p.2, p.2)
  left_inv := fun p => by ext <;> simp <;> ring
  right_inv := fun p => by ext <;> simp <;> ring

end QuintupleAssembly

/- Theorem 4.3 (Jacobi's identity) lives in `Chapter04_T43.lean`. -/

end Ch04
end PartI
end QseriesFormalization
