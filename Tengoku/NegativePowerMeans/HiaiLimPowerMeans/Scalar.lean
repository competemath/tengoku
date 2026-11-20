import Tengoku.Seed.Analysis.MeanInequalities
import Tengoku.Seed.Data.Fin.Rev

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar inequalities used in the power-mean proof

This file formalizes two parts of the paper that do not depend on operator
theory:

* the AM--GM step turning the normalized trace estimate into a product bound;
* the inversion step turning lower spectral-product bounds for a positive
  order into weak log-majorization for the corresponding negative order.
-/

namespace HiaiLimPowerMeans

open Finset
open scoped BigOperators

/-- Product of the first `k` entries of a vector of length `n`.-/
def prefixProd {n : ℕ} (x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : ℝ :=
  ∏ i : Fin k, x (Fin.castLE hk i)

/-- A positive vector written in decreasing order.-/
def PositiveDecreasing {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ Antitone x

/-- Weak log-majorization for positive vectors written in decreasing order.
The ordering and positivity conditions are part of the proposition, so an
instance of this definition is literally the standard finite-dimensional
relation rather than merely its prefix-product inequalities.-/
def WeakLogMajorized {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  PositiveDecreasing x ∧ PositiveDecreasing y ∧
    ∀ (k : ℕ) (_hk0 : 0 < k) (hk : k ≤ n),
      prefixProd x k hk ≤ prefixProd y k hk

/-- The lower-product relation used for increasingly ordered eigenvalues.-/
def LowerProductDominates {n : ℕ} (y q : Fin n → ℝ) : Prop :=
  ∀ (k : ℕ) (_hk0 : 0 < k) (hk : k ≤ n),
    prefixProd q k hk ≤ prefixProd y k hk

/--
@isnad1 id=lt.2h3v.s5.1e0f4deefe38 from=translated src=- shape=62ea9baf vocab=0904bc3f
-/
lemma prefixProd_pos {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 < x i)
    (k : ℕ) (hk : k ≤ n) : 0 < prefixProd x k hk := by
  unfold prefixProd
  exact Finset.prod_pos fun i _ ↦ hx _

/--
@isnad1 id=eq.1h3v.s5.676557f1ddc5 from=translated src=- shape=ffeeb909 vocab=a029059f
-/
lemma prefixProd_inv {n : ℕ} (x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    prefixProd (fun i ↦ (x i)⁻¹) k hk = (prefixProd x k hk)⁻¹ := by
  simp [prefixProd]

/-- Inverting a lower-product comparison reverses it and gives weak
log-majorization.  This is the scalar core of the final duality argument.
@isnad1 id=weaklogm.5h3v.s6.abb2574d2a99 from=translated src=- shape=e37c6503 vocab=cf236571
-/
theorem inv_weakLogMajorized_of_lowerProductDominates
    {n : ℕ} {y q : Fin n → ℝ}
    (hy : ∀ i, 0 < y i) (hq : ∀ i, 0 < q i)
    (hy_mono : Monotone y) (hq_mono : Monotone q)
    (h : LowerProductDominates y q) :
    WeakLogMajorized (fun i ↦ (y i)⁻¹) (fun i ↦ (q i)⁻¹) := by
  refine ⟨⟨fun i ↦ inv_pos.mpr (hy i), ?_⟩,
    ⟨fun i ↦ inv_pos.mpr (hq i), ?_⟩, ?_⟩
  · intro i j hij
    exact (inv_le_inv₀ (hy j) (hy i)).2 (hy_mono hij)
  · intro i j hij
    exact (inv_le_inv₀ (hq j) (hq i)).2 (hq_mono hij)
  · intro k hk0 hk
    rw [prefixProd_inv, prefixProd_inv]
    exact (inv_le_inv₀ (prefixProd_pos hy k hk) (prefixProd_pos hq k hk)).2
      (h k hk0 hk)

/-- The unweighted AM--GM consequence used in the determinant proposition.
@isnad1 id=le.2h2v.s6.8c220e06d43d from=translated src=- shape=b043e541 vocab=799be5d7
-/
theorem product_le_one_of_sum_le_card
    {n : ℕ} [NeZero n] {z : Fin n → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hsum : ∑ i, z i ≤ (n : ℝ)) :
    ∏ i, z i ≤ 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hgm := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin n))
    (fun _ ↦ (1 : ℝ)) z (by simp) (by simpa using hn) (by simpa using hz)
  have hroot : (∏ i, z i) ^ (n : ℝ)⁻¹ ≤ 1 := by
    calc
      (∏ i, z i) ^ (n : ℝ)⁻¹ ≤ (∑ i, z i) / (n : ℝ) := by simpa using hgm
      _ ≤ 1 := (div_le_one hn).2 hsum
  have hprod : 0 ≤ ∏ i, z i := Finset.prod_nonneg fun i _ ↦ hz i
  simpa using (Real.rpow_inv_le_iff_of_pos hprod zero_le_one hn).1 hroot

/-- If the normalized trace argument gives
`sum ((q i / y i)^t) ≤ n`, then AM--GM gives `prod q ≤ prod y`.
This is exactly the final scalar step of the determinant proposition.
@isnad1 id=le.4h4v.s7.d4ab4c5b7696 from=translated src=- shape=2bcf6b68 vocab=91b52f4a
-/
theorem product_le_product_of_sum_rpow_div_le_card
    {n : ℕ} [NeZero n] {q y : Fin n → ℝ} {t : ℝ}
    (hq : ∀ i, 0 < q i) (hy : ∀ i, 0 < y i) (ht : 0 < t)
    (htrace : ∑ i, (q i / y i) ^ t ≤ (n : ℝ)) :
    ∏ i, q i ≤ ∏ i, y i := by
  let z : Fin n → ℝ := fun i ↦ (q i / y i) ^ t
  have hz : ∀ i, 0 ≤ z i := fun i ↦ Real.rpow_nonneg (div_nonneg (hq i).le (hy i).le) _
  have hzprod : ∏ i, z i ≤ 1 :=
    product_le_one_of_sum_le_card hz (by simpa [z] using htrace)
  have hq0 : 0 ≤ ∏ i, q i := (Finset.prod_pos fun i _ ↦ hq i).le
  have hy0 : 0 ≤ ∏ i, y i := (Finset.prod_pos fun i _ ↦ hy i).le
  have hypos : 0 < ∏ i, y i := Finset.prod_pos fun i _ ↦ hy i
  have hratio_nonneg : 0 ≤ (∏ i, q i) / ∏ i, y i := div_nonneg hq0 hy0
  have hratio_rpow : ((∏ i, q i) / ∏ i, y i) ^ t ≤ 1 := by
    calc
      ((∏ i, q i) / ∏ i, y i) ^ t = (∏ i, q i / y i) ^ t := by
        rw [Finset.prod_div_distrib]
      _ = ∏ i, (q i / y i) ^ t :=
        (Real.finsetProd_rpow Finset.univ (fun i ↦ q i / y i)
          (fun i _ ↦ div_nonneg (hq i).le (hy i).le) t).symm
      _ = ∏ i, z i := rfl
      _ ≤ 1 := hzprod
  have hratio : (∏ i, q i) / ∏ i, y i ≤ 1 := by
    have := (Real.rpow_le_rpow_iff hratio_nonneg zero_le_one ht).1
      (by simpa using hratio_rpow)
    simpa using this
  exact (div_le_one hypos).1 hratio

end HiaiLimPowerMeans
