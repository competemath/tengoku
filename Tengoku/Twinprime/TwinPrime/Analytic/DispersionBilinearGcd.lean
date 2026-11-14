import Tengoku.Twinprime.TwinPrime.Analytic.DispersionLargeGcd

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual bilinear subrange with large gcd of the two factors

The sums retain the original signed coefficient and the exact product interval.
Only sparsity of pairs with a large gcd is used in the bound.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

/-- The dyadic factor pairs with gcd greater than `G`.-/
def bilinearBoxLargeGcdPairs (U V M N G : ℕ) : Finset (ℕ × ℕ) :=
  ((dispersionLeft U M).product (dispersionRight V N)).filter
    (fun dr => G < Nat.gcd dr.1 dr.2)

/-- The large-gcd part of the actual box; `dispersionEntry` retains the
characteristic function of `X < d*r ≤ 2X`.-/
def bilinearBoxLargeGcd (U V X M N G : ℕ) : ℝ :=
  ∑ dr ∈ bilinearBoxLargeGcdPairs U V M N G,
    vaughanBeta V dr.2 * dispersionEntry X dr.1 dr.2

def bilinearBoxSmallGcd (U V X M N G : ℕ) : ℝ :=
  ∑ dr ∈ ((dispersionLeft U M).product (dispersionRight V N)).filter
      (fun dr => Nat.gcd dr.1 dr.2 ≤ G),
    vaughanBeta V dr.2 * dispersionEntry X dr.1 dr.2

/-- Any restriction of the box is exactly the corresponding restriction of
the finite global factor domain.-/
theorem bilinearBox_filtered_eq_filtered_pair_sum (U V X M N : ℕ)
    (P : ℕ × ℕ → Prop) [DecidablePred P] :
    (∑ dr ∈ ((dispersionLeft U M).product (dispersionRight V N)).filter P,
      vaughanBeta V dr.2 * dispersionEntry X dr.1 dr.2) =
    ∑ dr ∈ (bilinearPairs U V X).filter
        (fun dr => (M < dr.1 ∧ dr.1 ≤ 2 * M ∧ N < dr.2 ∧ dr.2 ≤ 2 * N) ∧ P dr),
      (μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2) := by
  have hset :
      (((dispersionLeft U M).product (dispersionRight V N)).filter
        (fun dr => X < dr.1 * dr.2 ∧ dr.1 * dr.2 ≤ 2 * X)).filter P =
      (bilinearPairs U V X).filter
        (fun dr => (M < dr.1 ∧ dr.1 ≤ 2 * M ∧ N < dr.2 ∧ dr.2 ≤ 2 * N) ∧ P dr) := by
    rw [dispersion_boxPairs_eq, filter_filter]
  rw [← hset]
  simp only [sum_filter]
  apply sum_congr rfl
  intro dr _
  by_cases hP : P dr <;>
    by_cases hprod : X < dr.1 * dr.2 ∧ dr.1 * dr.2 ≤ 2 * X <;>
    simp [hP, hprod, dispersionEntry]
  all_goals ring

theorem bilinearBoxLargeGcd_eq_filtered_pair_sum (U V X M N G : ℕ) :
    bilinearBoxLargeGcd U V X M N G =
      ∑ dr ∈ (bilinearPairs U V X).filter
          (fun dr => (M < dr.1 ∧ dr.1 ≤ 2 * M ∧ N < dr.2 ∧ dr.2 ≤ 2 * N) ∧
            G < Nat.gcd dr.1 dr.2),
        (μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2) :=
  bilinearBox_filtered_eq_filtered_pair_sum U V X M N _

theorem bilinearBoxSmallGcd_eq_filtered_pair_sum (U V X M N G : ℕ) :
    bilinearBoxSmallGcd U V X M N G =
      ∑ dr ∈ (bilinearPairs U V X).filter
          (fun dr => (M < dr.1 ∧ dr.1 ≤ 2 * M ∧ N < dr.2 ∧ dr.2 ≤ 2 * N) ∧
            Nat.gcd dr.1 dr.2 ≤ G),
        (μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2) :=
  bilinearBox_filtered_eq_filtered_pair_sum U V X M N _

theorem bilinearBox_eq_smallGcd_add_largeGcd (U V X M N G : ℕ) :
    bilinearBox U V X M N =
      bilinearBoxSmallGcd U V X M N G + bilinearBoxLargeGcd U V X M N G := by
  have hbox : bilinearBox U V X M N =
      ∑ dr ∈ (dispersionLeft U M).product (dispersionRight V N),
        vaughanBeta V dr.2 * dispersionEntry X dr.1 dr.2 := by
    simp only [bilinearBox, Finset.product_eq_sprod, sum_product, mul_sum]
    rw [sum_comm]
  rw [hbox]
  simp only [bilinearBoxSmallGcd, bilinearBoxLargeGcd, bilinearBoxLargeGcdPairs,
    sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro dr _
  by_cases hg : Nat.gcd dr.1 dr.2 ≤ G
  · simp [hg, not_lt.mpr hg]
  · simp [hg, lt_of_not_ge hg]

theorem bilinearBoxLargeGcdPairs_card_le (U V M N G : ℕ) (hG : 1 ≤ G) :
    ((bilinearBoxLargeGcdPairs U V M N G).card : ℝ) ≤ 4 * (M : ℝ) * N / G := by
  have hsub : bilinearBoxLargeGcdPairs U V M N G ⊆
      ((Ioc 0 (2 * M)).product (Ioc 0 (2 * N))).filter
        (fun dr => G < Nat.gcd dr.1 dr.2) := by
    intro dr hdr
    rcases mem_filter.mp hdr with ⟨hdr, hg⟩
    rcases mem_product.mp hdr with ⟨hd, hr⟩
    have hdI := mem_Ioc.mp (mem_filter.mp hd).1
    have hrI := mem_Ioc.mp (mem_filter.mp hr).1
    exact mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_Ioc.mpr ⟨by omega, hdI.2⟩, mem_Ioc.mpr ⟨by omega, hrI.2⟩⟩, hg⟩
  calc
    _ ≤ ((((Ioc 0 (2 * M)).product (Ioc 0 (2 * N))).filter
        (fun dr => G < Nat.gcd dr.1 dr.2)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    _ ≤ ((2 * M : ℕ) : ℝ) * (2 * N : ℕ) / G :=
      card_largeGcd_rectangle_le (2 * M) (2 * N) G hG
    _ = _ := by push_cast; ring

theorem abs_bilinearBoxLargeGcd_le_card (U V X M N G : ℕ) (hN : 1 ≤ N) :
    |bilinearBoxLargeGcd U V X M N G| ≤
      (bilinearBoxLargeGcdPairs U V M N G).card *
        Real.log (2 * N) * Real.log (2 * X + 2) := by
  have hLN : 0 ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * N by omega))
  calc
    _ ≤ ∑ dr ∈ bilinearBoxLargeGcdPairs U V M N G,
        |vaughanBeta V dr.2 * dispersionEntry X dr.1 dr.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _dr ∈ bilinearBoxLargeGcdPairs U V M N G,
        Real.log (2 * N) * Real.log (2 * X + 2) := by
      apply sum_le_sum
      intro dr hdr
      have hr := (mem_product.mp (mem_filter.mp hdr).1).2
      have hrI := mem_Ioc.mp (mem_filter.mp hr).1
      have hbeta : vaughanBeta V dr.2 ≤ Real.log (2 * N) :=
        (vaughanBeta_le_log V dr.2).trans (Real.log_le_log
          (by exact_mod_cast (show 0 < dr.2 by omega)) (by exact_mod_cast hrI.2))
      rw [abs_mul, abs_of_nonneg (vaughanBeta_nonneg V dr.2)]
      exact mul_le_mul hbeta (abs_dispersionEntry_le_log X dr.1 dr.2)
        (abs_nonneg _) hLN
    _ = _ := by simp; ring

/-- The actual large-gcd bilinear subrange saves a factor `G`, without any
prime-distribution hypothesis.-/
theorem abs_bilinearBoxLargeGcd_le (U V X M N G : ℕ)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hG : 1 ≤ G) (hMN : M * N ≤ 2 * X) :
    |bilinearBoxLargeGcd U V X M N G| ≤
      8 * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 / G := by
  have hNbound : N ≤ 2 * X :=
    (Nat.le_mul_of_pos_left N hM).trans hMN
  have hlogN : Real.log (2 * (N : ℝ)) ≤ Real.log (4 * X + 4) :=
    Real.log_le_log (by positivity)
      (by have : (N : ℝ) ≤ 2 * X := by exact_mod_cast hNbound
          linarith)
  have hlogX : Real.log (2 * (X : ℝ) + 2) ≤ Real.log (4 * X + 4) :=
    Real.log_le_log (by positivity)
      (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  have hlogN0 : 0 ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * N by omega))
  have hlogX0 : 0 ≤ Real.log (2 * (X : ℝ) + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  have hlog0 : 0 ≤ Real.log (4 * (X : ℝ) + 4) :=
    hlogX0.trans hlogX
  have hprod : (M : ℝ) * N ≤ 2 * X := by exact_mod_cast hMN
  have hGr : 0 < (G : ℝ) := by exact_mod_cast (show 0 < G by omega)
  calc
    _ ≤ (bilinearBoxLargeGcdPairs U V M N G).card *
        Real.log (2 * N) * Real.log (2 * X + 2) :=
      abs_bilinearBoxLargeGcd_le_card U V X M N G hN
    _ ≤ (4 * (M : ℝ) * N / G) * Real.log (2 * N) * Real.log (2 * X + 2) := by
      gcongr
      exact bilinearBoxLargeGcdPairs_card_le U V M N G hG
    _ = (4 / (G : ℝ)) * ((M : ℝ) * N) * Real.log (2 * N) *
        Real.log (2 * X + 2) := by ring
    _ ≤ (4 / (G : ℝ)) * (2 * (X : ℝ)) * Real.log (4 * X + 4) *
        Real.log (4 * X + 4) := by gcongr
    _ = _ := by ring

end TwinPrime.Analytic
