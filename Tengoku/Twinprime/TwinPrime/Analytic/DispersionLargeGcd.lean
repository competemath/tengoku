import Tengoku.Twinprime.TwinPrime.Analytic.Dispersion
import Tengoku.Seed.Analysis.PSeries
import Tengoku.Seed.Data.Nat.Factorization.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Elementary large-gcd ranges in the exact dispersion off-diagonal

Both orientations of each distinct pair are retained. The product interval and
the shift by two remain inside `dispersionEntry`. The large-gcd estimate uses
only counting multiples and the elementary coefficient bounds.
-/

noncomputable section

open Finset ArithmeticFunction

namespace TwinPrime.Analytic

/-- The inverse-square tail, including the empty interval when `n < k`.
@isnad1 id=le.1h2v.s5.e8bc930da314 from=translated src=- shape=4f9722e9 vocab=eea0ea3e
-/
theorem sum_Ioc_inv_sq_le_inv (k n : ℕ) (hk : 1 ≤ k) :
    (∑ i ∈ Ioc k n, ((i : ℝ) ^ 2)⁻¹) ≤ (k : ℝ)⁻¹ := by
  by_cases hkn : k ≤ n
  · exact (sum_Ioc_inv_sq_le_sub (by omega) hkn).trans
      (sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg n)))
  · simp [Ioc_eq_empty_of_le (by omega : n ≤ k)]

/-- Counting pairs with a large gcd in an arbitrary positive integer rectangle.
The diagonal may be included in this elementary upper bound.
@isnad1 id=le.1h3v.s6.1f1ef9826c43 from=translated src=- shape=ba41ad09 vocab=b706f9b4
-/
theorem card_largeGcd_rectangle_le (A B G : ℕ) (hG : 1 ≤ G) :
    ((((Ioc 0 A).product (Ioc 0 B)).filter
      (fun de => G < Nat.gcd de.1 de.2)).card : ℝ) ≤ (A : ℝ) * B / G := by
  let P : ℕ → Finset (ℕ × ℕ) := fun g =>
    ((Ioc 0 A).filter (g ∣ ·)).product ((Ioc 0 B).filter (g ∣ ·))
  have hcover : ((Ioc 0 A).product (Ioc 0 B)).filter
      (fun de => G < Nat.gcd de.1 de.2) ⊆ (Ioc G A).biUnion P := by
    intro de hde
    rcases mem_filter.mp hde with ⟨hde, hlarge⟩
    rcases mem_product.mp hde with ⟨hd, he⟩
    have hdpos := (mem_Ioc.mp hd).1
    have hgA : Nat.gcd de.1 de.2 ≤ A :=
      (Nat.le_of_dvd hdpos (Nat.gcd_dvd_left _ _)).trans (mem_Ioc.mp hd).2
    apply mem_biUnion.mpr
    refine ⟨Nat.gcd de.1 de.2, mem_Ioc.mpr ⟨hlarge, hgA⟩, ?_⟩
    exact mem_product.mpr ⟨mem_filter.mpr ⟨hd, Nat.gcd_dvd_left _ _⟩,
      mem_filter.mpr ⟨he, Nat.gcd_dvd_right _ _⟩⟩
  have hcard : (((((Ioc 0 A).product (Ioc 0 B)).filter
      (fun de => G < Nat.gcd de.1 de.2)).card : ℕ) : ℝ) ≤
      ∑ g ∈ Ioc G A, ((P g).card : ℝ) := by
    exact_mod_cast (card_le_card hcover).trans card_biUnion_le
  calc
    _ ≤ ∑ g ∈ Ioc G A, ((P g).card : ℝ) := hcard
    _ ≤ ∑ g ∈ Ioc G A, ((A : ℝ) * B) * ((g : ℝ) ^ 2)⁻¹ := by
      apply sum_le_sum
      intro g hg
      have hg0 : 0 < g := by have := (mem_Ioc.mp hg).1; omega
      have hgr : 0 < (g : ℝ) := by exact_mod_cast hg0
      have hdiv (n : ℕ) : ((n / g : ℕ) : ℝ) ≤ (n : ℝ) / g := by
        apply (le_div_iff₀ hgr).mpr
        exact_mod_cast Nat.div_mul_le_self n g
      simp only [P, Finset.product_eq_sprod, card_product,
        Nat.Ioc_filter_dvd_card_eq_div, Nat.cast_mul]
      calc
        _ ≤ ((A : ℝ) / g) * ((B : ℝ) / g) := by
          exact mul_le_mul (hdiv A) (hdiv B) (Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
    _ = ((A : ℝ) * B) * ∑ g ∈ Ioc G A, ((g : ℝ) ^ 2)⁻¹ := by
      rw [mul_sum]
    _ ≤ ((A : ℝ) * B) * (G : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_inv G A hG) (by positivity)
    _ = _ := by rw [div_eq_mul_inv]

/-- Ordered distinct left-factor pairs whose gcd exceeds the threshold.-/
def dispersionLargeGcdPairs (U M G : ℕ) : Finset (ℕ × ℕ) :=
  ((dispersionLeft U M).product (dispersionLeft U M)).filter
    (fun de => de.1 ≠ de.2 ∧ G < Nat.gcd de.1 de.2)

/-- The complementary ordered distinct left-factor pairs.-/
def dispersionSmallGcdPairs (U M G : ℕ) : Finset (ℕ × ℕ) :=
  ((dispersionLeft U M).product (dispersionLeft U M)).filter
    (fun de => de.1 ≠ de.2 ∧ Nat.gcd de.1 de.2 ≤ G)

def dispersionOffDiagonalLargeGcd (U V X M N G : ℕ) : ℝ :=
  ∑ r ∈ dispersionRight V N, vaughanBeta V r *
    ∑ de ∈ dispersionLargeGcdPairs U M G,
      dispersionEntry X de.1 r * dispersionEntry X de.2 r

def dispersionOffDiagonalSmallGcd (U V X M N G : ℕ) : ℝ :=
  ∑ r ∈ dispersionRight V N, vaughanBeta V r *
    ∑ de ∈ dispersionSmallGcdPairs U M G,
      dispersionEntry X de.1 r * dispersionEntry X de.2 r

/--
@isnad1 id=le.1h3v.s6.c95381882f9d from=translated src=- shape=45b161b4 vocab=1be6740c
-/
theorem dispersionLargeGcdPairs_card_le (U M G : ℕ) (hG : 1 ≤ G) :
    ((dispersionLargeGcdPairs U M G).card : ℝ) ≤ 4 * (M : ℝ) ^ 2 / G := by
  have hsub : dispersionLargeGcdPairs U M G ⊆
      ((Ioc 0 (2 * M)).product (Ioc 0 (2 * M))).filter
        (fun de => G < Nat.gcd de.1 de.2) := by
    intro de hde
    rcases mem_filter.mp hde with ⟨hde, _, hg⟩
    rcases mem_product.mp hde with ⟨hd, he⟩
    have hdI := mem_Ioc.mp (mem_filter.mp hd).1
    have heI := mem_Ioc.mp (mem_filter.mp he).1
    exact mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_Ioc.mpr ⟨by omega, hdI.2⟩, mem_Ioc.mpr ⟨by omega, heI.2⟩⟩, hg⟩
  calc
    _ ≤ ((((Ioc 0 (2 * M)).product (Ioc 0 (2 * M))).filter
        (fun de => G < Nat.gcd de.1 de.2)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    _ ≤ ((2 * M : ℕ) : ℝ) * (2 * M : ℕ) / G :=
      card_largeGcd_rectangle_le (2 * M) (2 * M) G hG
    _ = _ := by push_cast; ring

/--
@isnad1 id=eq.0h6v.s5.3a132481320d from=translated src=- shape=3b3c0b1f vocab=b7ef7216
-/
theorem dispersionOffDiagonal_eq_small_add_large (U V X M N G : ℕ) :
    dispersionOffDiagonal U V X M N =
      dispersionOffDiagonalSmallGcd U V X M N G +
        dispersionOffDiagonalLargeGcd U V X M N G := by
  unfold dispersionOffDiagonal dispersionOffDiagonalSmallGcd
    dispersionOffDiagonalLargeGcd
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro r _
  rw [← mul_add]
  congr 1
  simp only [dispersionSmallGcdPairs, dispersionLargeGcdPairs, sum_filter,
    Finset.product_eq_sprod, sum_product]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  rw [← sum_add_distrib]
  calc
    _ = ∑ e ∈ dispersionLeft U M,
        if d ≠ e then dispersionEntry X d r * dispersionEntry X e r else 0 := by
      rw [← sum_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext e
      simp [mem_erase, ne_comm, and_comm]
    _ = _ := by
      apply sum_congr rfl
      intro e _
      by_cases hde : d = e <;> by_cases hg : Nat.gcd d e ≤ G <;>
        simp [hde, hg, show (G < Nat.gcd d e) ↔ ¬ Nat.gcd d e ≤ G from not_le.symm]

/-- Before any pair counting, bounded entries control the restricted sum.
@isnad1 id=le.0h6v.s6.662958cc5802 from=translated src=- shape=7a194afa vocab=df13be6e
-/
theorem abs_dispersionOffDiagonalLargeGcd_le_card (U V X M N G : ℕ) :
    |dispersionOffDiagonalLargeGcd U V X M N G| ≤
      (dispersionLargeGcdPairs U M G).card * (Real.log (2 * X + 2)) ^ 2 *
        dispersionMass V N := by
  have hL : 0 ≤ Real.log (2 * (X : ℝ) + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  calc
    _ ≤ ∑ r ∈ dispersionRight V N, |vaughanBeta V r *
        ∑ de ∈ dispersionLargeGcdPairs U M G,
          dispersionEntry X de.1 r * dispersionEntry X de.2 r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ dispersionRight V N, vaughanBeta V r *
        ((dispersionLargeGcdPairs U M G).card * (Real.log (2 * X + 2)) ^ 2) := by
      apply sum_le_sum
      intro r _
      rw [abs_mul, abs_of_nonneg (vaughanBeta_nonneg V r)]
      apply mul_le_mul_of_nonneg_left _ (vaughanBeta_nonneg V r)
      calc
        _ ≤ ∑ de ∈ dispersionLargeGcdPairs U M G,
            |dispersionEntry X de.1 r * dispersionEntry X de.2 r| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _de ∈ dispersionLargeGcdPairs U M G, (Real.log (2 * X + 2)) ^ 2 := by
          apply sum_le_sum
          intro de _
          rw [abs_mul, sq]
          exact mul_le_mul (abs_dispersionEntry_le_log X de.1 r)
            (abs_dispersionEntry_le_log X de.2 r) (abs_nonneg _) hL
        _ = _ := by simp
    _ = _ := by rw [← sum_mul]; unfold dispersionMass; ring

/--
@isnad1 id=le.1h6v.s7.60c8246acfca from=translated src=- shape=2123a983 vocab=c131e47b
-/
theorem abs_dispersionOffDiagonalLargeGcd_le (U V X M N G : ℕ) (hG : 1 ≤ G) :
    |dispersionOffDiagonalLargeGcd U V X M N G| ≤
      (4 * (M : ℝ) ^ 2 / G) * (Real.log (2 * X + 2)) ^ 2 *
        dispersionMass V N := by
  exact (abs_dispersionOffDiagonalLargeGcd_le_card U V X M N G).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (dispersionLargeGcdPairs_card_le U M G hG)
        (sq_nonneg _)) (dispersionMass_nonneg V N))

/-- A finite large-gcd saving on the true dyadic product range.
@isnad1 id=le.4h6v.s7.931cc0b9f2a6 from=translated src=- shape=08627c44 vocab=c131e47b
-/
theorem dispersion_mass_mul_abs_largeGcd_le (U V X M N G : ℕ)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hG : 1 ≤ G) (hMN : M * N ≤ 2 * X) :
    dispersionMass V N * |dispersionOffDiagonalLargeGcd U V X M N G| ≤
      16 * (X : ℝ) ^ 2 * (Real.log (4 * X + 4)) ^ 4 / G := by
  have hmass := dispersionMass_le V N hN
  have hmass0 := dispersionMass_nonneg V N
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
  have hprod : (M : ℝ) * N ≤ 2 * X := by exact_mod_cast hMN
  have hGr : 0 < (G : ℝ) := by exact_mod_cast (show 0 < G by omega)
  calc
    _ ≤ dispersionMass V N *
        ((4 * (M : ℝ) ^ 2 / G) * (Real.log (2 * X + 2)) ^ 2 *
          dispersionMass V N) :=
      mul_le_mul_of_nonneg_left (abs_dispersionOffDiagonalLargeGcd_le U V X M N G hG)
        hmass0
    _ = (4 * (M : ℝ) ^ 2 / G) * (Real.log (2 * X + 2)) ^ 2 *
        (dispersionMass V N) ^ 2 := by ring
    _ ≤ (4 * (M : ℝ) ^ 2 / G) * (Real.log (2 * X + 2)) ^ 2 *
        (N * Real.log (2 * N)) ^ 2 := by gcongr
    _ = (4 / (G : ℝ)) * ((M : ℝ) * N) ^ 2 *
        (Real.log (2 * N)) ^ 2 * (Real.log (2 * X + 2)) ^ 2 := by ring
    _ ≤ (4 / (G : ℝ)) * (2 * (X : ℝ)) ^ 2 *
        (Real.log (4 * X + 4)) ^ 2 * (Real.log (4 * X + 4)) ^ 2 := by gcongr
    _ = _ := by ring

end TwinPrime.Analytic
