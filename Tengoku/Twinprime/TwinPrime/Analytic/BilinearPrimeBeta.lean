import Tengoku.Twinprime.TwinPrime.Analytic.DispersionSquareFactor
import Tengoku.Twinprime.TwinPrime.Analytic.BilinearExceptional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Removing proper prime powers from the beta coefficient

The replacement keeps the prime divisors strictly above the cutoff. The
error is measured in absolute factorwise mass on the original product interval.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

def primeVaughanBeta (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun r => ∑ p ∈ r.divisors, if V < p ∧ p.Prime then vonMangoldt p else 0, by simp⟩

/--
@isnad1 id=eq.0h2v.s6.178927178de2 from=translated src=- shape=b6cc75a7 vocab=38899813
-/
theorem primeVaughanBeta_apply (V r : ℕ) :
    primeVaughanBeta V r = ∑ p ∈ r.divisors, if V < p ∧ p.Prime then vonMangoldt p else 0 := rfl

/--
@isnad1 id=eq.0h2v.s5.ac94a9b0c30c from=translated src=- shape=d9f1ae6a vocab=76b62868
-/
theorem vaughanBeta_sub_primeVaughanBeta (V r : ℕ) :
    vaughanBeta V r - primeVaughanBeta V r =
      ∑ b ∈ r.divisors.filter (V < ·), nonprimeMangoldt b := by
  rw [vaughanBeta_apply, primeVaughanBeta_apply, ← sum_sub_distrib, sum_filter]
  apply sum_congr rfl
  intro b _
  by_cases hV : V < b <;> by_cases hp : b.Prime <;> simp [hV, hp, nonprimeMangoldt]

/--
@isnad1 id=le.0h2v.s4.d4c6f7c5d4b8 from=translated src=- shape=f54b5217 vocab=ec95c1e4
-/
theorem primeVaughanBeta_nonneg (V r : ℕ) : 0 ≤ primeVaughanBeta V r := by
  rw [primeVaughanBeta_apply]
  exact sum_nonneg fun _ _ => by split_ifs <;> positivity

/--
@isnad1 id=le.0h2v.s5.99dcfcf515eb from=translated src=- shape=686dc35f vocab=1ba7f942
-/
theorem primeVaughanBeta_le (V r : ℕ) : primeVaughanBeta V r ≤ vaughanBeta V r := by
  have h := sum_nonneg (s := r.divisors.filter (V < ·))
    (fun b _ => nonprimeMangoldt_nonneg b)
  rw [← vaughanBeta_sub_primeVaughanBeta] at h
  linarith

/--
@isnad1 id=le.1h2v.s6.7bf40c4e4932 from=translated src=- shape=9622d6f2 vocab=f79abc5d
-/
theorem positiveHyperbola_right_dvd_card_le (T b : ℕ) (hb : 0 < b) :
    (((positiveHyperbolaPairs T).filter (fun dr => b ∣ dr.2)).card : ℝ) ≤
      (T : ℝ) / b * (1 + Real.log T) := by
  let f : ℕ × ℕ → ℕ × ℕ := fun dk => (dk.1, b * dk.2)
  have hsub : (positiveHyperbolaPairs T).filter (fun dr => b ∣ dr.2) ⊆
      (positiveHyperbolaPairs (T / b)).image f := by
    intro dr hdr
    rcases mem_filter.mp hdr with ⟨hdr, k, hk⟩
    rcases (mem_positiveHyperbolaPairs_iff T dr).mp hdr with ⟨hd0, hr0, hprod⟩
    apply mem_image.mpr
    refine ⟨(dr.1, k), (mem_positiveHyperbolaPairs_iff _ _).mpr ⟨hd0, ?_, ?_⟩, ?_⟩
    · by_contra h
      have : k = 0 := by omega
      simp [this] at hk
      omega
    · apply (Nat.le_div_iff_mul_le hb).mpr
      rw [hk] at hprod
      nlinarith only [hprod]
    · exact Prod.ext rfl hk.symm
  have hc : (((positiveHyperbolaPairs T).filter (fun dr => b ∣ dr.2)).card : ℝ) ≤
      (positiveHyperbolaPairs (T / b)).card := by
    exact_mod_cast (card_le_card hsub).trans card_image_le
  apply hc.trans
  by_cases hz : T / b = 0
  · simpa [hz, positiveHyperbolaPairs] using
      (show (0 : ℝ) ≤ (T : ℝ) / b * (1 + Real.log T) by positivity)
  have ht : (0 : ℝ) < (T / b : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  calc
    _ ≤ ((T / b : ℕ) : ℝ) * (1 + Real.log (T / b : ℕ)) := positiveHyperbolaPairs_card_le _
    _ ≤ ((T / b : ℕ) : ℝ) * (1 + Real.log T) :=
      mul_le_mul_of_nonneg_left
        (_root_.add_le_add le_rfl (Real.log_le_log ht (by exact_mod_cast Nat.div_le_self T b)))
        (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)

/--
@isnad1 id=le.1h3v.s6.37f60f65c1cc from=translated src=- shape=d8999609 vocab=db0d9bdf
-/
theorem sum_hyperbola_divisor_tail_le (T V : ℕ) (a : ℕ → ℝ) (ha : ∀ b, 0 ≤ a b) :
    (∑ dr ∈ positiveHyperbolaPairs T, ∑ b ∈ dr.2.divisors.filter (V < ·), a b) ≤
      (T : ℝ) * (1 + Real.log T) * ∑ b ∈ Ioc V T, a b / b := by
  classical
  have hset (r : ℕ) (hr0 : 0 < r) (hrT : r ≤ T) :
      r.divisors.filter (V < ·) = (Ioc V T).filter (· ∣ r) := by
    ext b
    simp only [mem_filter, Nat.mem_divisors, mem_Ioc]
    constructor
    · rintro ⟨⟨hbr, _⟩, hV⟩
      exact ⟨⟨hV, (Nat.le_of_dvd hr0 hbr).trans hrT⟩, hbr⟩
    · rintro ⟨⟨hV, _⟩, hbr⟩
      exact ⟨⟨hbr, hr0.ne'⟩, hV⟩
  have he : (∑ dr ∈ positiveHyperbolaPairs T, ∑ b ∈ dr.2.divisors.filter (V < ·), a b) =
      ∑ b ∈ Ioc V T, a b * (((positiveHyperbolaPairs T).filter (fun dr => b ∣ dr.2)).card : ℝ) := by
    calc
      _ = ∑ dr ∈ positiveHyperbolaPairs T, ∑ b ∈ Ioc V T, if b ∣ dr.2 then a b else 0 := by
        apply sum_congr rfl
        intro dr hdr
        have hp := (mem_positiveHyperbolaPairs_iff T dr).mp hdr
        rw [hset dr.2 hp.2.1 ((Nat.le_mul_of_pos_left dr.2 hp.1).trans hp.2.2), sum_filter]
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro b _
        rw [← sum_filter]
        simp [mul_comm]
  rw [he, mul_sum]
  apply sum_le_sum
  intro b hb
  calc
    _ ≤ a b * ((T : ℝ) / b * (1 + Real.log T)) :=
      mul_le_mul_of_nonneg_left (positiveHyperbola_right_dvd_card_le T b (by have := (mem_Ioc.mp hb).1; omega))
        (ha b)
    _ = _ := by ring

def bilinearPrimeBeta (U V X : ℕ) : ℝ :=
  ∑ dr ∈ bilinearPairs U V X,
    (μ dr.1 : ℝ) * primeVaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2)

def bilinearPrimeBetaErrorMass (U V X : ℕ) : ℝ :=
  ∑ dr ∈ bilinearPairs U V X,
    |(μ dr.1 : ℝ) * (vaughanBeta V dr.2 - primeVaughanBeta V dr.2) *
      vonMangoldt (dr.1 * dr.2 + 2)|

/--
@isnad1 id=le.0h3v.s4.05dbd6ac5024 from=translated src=- shape=1995cd38 vocab=746b86b5
-/
theorem bilinearPrimeBetaErrorMass_nonneg (U V X : ℕ) :
    0 ≤ bilinearPrimeBetaErrorMass U V X := sum_nonneg fun _ _ => abs_nonneg _

/--
@isnad1 id=le.0h3v.s5.4586f852527d from=translated src=- shape=502a303e vocab=e7581f64
-/
theorem abs_bilinear_sub_primeBeta_le_mass (U V X : ℕ) :
    |bilinearTerm U V X - bilinearPrimeBeta U V X| ≤ bilinearPrimeBetaErrorMass U V X := by
  rw [bilinearTerm_eq_pair_sum]
  unfold bilinearPrimeBeta bilinearPrimeBetaErrorMass
  rw [← sum_sub_distrib]
  have he : (∑ dr ∈ bilinearPairs U V X,
      ((μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2) -
      (μ dr.1 : ℝ) * primeVaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2))) =
      ∑ dr ∈ bilinearPairs U V X,
        (μ dr.1 : ℝ) * (vaughanBeta V dr.2 - primeVaughanBeta V dr.2) *
          vonMangoldt (dr.1 * dr.2 + 2) := by
    apply sum_congr rfl
    intro dr _
    ring
  rw [he]
  exact abs_sum_le_sum_abs _ _

/--
@isnad1 id=le.1h3v.s7.826c83f14b4d from=translated src=- shape=c8ffe264 vocab=fbaa8a3b
-/
theorem bilinearPrimeBetaErrorMass_le_tail (U V X : ℕ) (hX : 1 ≤ X) :
    bilinearPrimeBetaErrorMass U V X ≤
      4 * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 *
        ∑ b ∈ Ioc V (2 * X), nonprimeMangoldt b / b := by
  let L := Real.log (4 * (X : ℝ) + 4)
  let D := fun r => vaughanBeta V r - primeVaughanBeta V r
  have hL : 1 ≤ L := one_le_dispersion_log X
  have hD (r : ℕ) : 0 ≤ D r := sub_nonneg.mpr (primeVaughanBeta_le V r)
  have hsub : bilinearPairs U V X ⊆ positiveHyperbolaPairs (2 * X) := by
    intro dr hdr
    rcases mem_filter.mp hdr with ⟨hdr, _, _, _, hprod⟩
    rcases mem_product.mp hdr with ⟨hd, hr⟩
    exact (mem_positiveHyperbolaPairs_iff _ _).mpr
      ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hr).1, hprod⟩
  have hw (dr : ℕ × ℕ) (hdr : dr ∈ bilinearPairs U V X) :
      |(μ dr.1 : ℝ) * D dr.2 * vonMangoldt (dr.1 * dr.2 + 2)| ≤ L * D dr.2 := by
    have hprod := (mem_filter.mp hdr).2.2.2.2
    have hvm : vonMangoldt (dr.1 * dr.2 + 2) ≤ L :=
      vonMangoldt_le_log.trans (Real.log_le_log (by positivity)
        (by exact_mod_cast (by omega : dr.1 * dr.2 + 2 ≤ 4 * X + 4)))
    have hm : |(μ dr.1 : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := dr.1)
    rw [abs_mul, abs_mul, abs_of_nonneg (hD _), abs_of_nonneg vonMangoldt_nonneg]
    calc
      _ ≤ (1 * D dr.2) * L :=
        mul_le_mul (mul_le_mul_of_nonneg_right hm (hD _)) hvm
          vonMangoldt_nonneg (by simpa using hD dr.2)
      _ = _ := by ring
  have hlog : 1 + Real.log ((2 * X : ℕ) : ℝ) ≤ 2 * L := by
    have hh : Real.log ((2 * X : ℕ) : ℝ) ≤ L :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < 2 * X))
        (by exact_mod_cast (by omega : 2 * X ≤ 4 * X + 4))
    linarith
  have htail := sum_hyperbola_divisor_tail_le (2 * X) V nonprimeMangoldt
    nonprimeMangoldt_nonneg
  simp only [← vaughanBeta_sub_primeVaughanBeta] at htail
  calc
    _ ≤ ∑ dr ∈ bilinearPairs U V X, L * D dr.2 := sum_le_sum hw
    _ ≤ ∑ dr ∈ positiveHyperbolaPairs (2 * X), L * D dr.2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun dr _ _ => mul_nonneg (by linarith) (hD _))
    _ = L * ∑ dr ∈ positiveHyperbolaPairs (2 * X), D dr.2 := by rw [mul_sum]
    _ ≤ L * ((2 * X : ℕ) * (1 + Real.log ((2 * X : ℕ) : ℝ)) *
        ∑ b ∈ Ioc V (2 * X), nonprimeMangoldt b / b) :=
      mul_le_mul_of_nonneg_left htail (by linarith)
    _ ≤ L * ((2 * X : ℕ) * (2 * L) *
        ∑ b ∈ Ioc V (2 * X), nonprimeMangoldt b / b) := by
      gcongr
      exact sum_nonneg fun b _ => div_nonneg (nonprimeMangoldt_nonneg b) (Nat.cast_nonneg _)
    _ = _ := by change _ = 4 * (X : ℝ) * L ^ 2 * _; push_cast; ring

end TwinPrime.Analytic
