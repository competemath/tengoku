import Tengoku.Twinprime.TwinPrime.Analytic.MixedCorrelation
import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusTotient
import Tengoku.Twinprime.TwinPrime.Analytic.PartialSummation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The logarithmic Type I correction

The correction is reindexed by moduli before using distribution estimates.
Even moduli are bounded separately by their prime-power mass.
-/

noncomputable section

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

theorem truncatedMoebiusSum_eq_moduli (U n : ℕ) (hn : 0 < n) :
    truncatedMoebiusSum U n = ∑ d ∈ range (U + 1) with d ∣ n, (μ d : ℝ) := by
  unfold truncatedMoebiusSum
  congr 1
  ext d
  simp only [mem_filter, Nat.mem_divisors, mem_range]
  omega

theorem logarithmicCorrection_eq_progressions (U X : ℕ) :
    logarithmicCorrection U X = ∑ q ∈ range (U + 1), (μ q : ℝ) *
      ∑ n ∈ Ioc X (2 * X) with q ∣ n,
        Real.log ((n : ℝ) / U) * vonMangoldt (n + 2) := by
  unfold logarithmicCorrection
  simp_rw [sum_filter, mul_sum]
  calc
    _ = ∑ n ∈ Ioc X (2 * X), ∑ q ∈ range (U + 1),
        if q ∣ n then (μ q : ℝ) * Real.log ((n : ℝ) / U) * vonMangoldt (n + 2)
          else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [truncatedMoebiusSum_eq_moduli U n (by have := (mem_Ioc.mp hn).1; omega),
        sum_filter, mul_sum, mul_sum]
      apply sum_congr rfl
      intro q _
      split_ifs <;> simp [mul_assoc, mul_comm]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro q _
      apply sum_congr rfl
      intro n _
      split_ifs <;> simp [mul_assoc]

theorem log_ratio_nonneg {U X n : ℕ} (hU : 0 < U) (hUX : U ≤ X)
    (hn : n ∈ Ioc X (2 * X)) : 0 ≤ Real.log ((n : ℝ) / U) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (by exact_mod_cast hU : (0 : ℝ) < U)]
  simp only [one_mul]
  exact_mod_cast (show U ≤ n by have := mem_Ioc.mp hn; omega)

theorem log_ratio_le_dyadic {U X n : ℕ} (hU : 0 < U)
    (hn : n ∈ Ioc X (2 * X)) :
    Real.log ((n : ℝ) / U) ≤ Real.log (2 * X + 2) := by
  have hUp : (0 : ℝ) < U := by exact_mod_cast hU
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := mem_Ioc.mp hn; omega)
  apply Real.log_le_log (div_pos hnp hUp)
  apply (div_le_self (le_of_lt hnp) hU1).trans
  exact_mod_cast (show n ≤ 2 * X + 2 by have := mem_Ioc.mp hn; omega)

theorem even_logarithmicProgression_le (U X q : ℕ) (hU : 0 < U) (hUX : U ≤ X)
    (hq : Even q) :
    |∑ n ∈ Ioc X (2 * X) with q ∣ n,
      Real.log ((n : ℝ) / U) * vonMangoldt (n + 2)| ≤
        Real.log (2 * X + 2) * evenProgressionBound X := by
  rw [abs_of_nonneg (sum_nonneg (fun n hn => mul_nonneg
    (log_ratio_nonneg hU hUX (mem_filter.mp hn).1) vonMangoldt_nonneg))]
  calc
    _ ≤ ∑ n ∈ Ioc X (2 * X) with q ∣ n,
        Real.log (2 * X + 2) * vonMangoldt (n + 2) := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right (log_ratio_le_dyadic hU (mem_filter.mp hn).1)
        vonMangoldt_nonneg
    _ = Real.log (2 * X + 2) *
        ∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (even_shiftedProgression_le X q hq)
      (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith))

/-- Cumulative shifted errors on every intermediate integer endpoint.-/
theorem shiftedProgression_interval_sub_main_eq_errors (a b q : ℕ) (hab : a ≤ b) :
    (∑ n ∈ Ioc a b with q ∣ n, vonMangoldt (n + 2)) -
      ((b : ℝ) - a) / Nat.totient q =
        progressionError (b + 2) q 2 - progressionError (a + 2) q 2 := by
  have hs : (∑ n ∈ Ioc a b with q ∣ n, vonMangoldt (n + 2)) =
      progressionPsi (b + 2) q 2 - progressionPsi (a + 2) q 2 := by
    rw [progressionPsi_sub _ _ _ _ (by omega)]
    apply sum_bij (fun n _ => n + 2)
    · intro n hn
      obtain ⟨hnI, hqn⟩ := mem_filter.mp hn
      apply mem_filter.mpr
      refine ⟨?_, Nat.add_modEq_right_iff.mpr hqn⟩
      simp only [mem_Ioc] at hnI ⊢
      omega
    · intro n _ m _ h
      omega
    · intro m hm
      obtain ⟨hmI, hmcong⟩ := mem_filter.mp hm
      have hm := mem_Ioc.mp hmI
      have heq : m - 2 + 2 = m := by omega
      refine ⟨m - 2, mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩, heq⟩
      have hcong : Nat.ModEq q (m - 2 + 2) 2 := by simpa only [heq] using hmcong
      exact Nat.add_modEq_right_iff.mp hcong
    · intro n _
      rfl
  rw [hs]
  unfold progressionError
  push_cast
  ring

/-- The unweighted integer main mass arising in partial summation.-/
def logarithmicMass (U X : ℕ) : ℝ :=
  ∑ n ∈ Ioc X (2 * X), Real.log ((n : ℝ) / U)

theorem logarithmicMass_nonneg (U X : ℕ) (hU : 0 < U) (hUX : U ≤ X) :
    0 ≤ logarithmicMass U X :=
  sum_nonneg (fun _ hn => log_ratio_nonneg hU hUX hn)

theorem logarithmicMass_le (U X : ℕ) (hU : 0 < U) :
    logarithmicMass U X ≤ X * Real.log (2 * X + 2) := by
  calc
    _ ≤ ∑ n ∈ Ioc X (2 * X), Real.log (2 * X + 2) :=
      sum_le_sum (fun _ hn => log_ratio_le_dyadic hU hn)
    _ = _ := by simp [Nat.card_Ioc, show 2 * X - X = X by omega]

theorem oddCutoff_eq_range_filter (U : ℕ) :
    oddCutoff U = (range (U + 1)).filter Odd := by
  ext q
  simp only [oddCutoff, mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨_, hq⟩, ho⟩
    exact ⟨by omega, ho⟩
  · rintro ⟨hq, ho⟩
    exact ⟨⟨ho.pos, by omega⟩, ho⟩

/-- A finite assembly lemma retaining a separate reduced-residue estimate.-/
theorem logarithmicCorrection_error_le_of_progressions (U X : ℕ)
    (hU : 0 < U) (hUX : U ≤ X)
    (hodd : ∀ q, Odd q →
      |(∑ n ∈ Ioc X (2 * X) with q ∣ n,
        Real.log ((n : ℝ) / U) * vonMangoldt (n + 2)) -
          logarithmicMass U X / Nat.totient q| ≤
            4 * Real.log (2 * X + 2) * progressionMaxError (2 * X + 2) q) :
    |logarithmicCorrection U X - oddMoebiusTotientSum U * logarithmicMass U X| ≤
      4 * Real.log (2 * X + 2) * ∑ q ∈ Icc 1 U, progressionMaxError (2 * X + 2) q +
        (U + 1 : ℝ) * Real.log (2 * X + 2) * evenProgressionBound X := by
  let f := fun q => ∑ n ∈ Ioc X (2 * X) with q ∣ n,
    Real.log ((n : ℝ) / U) * vonMangoldt (n + 2)
  have hL : 0 ≤ Real.log (2 * X + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  have hmu (q : ℕ) : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := q))
  have hdecomp : logarithmicCorrection U X =
      (∑ q ∈ oddCutoff U, (μ q : ℝ) * f q) +
        ∑ q ∈ range (U + 1) with Even q, (μ q : ℝ) * f q := by
    rw [logarithmicCorrection_eq_progressions, oddCutoff_eq_range_filter]
    simpa only [Nat.not_odd_iff_even] using
      (sum_filter_add_sum_filter_not (range (U + 1)) Odd (fun q => (μ q : ℝ) * f q)).symm
  have ho : |(∑ q ∈ oddCutoff U, (μ q : ℝ) * f q) -
      oddMoebiusTotientSum U * logarithmicMass U X| ≤
        4 * Real.log (2 * X + 2) * ∑ q ∈ Icc 1 U, progressionMaxError (2 * X + 2) q := by
    unfold oddMoebiusTotientSum
    rw [sum_mul, ← sum_sub_distrib]
    calc
      _ ≤ ∑ q ∈ oddCutoff U, |(μ q : ℝ) * f q -
          (μ q : ℝ) / Nat.totient q * logarithmicMass U X| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ oddCutoff U, 4 * Real.log (2 * X + 2) * progressionMaxError (2 * X + 2) q := by
        apply sum_le_sum
        intro q hq
        have heq : (μ q : ℝ) * f q - (μ q : ℝ) / Nat.totient q * logarithmicMass U X =
            (μ q : ℝ) * (f q - logarithmicMass U X / Nat.totient q) := by ring
        rw [heq, abs_mul]
        calc
          _ ≤ 1 * |f q - logarithmicMass U X / Nat.totient q| :=
            mul_le_mul_of_nonneg_right (hmu q) (abs_nonneg _)
          _ ≤ _ := by simpa only [one_mul] using hodd q (mem_filter.mp hq).2
      _ ≤ ∑ q ∈ Icc 1 U, 4 * Real.log (2 * X + 2) * progressionMaxError (2 * X + 2) q :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ =>
          mul_nonneg (by positivity) (progressionMaxError_nonneg _ q))
      _ = _ := (mul_sum ..).symm
  have he : |∑ q ∈ range (U + 1) with Even q, (μ q : ℝ) * f q| ≤
      (U + 1 : ℝ) * Real.log (2 * X + 2) * evenProgressionBound X := by
    calc
      _ ≤ ∑ q ∈ range (U + 1) with Even q, |(μ q : ℝ) * f q| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ range (U + 1) with Even q,
          Real.log (2 * X + 2) * evenProgressionBound X := by
        apply sum_le_sum
        intro q hq
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right (hmu q) (abs_nonneg _)).trans
          (by simpa only [one_mul] using
            (even_logarithmicProgression_le U X q hU hUX (mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ range (U + 1), Real.log (2 * X + 2) * evenProgressionBound X :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ =>
          mul_nonneg hL (evenProgressionBound_nonneg X))
      _ = _ := by simp; ring
  rw [hdecomp, add_sub_right_comm]
  exact (abs_add_le _ _).trans (add_le_add ho he)

end TwinPrime.Analytic
