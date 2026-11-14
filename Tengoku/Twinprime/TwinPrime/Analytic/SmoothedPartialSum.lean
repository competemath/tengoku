import Tengoku.Seed.Algebra.BigOperators.Intervals
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Algebra.Order.Floor.Ring
import Tengoku.Seed.NumberTheory.ArithmeticFunction.VonMangoldt
import Tengoku.Seed.NumberTheory.DirichletCharacter.Bounds
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact finite unsmoothing

The integrated weight `x - n` has forward difference one at every old
index and a weight in `[0,1]` on the newly included short interval.
All statements concern finite sums and make no distribution assumption.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- The integrated first-order smoothing of a complex coefficient sequence.-/
def integratedWeightedPartialSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((x : ℂ) - (n : ℂ))

/-- The normalized weight, with the usual totalized division at zero.-/
def weightedPartialSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, a n * (1 - (n : ℂ) / (x : ℂ))

theorem integratedWeightedPartialSum_eq_mul_weightedPartialSum
    (a : ℕ → ℂ) (x : ℝ) (hx : x ≠ 0) :
    integratedWeightedPartialSum a x = (x : ℂ) * weightedPartialSum a x := by
  unfold integratedWeightedPartialSum weightedPartialSum
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  field_simp

private theorem prefix_union_shortInterval (x h : ℝ) (hh : 0 ≤ h) :
    Icc 1 ⌊x + h⌋₊ = Icc 1 ⌊x⌋₊ ∪ Ioc ⌊x⌋₊ ⌊x + h⌋₊ := by
  have hfloor := Nat.floor_mono (show x ≤ x + h by linarith)
  ext n
  simp only [mem_Icc, mem_union, mem_Ioc]
  omega

private theorem prefix_disjoint_shortInterval (x h : ℝ) :
    Disjoint (Icc 1 ⌊x⌋₊) (Ioc ⌊x⌋₊ ⌊x + h⌋₊) := by
  apply disjoint_left.mpr
  intro n hn hm
  simp only [mem_Icc, mem_Ioc] at hn hm
  omega

/-- The old indices contribute exactly `h` times their unweighted sum.-/
theorem integratedWeightedPartialSum_add_sub (a : ℕ → ℂ) (x h : ℝ)
    (hh : 0 ≤ h) :
    integratedWeightedPartialSum a (x + h) - integratedWeightedPartialSum a x =
      (h : ℂ) * (∑ n ∈ Icc 1 ⌊x⌋₊, a n) +
        ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - (n : ℂ)) := by
  unfold integratedWeightedPartialSum
  rw [prefix_union_shortInterval x h hh, sum_union (prefix_disjoint_shortInterval x h),
    add_sub_right_comm, ← sum_sub_distrib, mul_sum]
  congr 1
  apply sum_congr rfl
  intro n _
  push_cast
  ring

/-- Exact unsmoothing, retaining the weight on each new short-interval index.-/
theorem integratedWeightedPartialSum_forward_difference (a : ℕ → ℂ) (x h : ℝ)
    (hh : 0 < h) :
    (integratedWeightedPartialSum a (x + h) - integratedWeightedPartialSum a x) /
        (h : ℂ) =
      (∑ n ∈ Icc 1 ⌊x⌋₊, a n) +
        ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊,
          a n * ((((x + h - n) / h : ℝ) : ℂ)) := by
  rw [integratedWeightedPartialSum_add_sub a x h hh.le, add_div, sum_div]
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  rw [mul_div_cancel_left₀ _ hh']
  congr 1
  apply sum_congr rfl
  intro n _
  push_cast
  ring

theorem shortInterval_weight_nonneg_le_one (x h : ℝ) (hx : 0 ≤ x) (hh : 0 < h)
    (n : ℕ) (hn : n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊) :
    0 ≤ (x + h - n) / h ∧ (x + h - n) / h ≤ 1 := by
  obtain ⟨hnx, hnh⟩ := mem_Ioc.mp hn
  have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hnx
  have hnxh : (n : ℝ) ≤ x + h :=
    (Nat.cast_le.mpr hnh).trans (Nat.floor_le (by linarith))
  constructor
  · exact div_nonneg (by linarith) hh.le
  · apply (div_le_one hh).mpr
    linarith

/-- The smoothing error is bounded by the coefficient mass on `(x,x+h]`.-/
theorem norm_integratedWeightedPartialSum_forward_difference_sub_sum_le
    (a : ℕ → ℂ) (x h : ℝ) (hx : 0 ≤ x) (hh : 0 < h) :
    ‖(integratedWeightedPartialSum a (x + h) - integratedWeightedPartialSum a x) /
        (h : ℂ) - (∑ n ∈ Icc 1 ⌊x⌋₊, a n)‖ ≤
      ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a n‖ := by
  rw [integratedWeightedPartialSum_forward_difference a x h hh, add_sub_cancel_left]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  obtain ⟨hw0, hw1⟩ := shortInterval_weight_nonneg_le_one x h hx hh n hn
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
  exact mul_le_of_le_one_right (norm_nonneg _) hw1

theorem card_shortInterval_le (x h : ℝ) (hx : 0 ≤ x) (hh : 0 ≤ h) :
    ((Ioc ⌊x⌋₊ ⌊x + h⌋₊).card : ℝ) ≤ h + 1 := by
  have hfloor := Nat.floor_mono (show x ≤ x + h by linarith)
  rw [Nat.card_Ioc, Nat.cast_sub hfloor]
  have htop := Nat.floor_le (show 0 ≤ x + h by linarith)
  have hbottom := Nat.lt_floor_add_one x
  linarith

/-- A constant bound on the new coefficients costs at most `h+1` terms.-/
theorem norm_integratedWeightedPartialSum_forward_difference_sub_sum_le_const
    (a : ℕ → ℂ) (x h B : ℝ) (hx : 0 ≤ x) (hh : 0 < h) (hB : 0 ≤ B)
    (ha : ∀ n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a n‖ ≤ B) :
    ‖(integratedWeightedPartialSum a (x + h) - integratedWeightedPartialSum a x) /
        (h : ℂ) - (∑ n ∈ Icc 1 ⌊x⌋₊, a n)‖ ≤ (h + 1) * B := by
  apply (norm_integratedWeightedPartialSum_forward_difference_sub_sum_le a x h hx hh).trans
  calc
    _ ≤ ∑ _ ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊, B := sum_le_sum ha
    _ = ((Ioc ⌊x⌋₊ ⌊x + h⌋₊).card : ℝ) * B := by simp
    _ ≤ (h + 1) * B := mul_le_mul_of_nonneg_right (card_shortInterval_le x h hx hh.le) hB

/-- The elementary unsmoothing budget for any Mangoldt character twist.-/
theorem norm_mangoldt_character_forward_difference_sub_sum_le {q : ℕ}
    (χ : DirichletCharacter ℂ q) (x h : ℝ) (hx : 0 ≤ x) (hh : 0 < h)
    (hxh : 1 ≤ x + h) :
    ‖(integratedWeightedPartialSum (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ n)
          (x + h) -
        integratedWeightedPartialSum (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) x) /
        (h : ℂ) - (∑ n ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n)‖ ≤
      (h + 1) * Real.log (x + h) := by
  apply norm_integratedWeightedPartialSum_forward_difference_sub_sum_le_const
    _ x h (Real.log (x + h)) hx hh (Real.log_nonneg hxh)
  intro n hn
  obtain ⟨hnx, hnh⟩ := mem_Ioc.mp hn
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hnx
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnxh : (n : ℝ) ≤ x + h :=
    (Nat.cast_le.mpr hnh).trans (Nat.floor_le (by linarith))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)).trans
    (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnr hnxh))

end TwinPrime.Analytic
