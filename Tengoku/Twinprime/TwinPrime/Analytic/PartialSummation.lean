import Tengoku.Seed.Algebra.BigOperators.Module
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite discrete partial summation

The lower endpoint is excluded and the upper endpoint included. Cumulative
sums always start at the same lower endpoint. All identities and estimates
are finite; no integral or distribution theorem is used.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- Discrete Abel summation with cumulative sums based at `a`. Including the
index `a` in the variation sum is harmless because its cumulative sum is zero.-/
theorem discrete_abel_Ioc (a b : ℕ) (hab : a ≤ b) (w e : ℕ → ℝ) :
    (∑ n ∈ Ioc a b, w n * e n) =
      w b * (∑ n ∈ Ioc a b, e n) -
      ∑ t ∈ Ico a b, (w (t + 1) - w t) * (∑ n ∈ Ioc a t, e n) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ioc_succ_top hab (fun n => w n * e n),
      sum_Ioc_succ_top hab e,
      sum_Ico_succ_top hab (fun t => (w (t + 1) - w t) * (∑ n ∈ Ioc a t, e n)), ih]
    ring

/-- Bounded cumulative errors control a weighted sum by the endpoint weight
and its full finite variation. The weights may have either sign.-/
theorem abs_sum_Ioc_mul_le_total_variation (a b : ℕ) (hab : a ≤ b)
    (w e : ℕ → ℝ) (M : ℝ)
    (hE : ∀ t ∈ Icc a b, |∑ n ∈ Ioc a t, e n| ≤ M) :
    |∑ n ∈ Ioc a b, w n * e n| ≤
      M * (|w b| + ∑ t ∈ Ico a b, |w (t + 1) - w t|) := by
  rw [discrete_abel_Ioc a b hab w e]
  calc
    _ ≤ |w b * (∑ n ∈ Ioc a b, e n)| +
        |∑ t ∈ Ico a b, (w (t + 1) - w t) * (∑ n ∈ Ioc a t, e n)| :=
      abs_sub _ _
    _ ≤ |w b| * M + ∑ t ∈ Ico a b, |w (t + 1) - w t| * M := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hE b (mem_Icc.mpr ⟨hab, le_rfl⟩)) (abs_nonneg _)
      · apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro t ht
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (hE t (mem_Icc.mpr ⟨(mem_Ico.mp ht).1, (mem_Ico.mp ht).2.le⟩))
          (abs_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

/-- Nonnegative nondecreasing weights cost at most twice their final value.-/
theorem abs_sum_Ioc_mul_le_of_partial_sums (a b : ℕ) (hab : a ≤ b)
    (w e : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hw0 : 0 ≤ w a)
    (hw : MonotoneOn w (Set.Icc a b))
    (hE : ∀ t ∈ Icc a b, |∑ n ∈ Ioc a t, e n| ≤ M) :
    |∑ n ∈ Ioc a b, w n * e n| ≤ 2 * M * w b := by
  have hwb : 0 ≤ w b := hw0.trans (hw ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  have hvar : (∑ t ∈ Ico a b, |w (t + 1) - w t|) = w b - w a := by
    calc
      _ = ∑ t ∈ Ico a b, (w (t + 1) - w t) := by
        apply sum_congr rfl
        intro t ht
        obtain ⟨hat, htb⟩ := mem_Ico.mp ht
        apply abs_of_nonneg
        apply sub_nonneg.mpr
        exact hw ⟨hat, htb.le⟩ ⟨by omega, by omega⟩ (Nat.le_succ t)
      _ = _ := sum_Ico_sub w hab
  apply (abs_sum_Ioc_mul_le_total_variation a b hab w e M hE).trans
  rw [abs_of_nonneg hwb, hvar]
  nlinarith

/-- Logarithmic weights used by the Type I correction fit the monotone-weight
bound as soon as the positive cutoff is at most the lower interval endpoint.-/
theorem abs_sum_Ioc_log_mul_le_of_partial_sums (a b U : ℕ) (hab : a ≤ b)
    (hU : 0 < U) (hUa : U ≤ a) (e : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hE : ∀ t ∈ Icc a b, |∑ n ∈ Ioc a t, e n| ≤ M) :
    |∑ n ∈ Ioc a b, Real.log ((n : ℝ) / U) * e n| ≤
      2 * M * Real.log ((b : ℝ) / U) := by
  have hUr : (0 : ℝ) < U := by exact_mod_cast hU
  apply abs_sum_Ioc_mul_le_of_partial_sums a b hab
    (fun n => Real.log ((n : ℝ) / U)) e M hM _ _ hE
  · apply Real.log_nonneg
    exact (one_le_div hUr).mpr (by exact_mod_cast hUa)
  · intro n hn m hm hnm
    apply Real.log_le_log
    · apply div_pos _ hUr
      exact_mod_cast (hU.trans_le (hUa.trans hn.1))
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hnm) hUr.le

end TwinPrime.Analytic
