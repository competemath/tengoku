import Tengoku.OpenaiMath.OAI.InformationTheory.BooleanNoise.EntropyScalars
import Tengoku

namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

def psiCoeff (k : ℕ) : ℝ := 1 / ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1))

theorem psiCoeff_pos (k : ℕ) : 0 < psiCoeff k := by unfold psiCoeff; positivity

theorem psiCoeff_nonneg (k : ℕ) : 0 ≤ psiCoeff k := (psiCoeff_pos k).le

@[simp] theorem psiCoeff_zero : psiCoeff 0 = 1 / 2 := by norm_num [psiCoeff]

theorem hasSum_artanh {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => v ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) (Real.artanh v) := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

theorem psi_eq_mul_artanh_add_log {v : ℝ} (hv : |v| < 1) :
    psi v = v * Real.artanh v + 1 / 2 * Real.log (1 - v ^ 2) := by
  have hp : 1 + v ≠ 0 := by linarith [(abs_lt.mp hv).1]
  have hm : 1 - v ≠ 0 := by linarith [(abs_lt.mp hv).2]
  have hl : Real.log (1 - v ^ 2) = Real.log (1 + v) + Real.log (1 - v) := by
    rw [← Real.log_mul hp hm]
    congr 1
    ring
  rw [artanh_eq_log_sub (abs_lt.mp hv), hl]
  unfold psi
  ring

theorem summable_psiCoeff : Summable psiCoeff := by
  have h : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  apply Summable.of_nonneg_of_le psiCoeff_nonneg ?_ h
  intro k
  unfold psiCoeff
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg (k : ℝ), Nat.cast_nonneg (α := ℝ) k]

end LeanBlast.CourtadeKumar

end

end OAI
