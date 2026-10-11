import Tengoku.OpenaiMath.OAI.InformationTheory.BooleanNoise.Basic
import Tengoku

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

def lambda (z : ℝ) : ℝ := if z = 0 then 1 else -Real.log (1 - z) / z

@[simp] theorem lambda_zero : lambda 0 = 1 := by simp [lambda]

theorem lambda_of_ne_zero {z : ℝ} (hz : z ≠ 0) :
    lambda z = -Real.log (1 - z) / z := by simp [lambda, hz]

theorem mul_lambda (z : ℝ) : z * lambda z = -Real.log (1 - z) := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [lambda_of_ne_zero hz]
    field_simp

end LeanBlast.CourtadeKumar

end

end OAI
