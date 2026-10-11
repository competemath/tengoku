import Tengoku.OpenaiMath.OAI.Analysis.Steinitz.Prekopa

namespace OAI

/-! Convexity and norm inequalities for Gaussian kernels. -/

section

open MeasureTheory Set Filter
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2

lemma le_of_shifted_pow_le_const_mul_pow {a b K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ n : ℕ, a^(n+2) ≤ K*b^n) : a ≤ b := by
  by_cases hz : a = 0
  · simpa [hz] using hb
  have hp : 0 < a^2 := sq_pos_of_ne_zero hz
  apply le_of_pow_le_const_mul_pow ha hb (C := K/a^2)
  intro n
  rw [div_mul_eq_mul_div, le_div_iff₀ hp, ← pow_add]
  exact h n

section
variable {X : Type*} [MeasurableSpace X]
variable (k : BoundedKernel X) (hs : ∀ x y, k.value (x,y) = k.value (y,x))
variable (μ ν ω : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ω]

include hs in
lemma kernel_norm_logconcave_of_pathMass {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (h : ∀ n, pathMass (μ := μ) k n^(1-t) * pathMass (μ := ν) k n^t ≤ pathMass (μ := ω) k n) :
    ‖kernelOp (μ := μ) k‖^(1-t) * ‖kernelOp (μ := ν) k‖^t ≤ ‖kernelOp (μ := ω) k‖ := by
  let A := k.bound^2 * ‖(oneLp : Lp ℂ 2 μ)‖^2
  let B := k.bound^2 * ‖(oneLp : Lp ℂ 2 ν)‖^2
  let C := ‖(oneLp : Lp ℂ 2 ω)‖^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply le_of_shifted_pow_le_const_mul_pow (by positivity) (norm_nonneg _)
    (K := A^(1-t)*B^t*C)
  intro n
  rw [mul_pow, Real.rpow_pow_comm (norm_nonneg _), Real.rpow_pow_comm (norm_nonneg _)]
  calc
    _ ≤ (A*pathMass (μ := μ) k n)^(1-t) * (B*pathMass (μ := ν) k n)^t := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow (by positivity) (kernel_norm_pow_le_pathMass k hs n) (sub_nonneg.mpr ht.2)
      · exact Real.rpow_le_rpow (by positivity) (kernel_norm_pow_le_pathMass k hs n) ht.1
      · exact Real.rpow_nonneg (by positivity) _
      · exact Real.rpow_nonneg (mul_nonneg hA (pathMass_nonneg k n)) _
    _ = (A^(1-t)*B^t) * (pathMass (μ := μ) k n^(1-t)*pathMass (μ := ν) k n^t) := by
      rw [Real.mul_rpow hA (pathMass_nonneg k n), Real.mul_rpow hB (pathMass_nonneg k n)]
      ring
    _ ≤ (A^(1-t)*B^t)*pathMass (μ := ω) k n :=
      mul_le_mul_of_nonneg_left (h n) (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _))
    _ ≤ (A^(1-t)*B^t)*(C*‖kernelOp (μ := ω) k‖^n) :=
      mul_le_mul_of_nonneg_left (pathMass_le k n) (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _))
    _ = _ := by ring
end

section Haar
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasureSpace E] [BorelSpace E]
variable [(volume : Measure E).IsAddHaarMeasure]
variable (k : BoundedKernel E) (hk : Continuous k.value) (hp : ∀ z, 0 < k.value z)
variable {A B C : Set E} [IsFiniteMeasure (volume.restrict A)]
  [IsFiniteMeasure (volume.restrict B)] [IsFiniteMeasure (volume.restrict C)]

end Haar
end HeatL2

end

section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexInnerProductSpace
namespace GaussianKernel
variable {ι : Type*} [Fintype ι]

end GaussianKernel

end

end OAI
