/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.Holomorphic
import Tengoku.Seed.Analysis.Analytic.OfScalars
import Tengoku.Seed.Analysis.Calculus.FDeriv.Analytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 复幂级数的收敛圆与逐项求导

给定系数 `a n` 和中心 `c`，本文件将幂级数定义为
`∑ a n * (z-c)^n`，并把它的收敛半径取为相应标量形式幂级数的半径。
我们证明和函数在收敛圆内符合本库教材全纯定义，且导数可逐项计算为
`∑ (n+1) a(n+1) (z-c)^n`。
-/

namespace SandronesLibrary.ComplexAnalysis

open scoped ENNReal

/-- 以 `c` 为中心、系数为 `a` 的复幂级数之和。
> **Entry**: complex-analysis.holomorphic.power-series-/
noncomputable def complexPowerSeries (a : ℕ → ℂ) (c z : ℂ) : ℂ :=
  (FormalMultilinearSeries.ofScalars ℂ a).sum (z - c)

/-- 系数 `a` 的幂级数收敛半径，取值于带无穷的非负实数。
> **Entry**: complex-analysis.holomorphic.power-series-/
noncomputable def powerSeriesRadius (a : ℕ → ℂ) : ℝ≥0∞ :=
  (FormalMultilinearSeries.ofScalars ℂ a).radius

/-- 幂级数的形式导级数之和。后续定理将它展开为教材的逐项公式。
> **Entry**: complex-analysis.holomorphic.power-series-/
noncomputable def termwiseDerivativePowerSeries (a : ℕ → ℂ) (c z : ℂ) : ℂ :=
  (FormalMultilinearSeries.ofScalars ℂ a).derivSeries.sum (z - c) 1

/-- 底层形式幂级数与教材中的显式级数 `∑ aₙ(z-c)ⁿ` 相同。
> **Entry**: complex-analysis.holomorphic.power-series-/
theorem complexPowerSeries_eq_tsum (a : ℕ → ℂ) (c z : ℂ) :
    complexPowerSeries a c z = ∑' n : ℕ, a n * (z - c) ^ n := by
  apply tsum_congr
  intro n
  simp [mul_comm]

/-- 在收敛圆内，形式导级数恰为 `∑ (n+1)aₙ₊₁(z-c)ⁿ`。
> **Entry**: complex-analysis.holomorphic.power-series-/
theorem termwiseDerivativePowerSeries_eq_tsum (a : ℕ → ℂ) (c z : ℂ)
    (hz : z ∈ Metric.eball c (powerSeriesRadius a)) :
    termwiseDerivativePowerSeries a c z =
      ∑' n : ℕ, (n + 1 : ℂ) * a (n + 1) * (z - c) ^ n := by
  let p := FormalMultilinearSeries.ofScalars ℂ a
  have hinside : ‖z - c‖ₑ < (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    simpa only [Metric.mem_eball, edist_eq_enorm_sub, powerSeriesRadius] using hz
  have hR : 0 < p.radius := by
    have h0 : (0 : ℝ≥0∞) ≤ ‖z - c‖ₑ := zero_le
    simpa only [p] using (lt_of_le_of_lt h0 hinside)
  have hy : z - c ∈ Metric.eball 0 p.radius := by
    rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero]
    simpa only [p] using hinside
  have hs : Summable (fun n ↦ p.derivSeries n fun _ ↦ z - c) :=
    ((p.hasFPowerSeriesOnBall hR).fderiv.hasSum hy).summable
  rw [termwiseDerivativePowerSeries, FormalMultilinearSeries.sum]
  change (∑' n, p.derivSeries n (fun _ ↦ z - c)) 1 = _
  change ((ContinuousLinearMap.apply ℂ ℂ) 1) (∑' n, p.derivSeries n (fun _ ↦ z - c)) = _
  rw [ContinuousLinearMap.map_tsum _ hs]
  apply tsum_congr
  intro n
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp [p, FormalMultilinearSeries.derivSeries_coeff_one, mul_comm]

/-- **收敛圆内全纯**：正收敛半径的幂级数在开收敛圆中逐点复可微。
> **Entry**: complex-analysis.holomorphic.power-series-/
theorem powerSeries_holomorphicOn_convergenceDisc (a : ℕ → ℂ) (c : ℂ)
    (hR : 0 < powerSeriesRadius a) :
    HolomorphicOnTextbook (complexPowerSeries a c)
      (Metric.eball c (powerSeriesRadius a)) := by
  rw [holomorphicOnTextbook_iff_differentiableOn Metric.isOpen_eball]
  let p := FormalMultilinearSeries.ofScalars ℂ a
  have hp : HasFPowerSeriesOnBall (fun z ↦ p.sum (z - c)) p c p.radius := by
    have hp₀ := p.hasFPowerSeriesOnBall (by simpa [p, powerSeriesRadius] using hR)
    simpa only [zero_add] using hp₀.comp_sub c
  change DifferentiableOn ℂ (fun z ↦ p.sum (z - c)) (Metric.eball c p.radius)
  exact hp.differentiableOn

/-- **逐项求导**：收敛圆内每点的导数等于形式导级数的和。
> **Entry**: complex-analysis.holomorphic.power-series-/
theorem powerSeries_hasDerivAt_termwise {a : ℕ → ℂ} {c z : ℂ}
    (hz : z ∈ Metric.eball c (powerSeriesRadius a)) :
    HasDerivAt (complexPowerSeries a c) (termwiseDerivativePowerSeries a c z) z := by
  let p := FormalMultilinearSeries.ofScalars ℂ a
  have hinside : ‖z - c‖ₑ < p.radius := by
    simpa only [p, Metric.mem_eball, edist_eq_enorm_sub, powerSeriesRadius] using hz
  have hbase : HasDerivAt p.sum (p.derivSeries.sum (z - c) 1) (z - c) :=
    (p.hasFDerivAt_sum hinside).hasDerivAt
  have hcomp := hbase.comp z ((hasDerivAt_id z).sub_const c)
  convert hcomp using 1
  · rfl
  · rfl
  · funext w
    rfl
  · simp [termwiseDerivativePowerSeries, p]

end SandronesLibrary.ComplexAnalysis
