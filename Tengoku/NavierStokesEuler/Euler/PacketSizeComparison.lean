import Tengoku.NavierStokesEuler.Euler.PacketActualFrameEstimates
import Tengoku.NavierStokesEuler.Euler.PacketIdealSize

/-! Uniform comparison between actual and ideal physical primary sizes. -/

noncomputable section

namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketRay EulerPacketFrameStability EulerPacketFrameQuantitative
  InnerProductSpace

theorem scalar_size_comparison {s₀ D D₀ E V Z : ℝ}
    (hs₀ : 0 ≤ s₀) (hD₀ : 1 ≤ D₀) (hD : |D-D₀| ≤ 1/2)
    (hElo : 1 ≤ E) (hEup : E ≤ 2) (hZ : 0 < Z) (hV : |V-Z| ≤ Z/2) :
    s₀*Real.sqrt D₀*Z/4 ≤ s₀*Real.sqrt D*V*Real.sqrt E ∧
      s₀*Real.sqrt D*V*Real.sqrt E ≤ 8*s₀*Real.sqrt D₀*Z := by
  have hd := abs_le.mp hD
  have hv := abs_le.mp hV
  have hDp : 0 < D := by linarith only [hd.1, hD₀]
  have hD₀p : 0 ≤ D₀ := by linarith only [hD₀]
  have hVlo : Z/2 ≤ V := by linarith only [hv.1]
  have hVup : V ≤ 2*Z := by linarith only [hv.2, hZ]
  have hVp : 0 ≤ V := by linarith only [hVlo, hZ]
  have hrootD : Real.sqrt D₀/2 ≤ Real.sqrt D := by
    have hh : Real.sqrt D₀ ≤ 2*Real.sqrt D := Real.sqrt_le_iff.mpr
      ⟨by positivity, by nlinarith only [Real.sq_sqrt hDp.le, hd.1, hD₀]⟩
    linarith only [hh]
  have hrootD' : Real.sqrt D ≤ 2*Real.sqrt D₀ := Real.sqrt_le_iff.mpr
    ⟨by positivity, by nlinarith only [Real.sq_sqrt hD₀p, hd.2, hD₀]⟩
  have hrootE : 1 ≤ Real.sqrt E := Real.one_le_sqrt.mpr hElo
  have hrootE' : Real.sqrt E ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith only [hEup]⟩
  have hlower := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hrootD hs₀) hVlo (by positivity) (by positivity))
    hrootE (by norm_num : (0:ℝ) ≤ 1) (by positivity)
  have hupper := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hrootD' hs₀) hVup hVp (by positivity))
    hrootE' (Real.sqrt_nonneg E) (by positivity)
  constructor <;> nlinarith only [hlower, hupper]

end EulerPacketMovingFrame
