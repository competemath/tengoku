import Tengoku.Piirrationalitymeasure.Formalization.CoefficientMean
import Tengoku.Piirrationalitymeasure.Formalization.Saddle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The real saddle identities and exact isolating intervals in Appendix A.1. -/

namespace PiIrrationality

def coefficientSaddleNumerator (z : ℝ) : ℝ :=
  -11140 + 11152 * z + 102158 * z ^ 2 + 167160 * z ^ 3 +
    102158 * z ^ 4 + 11152 * z ^ 5 - 11140 * z ^ 6

theorem coefficientMean_numerator {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    (1 - z ^ 2) * PReal z * (coefficientMean z - 5570) =
      coefficientSaddleNumerator z := by
  have hp : 1 + z ≠ 0 := by linarith
  have hm : 1 - z ≠ 0 := by linarith
  have hP := (PReal_strictPositive z hz0).ne'
  unfold coefficientMean
  field_simp [hp, hm, hP]
  dsimp [PReal, PRealPrime, coefficientSaddleNumerator]
  ring

theorem coefficientSaddle_cubic_identity {w : ℝ} (hw : w + 1 ≠ 0) :
    (w + 1) ^ 6 * coefficientSaddleNumerator ((w - 1) / (w + 1)) =
      4 / 625 * stationaryCubic (25 * w ^ 2) := by
  unfold coefficientSaddleNumerator stationaryCubic
  field_simp
  ring

theorem coefficientSaddleNumerator_eq_zero :
    coefficientSaddleNumerator coefficientSaddle = 0 := by
  rw [← coefficientMean_numerator coefficientSaddle_mem.1.le coefficientSaddle_mem.2,
    coefficientSaddle_mean, sub_self, mul_zero]

theorem coefficientSaddle_gt_of_numerator_neg {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hN : coefficientSaddleNumerator z < 0) : z < coefficientSaddle := by
  have hd : 0 < (1 - z ^ 2) * PReal z :=
    mul_pos (by nlinarith) (PReal_strictPositive z hz0)
  have hm : coefficientMean z < 5570 := by
    have he := coefficientMean_numerator hz0 hz1
    nlinarith
  by_contra h
  have hle := coefficientMean_strictMono.monotoneOn
    ⟨coefficientSaddle_mem.1.le, coefficientSaddle_mem.2⟩ ⟨hz0, hz1⟩ (le_of_not_gt h)
  rw [coefficientSaddle_mean] at hle
  linarith

theorem coefficientSaddle_lt_of_numerator_pos {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hN : 0 < coefficientSaddleNumerator z) : coefficientSaddle < z := by
  have hd : 0 < (1 - z ^ 2) * PReal z :=
    mul_pos (by nlinarith) (PReal_strictPositive z hz0)
  have hm : 5570 < coefficientMean z := by
    have he := coefficientMean_numerator hz0 hz1
    nlinarith
  by_contra h
  have hle := coefficientMean_strictMono.monotoneOn ⟨hz0, hz1⟩
    ⟨coefficientSaddle_mem.1.le, coefficientSaddle_mem.2⟩ (le_of_not_gt h)
  rw [coefficientSaddle_mean] at hle
  linarith

noncomputable def coefficientSaddleLower : ℝ :=
  23918337643845311771849563937315852029007245250806 / 10 ^ 50

noncomputable def coefficientSaddleUpper : ℝ :=
  23918337643845311771849563937315852029007245250807 / 10 ^ 50

theorem coefficientSaddle_fine_bounds :
    coefficientSaddleLower < coefficientSaddle ∧ coefficientSaddle < coefficientSaddleUpper := by
  constructor
  · apply coefficientSaddle_gt_of_numerator_neg
      (by norm_num [coefficientSaddleLower]) (by norm_num [coefficientSaddleLower])
    norm_num [coefficientSaddleNumerator, coefficientSaddleLower]
  · apply coefficientSaddle_lt_of_numerator_pos
      (by norm_num [coefficientSaddleUpper]) (by norm_num [coefficientSaddleUpper])
    norm_num [coefficientSaddleNumerator, coefficientSaddleUpper]

theorem coefficientSaddle_coarse_bounds :
    (239 : ℝ) / 1000 < coefficientSaddle ∧ coefficientSaddle < 6 / 25 := by
  have h := coefficientSaddle_fine_bounds
  norm_num [coefficientSaddleLower, coefficientSaddleUpper] at h
  constructor <;> linarith

theorem coefficientSaddle_real_root :
    stationaryRoot = 25 * (1 + coefficientSaddle) ^ 2 / (1 - coefficientSaddle) ^ 2 := by
  let z := coefficientSaddle
  let w := (1 + z) / (1 - z)
  have hz0 : 0 < z := coefficientSaddle_mem.1
  have hz1 : z < 1 := coefficientSaddle_mem.2
  have hden : 0 < 1 - z := by linarith
  have hw0 : 0 < w := div_pos (by linarith) hden
  have hw1 : w + 1 ≠ 0 := by linarith
  have he : (w - 1) / (w + 1) = z := by
    dsimp [w]
    field_simp
    ring
  have hroot : stationaryCubic (25 * w ^ 2) = 0 := by
    have h := coefficientSaddle_cubic_identity hw1
    rw [he, coefficientSaddleNumerator_eq_zero, mul_zero] at h
    linarith
  have hb := coefficientSaddle_coarse_bounds
  have hwL : (1239 : ℝ) / 761 < w := by
    dsimp [w]
    apply (div_lt_div_iff₀ (by norm_num) hden).mpr
    linarith [hb.1]
  have hwU : w < (31 : ℝ) / 19 := by
    dsimp [w]
    apply (div_lt_div_iff₀ hden (by norm_num)).mpr
    linarith [hb.2]
  have hmem : 25 * w ^ 2 ∈ Set.Icc (66 : ℝ) 67 := by
    constructor <;> nlinarith [sq_nonneg (w - 1239 / 761),
      mul_nonneg (sub_nonneg.mpr hwL.le) (show 0 ≤ w + 1239 / 761 by positivity),
      mul_nonneg (sub_nonneg.mpr hwU.le) (show 0 ≤ 31 / 19 + w by positivity)]
  have hy := stationaryCubic_strictMono.injOn stationaryRoot_mem hmem
    (stationaryRoot_eq_zero.trans hroot.symm)
  simpa only [w, div_pow, mul_div_assoc] using hy

noncomputable def stationaryRootFineLower : ℝ :=
  6632101738059856717221773124052531930114787749744963 / 10 ^ 50

noncomputable def stationaryRootFineUpper : ℝ :=
  6632101738059856717221773124052531930114787749744964 / 10 ^ 50

theorem stationaryRoot_fine_bounds :
    stationaryRootFineLower < stationaryRoot ∧ stationaryRoot < stationaryRootFineUpper := by
  have hL : stationaryRootFineLower ∈ Set.Icc (66 : ℝ) 67 := by
    norm_num [stationaryRootFineLower, Set.mem_Icc]
  have hU : stationaryRootFineUpper ∈ Set.Icc (66 : ℝ) 67 := by
    norm_num [stationaryRootFineUpper, Set.mem_Icc]
  have hpL : stationaryCubic stationaryRootFineLower < 0 := by
    norm_num [stationaryCubic, stationaryRootFineLower]
  have hpU : 0 < stationaryCubic stationaryRootFineUpper := by
    norm_num [stationaryCubic, stationaryRootFineUpper]
  constructor
  · by_contra h
    have hm := stationaryCubic_strictMono.monotoneOn stationaryRoot_mem hL (le_of_not_gt h)
    rw [stationaryRoot_eq_zero] at hm
    linarith
  · by_contra h
    have hm := stationaryCubic_strictMono.monotoneOn hU stationaryRoot_mem (le_of_not_gt h)
    rw [stationaryRoot_eq_zero] at hm
    linarith

end PiIrrationality
