import Tengoku
import Tengoku.Piirrationalitymeasure.Formalization.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Exact root-isolation certificates for the stationary cubic in Appendix A.1.
-/

namespace PiIrrationality

def stationaryCubic (y : ℝ) : ℝ :=
  3715 * y^3 - 232119 * y^2 - 928475 * y - 1160625

theorem stationaryCubic_at_66 : stationaryCubic 66 < 0 := by
  norm_num [stationaryCubic]

theorem stationaryCubic_at_67 : 0 < stationaryCubic 67 := by
  norm_num [stationaryCubic]

theorem stationaryCubic_strictMono :
    StrictMonoOn stationaryCubic (Set.Icc (66 : ℝ) 67) := by
  intro x hx y hy hxy
  unfold stationaryCubic
  have hfac :
      (3715 * y^3 - 232119 * y^2 - 928475 * y - 1160625) -
        (3715 * x^3 - 232119 * x^2 - 928475 * x - 1160625) =
      (y - x) * (3715 * (y^2 + y*x + x^2) - 232119 * (y + x) - 928475) := by
    ring
  have hbracket : 0 < 3715 * (y^2 + y*x + x^2) - 232119 * (y + x) - 928475 := by
    have hxy66 : 0 ≤ (x - 66) * (y - 66) :=
      mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hy.1)
    have hx66 : 0 ≤ (x - 66) * (x + 66) :=
      mul_nonneg (sub_nonneg.mpr hx.1) (by linarith [hx.1])
    have hy66 : 0 ≤ (y - 66) * (y + 66) :=
      mul_nonneg (sub_nonneg.mpr hy.1) (by linarith [hy.1])
    nlinarith
  have hdiff : 0 <
      (3715 * y^3 - 232119 * y^2 - 928475 * y - 1160625) -
        (3715 * x^3 - 232119 * x^2 - 928475 * x - 1160625) := by
    rw [hfac]
    exact mul_pos (sub_pos.mpr hxy) hbracket
  linarith

theorem stationaryCubic_unique_root :
    ∃! y : ℝ, y ∈ Set.Icc 66 67 ∧ stationaryCubic y = 0 := by
  have hcont : ContinuousOn stationaryCubic (Set.Icc (66 : ℝ) 67) := by
    unfold stationaryCubic
    fun_prop
  have hzero : (0 : ℝ) ∈ Set.Icc (stationaryCubic 66) (stationaryCubic 67) := by
    constructor <;> nlinarith [stationaryCubic_at_66, stationaryCubic_at_67]
  obtain ⟨y, hy, hroot⟩ := intermediate_value_Icc (show (66 : ℝ) ≤ 67 by norm_num)
    hcont hzero
  refine ⟨y, ⟨hy, hroot⟩, ?_⟩
  intro z hz
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmono := stationaryCubic_strictMono hz.1 hy hlt
    linarith
  · have hmono := stationaryCubic_strictMono hy hz.1 hgt
    linarith

theorem stationaryCubic_discriminant :
    (-16947864892329506560000 : ℤ) =
      (-232119)^2 * (-928475)^2
      - 4 * 3715 * (-928475)^3
      - 4 * (-232119)^3 * (-1160625)
      - 27 * 3715^2 * (-1160625)^2
      + 18 * 3715 * (-232119) * (-928475) * (-1160625) := by
  norm_num

end PiIrrationality
