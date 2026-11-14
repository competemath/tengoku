import Tengoku
import Tengoku.Piirrationalitymeasure.Formalization.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Exact root-isolation certificates for the stationary cubic in Appendix A.1.
-/

namespace PiIrrationality

def stationaryCubic (y : ℝ) : ℝ :=
  3715 * y^3 - 232119 * y^2 - 928475 * y - 1160625

/--
@isnad1 id=lt.0h0v.s4.823b4ad6f839 from=translated src=- shape=3c26ae4f vocab=892dfa56
-/
theorem stationaryCubic_at_66 : stationaryCubic 66 < 0 := by
  norm_num [stationaryCubic]

/--
@isnad1 id=lt.0h0v.s4.ec7a376a9cc5 from=translated src=- shape=cf0a9d99 vocab=892dfa56
-/
theorem stationaryCubic_at_67 : 0 < stationaryCubic 67 := by
  norm_num [stationaryCubic]

/--
@isnad1 id=strictmo.0h0v.s4.2d1438876362 from=translated src=- shape=6c3888e7 vocab=4645fd30
-/
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

/--
@isnad1 id=existsun.0h0v.s5.dac2a0cf8a57 from=translated src=- shape=57cd9b24 vocab=55db463e
-/
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

/--
@isnad1 id=eq.0h0v.s8.c591991d7744 from=translated src=- shape=c5f2076c vocab=d13119ac
-/
theorem stationaryCubic_discriminant :
    (-16947864892329506560000 : ℤ) =
      (-232119)^2 * (-928475)^2
      - 4 * 3715 * (-928475)^3
      - 4 * (-232119)^3 * (-1160625)
      - 27 * 3715^2 * (-1160625)^2
      + 18 * 3715 * (-232119) * (-928475) * (-1160625) := by
  norm_num

end PiIrrationality
