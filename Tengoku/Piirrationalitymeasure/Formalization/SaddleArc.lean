import Tengoku.Piirrationalitymeasure.Formalization.Saddle
import Tengoku.Piirrationalitymeasure.Formalization.ContourPath

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The explicit saddle parameters and the identity (4.17) placing the complex
saddle on the controlled arc.
-/

namespace PiIrrationality

noncomputable def saddleX : ℝ := (-3 * saddleU + 4 * saddleV) / saddleNormSq

noncomputable def saddleY : ℝ := (4 * saddleU + 3 * saddleV) / saddleNormSq

noncomputable def saddleLambda : ℝ := 1 / saddleX

noncomputable def saddleEta : ℝ := -saddleY / (saddleX - 1)

/--
@isnad1 id=lt.0h0v.s4.efe4a8b4b193 from=translated src=- shape=0efb1284 vocab=5831f76f
-/
theorem saddleV_lt : saddleV < (11 : ℝ) / 10 := by
  have hv2 := saddleV_sq
  unfold saddleVSq at hv2
  have hu := saddleU_tight_bounds
  have hm := saddleNormSq_lt
  have hv0 := saddleV_pos
  nlinarith [hv2]

/--
@isnad1 id=lt.0h0v.s3.227ebcf3e5d3 from=translated src=- shape=ff3a10fc vocab=f1f1b7af
-/
theorem saddleX_gt_one : 1 < saddleX := by
  unfold saddleX
  apply (lt_div_iff₀ saddleNormSq_pos).2
  have hu := saddleU_tight_bounds
  have hm := saddleNormSq_lt
  have hv := saddleV_pos
  nlinarith

/--
@isnad1 id=lt.0h0v.s3.a85c76f754d5 from=translated src=- shape=ff3a10fc vocab=f1f1b7af
-/
theorem saddleX_pos : 0 < saddleX := by linarith [saddleX_gt_one]

/--
@isnad1 id=mem.0h0v.s4.086dcaf584af from=translated src=- shape=48e903f7 vocab=0cffe37a
-/
theorem saddleLambda_mem : saddleLambda ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold saddleLambda
  constructor
  · exact one_div_pos.mpr saddleX_pos
  · exact (div_lt_iff₀ saddleX_pos).2 (by linarith [saddleX_gt_one])

noncomputable def saddleLambdaLower : ℝ :=
  (48021524689625610102 : ℝ) / 10 ^ 20

noncomputable def saddleLambdaUpper : ℝ :=
  (48021524689625610103 : ℝ) / 10 ^ 20

/--
@isnad1 id=and.0h0v.s3.7192ad375958 from=translated src=- shape=9cf45692 vocab=d612cba1
-/
theorem saddleLambda_paper_bounds :
    saddleLambdaLower < saddleLambda ∧ saddleLambda < saddleLambdaUpper := by
  have hm := saddleNormSq_paper_bounds
  have hu := saddleU_paper_bounds
  have hv := saddleV_paper_bounds
  have hNpos : 0 < -3 * saddleU + 4 * saddleV := by
    nlinarith [saddleU_bounds.2, saddleV_pos]
  have hm' := hm
  dsimp [saddleNormSqLower, saddleNormSqUpper] at hm'
  have hu' := hu
  have hv' := hv
  dsimp [saddleULower, saddleUUpper, saddleVLower, saddleVUpper] at hu' hv'
  have hNlow :
      (9809479826108466287978065 : ℝ) / 10 ^ 24 <
        -3 * saddleU + 4 * saddleV := by
    nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
  have hNupp :
      -3 * saddleU + 4 * saddleV <
        (9809479826108466287978074 : ℝ) / 10 ^ 24 := by
    nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
  have hdiv : saddleLambda = saddleNormSq / (-3 * saddleU + 4 * saddleV) := by
    unfold saddleLambda saddleX
    field_simp [ne_of_gt saddleNormSq_pos, ne_of_gt hNpos]
  have hlow : saddleLambdaLower * (-3 * saddleU + 4 * saddleV) < saddleNormSq := by
    have hnum : saddleLambdaLower *
        ((9809479826108466287978074 : ℝ) / 10 ^ 24) <
          (4710661776618520503155596336 : ℝ) / 10 ^ 27 := by
      norm_num [saddleLambdaLower]
    nlinarith [hm'.1, hNupp, hnum]
  have hupp : saddleNormSq < saddleLambdaUpper * (-3 * saddleU + 4 * saddleV) := by
    have hnum : (4710661776618520503155596337 : ℝ) / 10 ^ 27 <
        saddleLambdaUpper *
          ((9809479826108466287978065 : ℝ) / 10 ^ 24) := by
      norm_num [saddleLambdaUpper]
    nlinarith [hm'.2, hNlow, hnum]
  constructor
  · rw [hdiv]
    exact (lt_div_iff₀ hNpos).2 hlow
  · rw [hdiv]
    exact (div_lt_iff₀ hNpos).2 hupp

/--
@isnad1 id=lt.0h0v.s3.550b1b633a14 from=translated src=- shape=ffdda526 vocab=7c7869b0
-/
theorem saddleY_neg : saddleY < 0 := by
  unfold saddleY
  have hu := saddleU_tight_bounds
  have hv := saddleV_lt
  apply div_neg_of_neg_of_pos
  · nlinarith
  · exact saddleNormSq_pos

/--
@isnad1 id=lt.0h0v.s3.5da556b3f882 from=translated src=- shape=ff3a10fc vocab=278acded
-/
theorem saddleEta_pos : 0 < saddleEta := by
  unfold saddleEta
  exact div_pos (neg_pos.mpr saddleY_neg) (by linarith [saddleX_gt_one])

/--
@isnad1 id=lt.0h0v.s3.f2519625f1c6 from=translated src=- shape=ffdda526 vocab=278acded
-/
theorem saddleEta_lt_one : saddleEta < 1 := by
  unfold saddleEta
  have hx : 0 < saddleX - 1 := by linarith [saddleX_gt_one]
  apply (div_lt_iff₀ hx).2
  unfold saddleY saddleX
  have hm := saddleNormSq_pos
  have hu := saddleU_tight_bounds
  have hv := saddleV_gt
  have hml := saddleNormSq_lt
  field_simp [ne_of_gt hm]
  nlinarith

/--
@isnad1 id=mem.0h0v.s4.65a938a88b71 from=translated src=- shape=48e903f7 vocab=4d0e0a33
-/
theorem saddleEta_mem : saddleEta ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨saddleEta_pos, saddleEta_lt_one⟩

noncomputable def saddleQ : ℂ := (-3 : ℂ) + 4 * Complex.I

/--
@isnad1 id=eq.0h0v.s4.5938a9aabe57 from=translated src=- shape=cd8fc378 vocab=6d0bd394
-/
theorem saddle_ratio_mul :
    ((saddleX : ℂ) + (saddleY : ℂ) * Complex.I) * saddleUpper = saddleQ := by
  apply Complex.ext
  · simp [saddleX, saddleY, saddleUpper, saddleQ, Complex.mul_re, Complex.mul_im]
    have hv := saddleV_sq
    unfold saddleVSq at hv
    field_simp [ne_of_gt saddleNormSq_pos]
    nlinarith [hv]
  · simp [saddleX, saddleY, saddleUpper, saddleQ, Complex.mul_re, Complex.mul_im]
    have hv := saddleV_sq
    unfold saddleVSq at hv
    field_simp [ne_of_gt saddleNormSq_pos]
    nlinarith [hv]

/--
@isnad1 id=ne.0h0v.s4.62b0423a0f09 from=translated src=- shape=8eb6ceac vocab=3f5f2945
-/
theorem saddle_ratio_ne_zero :
    (saddleX : ℂ) + (saddleY : ℂ) * Complex.I ≠ 0 := by
  intro h
  have hr := saddle_ratio_mul
  rw [h] at hr
  have hr' := congrArg Complex.re hr
  norm_num [saddleQ] at hr'

/--
@isnad1 id=eq.0h0v.s2.7c10e4057708 from=translated src=- shape=583fb3b9 vocab=b16770f7
-/
theorem saddle_arc_identity :
    gammaPath saddleEta saddleLambda = saddleUpper := by
  have hx : saddleX ≠ 0 := ne_of_gt saddleX_pos
  have hxm : saddleX - 1 ≠ 0 := ne_of_gt (by linarith [saddleX_gt_one])
  have hxC : (saddleX : ℂ) ≠ 0 := by exact_mod_cast hx
  have hxmC : (saddleX : ℂ) - 1 ≠ 0 := by exact_mod_cast hxm
  have hden : (saddleX : ℂ) + (saddleY : ℂ) * Complex.I ≠ 0 := saddle_ratio_ne_zero
  have hxmInv : (-1 + (saddleX : ℂ))⁻¹ =
      ((saddleX - 1)⁻¹ : ℝ) := by
    rw [show (-1 : ℂ) + (saddleX : ℂ) = ((saddleX - 1 : ℝ) : ℂ) by
      norm_num; ring]
    rw [← Complex.ofReal_inv]
  unfold gammaPath saddleEta saddleLambda
  have hfactor :
      1 - Complex.I * ((-saddleY / (saddleX - 1) : ℝ) : ℂ) *
          (1 - ((1 / saddleX : ℝ) : ℂ)) =
        ((saddleX : ℂ) + (saddleY : ℂ) * Complex.I) / (saddleX : ℂ) := by
    apply Complex.ext
    · norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      field_simp [hx, hxm, hxC, hxmC]
    · norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      field_simp [hx, hxm, hxC, hxmC]
  rw [hfactor]
  have hxInv : ((1 / saddleX : ℝ) : ℂ) = (saddleX : ℂ)⁻¹ := by
    rw [one_div]
    exact Complex.ofReal_inv _
  rw [hxInv]
  calc
    saddleQ * (saddleX : ℂ)⁻¹ /
          (((saddleX : ℂ) + (saddleY : ℂ) * Complex.I) / (saddleX : ℂ)) =
        saddleQ / ((saddleX : ℂ) + (saddleY : ℂ) * Complex.I) := by
          field_simp [hxC, hden]
    _ = saddleUpper := by
      apply (div_eq_iff hden).2
      simpa [mul_comm, add_comm, add_left_comm, add_assoc] using saddle_ratio_mul.symm

end PiIrrationality
