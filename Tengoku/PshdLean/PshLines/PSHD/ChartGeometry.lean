import Tengoku.PshdLean.PshLines.PSHD.StarGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Gram determinants in a bounded affine projective chart

A concrete local-chart estimate for the energy argument of `pshd-vibe`,
Lemma 1.3. The chart vectors are `(1,v)` before normalization.
-/

namespace PshLines.PSHD

/-- The Gram determinant of `(1,v)` and `(1,w)` controls `‖v-w‖²`.
@isnad1 id=le.0h3v.s7.640ab156cdae from=translated src=- shape=055ff338 vocab=7965592d
-/
theorem affineChart_gram_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v w : E) :
    ‖v - w‖ ^ 2 ≤
      (1 + ‖v‖ ^ 2) * (1 + ‖w‖ ^ 2) - ‖(1 : ℂ) + inner ℂ v w‖ ^ 2 := by
  have hi := norm_inner_le_norm v w (𝕜 := ℂ)
  have hisq : ‖inner ℂ v w‖ ^ 2 ≤ ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
    nlinarith [norm_nonneg (inner ℂ v w), norm_nonneg v, norm_nonneg w]
  rw [norm_sub_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ)]
  simp only [norm_one, RCLike.inner_apply, map_one, mul_one]
  change ‖v‖ ^ 2 - 2 * (inner ℂ v w).re + ‖w‖ ^ 2 ≤
    (1 + ‖v‖ ^ 2) * (1 + ‖w‖ ^ 2) -
      (1 ^ 2 + 2 * (inner ℂ v w).re + ‖inner ℂ v w‖ ^ 2)
  nlinarith

/-- On a unit affine chart, the normalized Hermitian correlation controls
Euclidean separation with an absolute constant.
@isnad1 id=le.2h3v.s8.1a8e8c863d23 from=translated src=- shape=cb28e760 vocab=2fd64363
-/
theorem affineChart_correlation_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {v w : E} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖v - w‖ ^ 2 / 4 ≤ 2 - 2 *
      (‖(1 : ℂ) + inner ℂ v w‖ /
        Real.sqrt ((1 + ‖v‖ ^ 2) * (1 + ‖w‖ ^ 2))) := by
  let D := (1 + ‖v‖ ^ 2) * (1 + ‖w‖ ^ 2)
  let B := ‖(1 : ℂ) + inner ℂ v w‖
  let q := B / Real.sqrt D
  have hD : 0 < D := by dsimp [D]; positivity
  have hD4 : D ≤ 4 := by
    have hv2 : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
    have hw2 : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    calc
      D ≤ 2 * 2 := mul_le_mul (by linarith : 1 + ‖v‖ ^ 2 ≤ 2)
        (by linarith : 1 + ‖w‖ ^ 2 ≤ 2) (by positivity) (by positivity)
      _ = 4 := by norm_num
  have hd : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hd2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD.le
  have hq0 : 0 ≤ q := div_nonneg (norm_nonneg _) hd.le
  have hmul : q * Real.sqrt D = B := div_mul_cancel₀ _ hd.ne'
  have hg : ‖v - w‖ ^ 2 ≤ D - B ^ 2 := affineChart_gram_lower_bound v w
  have hB : B ≤ Real.sqrt D := by nlinarith [sq_nonneg ‖v - w‖]
  have hq1 : q ≤ 1 := (div_le_one hd).mpr hB
  have hidentity : D * (1 - q ^ 2) = D - B ^ 2 := by
    calc
      D * (1 - q ^ 2) = D - (q * Real.sqrt D) ^ 2 := by
        rw [mul_pow, hd2]
        ring
      _ = D - B ^ 2 := by rw [hmul]
  have hpos : 0 ≤ 1 - q ^ 2 := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hD4 hpos
  change ‖v - w‖ ^ 2 / 4 ≤ 2 - 2 * q
  nlinarith [sq_nonneg (1 - q)]

end PshLines.PSHD
