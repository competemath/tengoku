import Tengoku.Piirrationalitymeasure.Formalization.LocalOptimization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! An exact quadratic remainder for the quotient in (6.55). -/

namespace PiIrrationality

theorem quotient_sub_linear_remainder {N D u v : ℝ} (hD : D ≠ 0)
    (hDv : D + v ≠ 0) :
    (N + u) / (D + v) - N / D - (D * u - N * v) / D ^ 2 =
      -(D * u - N * v) * v / (D ^ 2 * (D + v)) := by
  field_simp
  <;> ring

theorem quotient_quadratic_remainder_bound {N D u v U V t : ℝ}
    (hD : 0 < D) (hDv : D / 2 ≤ D + v) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (ht : 0 ≤ t) (hu : |u| ≤ U * t) (hv : |v| ≤ V * t) :
    |(N + u) / (D + v) - N / D - (D * u - N * v) / D ^ 2| ≤
      (2 * (D * U + |N| * V) * V / D ^ 3) * t ^ 2 := by
  have hDvpos : 0 < D + v := lt_of_lt_of_le (by positivity) hDv
  rw [quotient_sub_linear_remainder hD.ne' hDvpos.ne', abs_div, abs_mul, abs_neg,
    abs_of_pos (show 0 < D ^ 2 * (D + v) by positivity)]
  have hlin : |D * u - N * v| ≤ (D * U + |N| * V) * t := by
    have htri := abs_sub (D * u) (N * v)
    rw [abs_mul, abs_mul, abs_of_pos hD] at htri
    have hu' := mul_le_mul_of_nonneg_left hu hD.le
    have hv' := mul_le_mul_of_nonneg_left hv (abs_nonneg N)
    nlinarith only [htri, hu', hv']
  have hprod := mul_le_mul hlin hv (abs_nonneg v) (by positivity)
  have hden : D ^ 3 / 2 ≤ D ^ 2 * (D + v) := by
    have hm := mul_le_mul_of_nonneg_left hDv (sq_nonneg D)
    nlinarith only [hm]
  apply (div_le_iff₀ (show 0 < D ^ 2 * (D + v) by positivity)).mpr
  calc
    |D * u - N * v| * |v| ≤ (D * U + |N| * V) * V * t ^ 2 := by
      nlinarith only [hprod]
    _ = ((2 * (D * U + |N| * V) * V / D ^ 3) * t ^ 2) * (D ^ 3 / 2) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

theorem quotient_saving_remainder_bound {N D a b w A B W e L : ℝ}
    (hD : 0 < D) (hden : D / 2 ≤ D + b + w)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : 0 ≤ W) (he : 0 ≤ e) (hL : 1 ≤ L)
    (ha : |a| ≤ A * e) (hb : |b| ≤ B * e) (hw : |w| ≤ W * (e * L)) :
    |(N + a - w) / (D + b + w) - N / D + ((D + N) / D ^ 2) * w| ≤
      ((D * A + |N| * B) / D ^ 2) * e +
        (2 * (D * (A + W) + |N| * (B + W)) * (B + W) / D ^ 3) *
          (e * L) ^ 2 := by
  have hLe : e ≤ e * L := by nlinarith
  have hu : |a - w| ≤ (A + W) * (e * L) := by
    have htri := abs_sub a w
    have hm := mul_le_mul_of_nonneg_left hLe hA
    nlinarith only [ha, hw, htri, hm]
  have hv : |b + w| ≤ (B + W) * (e * L) := by
    have htri := abs_add_le b w
    have hm := mul_le_mul_of_nonneg_left hLe hB
    nlinarith only [hb, hw, htri, hm]
  have hrem := quotient_quadratic_remainder_bound (N := N) hD
    (v := b + w) (by linarith) (add_nonneg hA hW) (add_nonneg hB hW)
    (show 0 ≤ e * L by positivity) hu hv
  have hlin : |(D * a - N * b) / D ^ 2| ≤ ((D * A + |N| * B) / D ^ 2) * e := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hD)]
    have htri := abs_sub (D * a) (N * b)
    rw [abs_mul, abs_mul, abs_of_pos hD] at htri
    have ha' := mul_le_mul_of_nonneg_left ha hD.le
    have hb' := mul_le_mul_of_nonneg_left hb (abs_nonneg N)
    apply (div_le_iff₀ (sq_pos_of_pos hD)).mpr
    have heq : ((D * A + |N| * B) / D ^ 2) * e * D ^ 2 =
        (D * A + |N| * B) * e := by field_simp
    rw [heq]
    nlinarith only [htri, ha', hb']
  have heq : (N + a - w) / (D + b + w) - N / D + ((D + N) / D ^ 2) * w =
      ((N + (a - w)) / (D + (b + w)) - N / D -
        (D * (a - w) - N * (b + w)) / D ^ 2) + (D * a - N * b) / D ^ 2 := by
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith only [hrem, hlin])

end PiIrrationality
