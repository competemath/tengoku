import Tengoku.AbelFormalization.AbelFormalization.Inverse
import Tengoku.Seed.Analysis.Calculus.MeanValue
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Analytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quantitative contraction by the principal logarithm

The complex version of `L` maps a disk about a sufficiently positive real
center into a smaller disk. The explicit bound remains valid for the first,
possibly large, disk in the construction of the paper's holomorphic extensions.
-/

noncomputable section

namespace AbelFormalization

open Set Complex

/-- The principal complex logarithmic inverse of the dynamics.-/
def complexL (z : ℂ) : ℂ := Complex.log (1 + z)

/--
@isnad1 id=eq.1h1v.s5.692a866f8561 from=translated src=- shape=9edbe257 vocab=795e3ba0
-/
theorem complexL_ofReal {x : ℝ} (hx : 0 ≤ 1 + x) :
    complexL (x : ℂ) = (L x : ℂ) := by
  simp only [complexL, L, Complex.ofReal_log hx, Complex.ofReal_add,
    Complex.ofReal_one]

private theorem one_add_re_lower_bound {c r : ℝ} {z : ℂ}
    (hz : z ∈ Metric.ball (c : ℂ) r) :
    1 + c - r < (1 + z).re := by
  have h := Complex.re_le_norm ((c : ℂ) - z)
  have hn : ‖(c : ℂ) - z‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz
  simp only [sub_re, ofReal_re, add_re, one_re] at *
  linarith

/--
@isnad1 id=hasderiv.1h1v.s6.221c949c6453 from=translated src=- shape=fc45903f vocab=5248019e
-/
theorem complexL_hasDerivAt {z : ℂ} (hz : 0 < (1 + z).re) :
    HasDerivAt complexL (1 + z)⁻¹ z := by
  change HasDerivAt (fun w : ℂ => Complex.log (1 + w)) (1 + z)⁻¹ z
  simpa only [one_div, id_eq] using
    ((hasDerivAt_id z).const_add 1).clog (Or.inl hz)

/--
@isnad1 id=analytic.1h1v.s5.c881947a25e9 from=translated src=- shape=874a7564 vocab=e57b0e4f
-/
theorem complexL_analyticAt {z : ℂ} (hz : 0 < (1 + z).re) :
    AnalyticAt ℂ complexL z :=
  (analyticAt_const.add analyticAt_id).clog (Or.inl hz)

/-- The derivative estimate on a disk gives the precise logarithmic
contraction factor `1 / (1 + c - r)`.
@isnad1 id=le.3h3v.s6.a8062d419407 from=translated src=- shape=1c1c2d29 vocab=0267c7b8
-/
theorem norm_complexL_sub_le {c r : ℝ} (hr : 0 < r) (hc : r < 1 + c)
    {z : ℂ} (hz : z ∈ Metric.ball (c : ℂ) r) :
    ‖complexL z - complexL (c : ℂ)‖ ≤ ‖z - (c : ℂ)‖ / (1 + c - r) := by
  have hd : 0 < 1 + c - r := sub_pos.mpr hc
  have hder : ∀ w ∈ Metric.ball (c : ℂ) r,
      HasDerivWithinAt complexL (1 + w)⁻¹ (Metric.ball (c : ℂ) r) w := by
    intro w hw
    exact (complexL_hasDerivAt (hd.trans (one_add_re_lower_bound hw))).hasDerivWithinAt
  have hbound : ∀ w ∈ Metric.ball (c : ℂ) r, ‖(1 + w)⁻¹‖ ≤ (1 + c - r)⁻¹ := by
    intro w hw
    rw [norm_inv]
    have hl := (one_add_re_lower_bound hw).le.trans (Complex.re_le_norm _)
    exact (inv_le_inv₀ (hd.trans_le hl) hd).mpr hl
  have h := (convex_ball (c : ℂ) r).norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (Metric.mem_ball_self hr) hz
  simpa only [div_eq_mul_inv, mul_comm] using h

/--
@isnad1 id=mapsto.2h2v.s6.9d25920adc12 from=translated src=- shape=7e4472d8 vocab=2ca2065d
-/
theorem complexL_mapsTo_ball {c r : ℝ} (hr : 0 < r) (hc : r < 1 + c) :
    MapsTo complexL (Metric.ball (c : ℂ) r)
      (Metric.ball (complexL (c : ℂ)) (r / (1 + c - r))) := by
  intro z hz
  apply (Metric.mem_ball).mpr
  rw [dist_eq_norm]
  exact (norm_complexL_sub_le hr hc hz).trans_lt
    ((div_lt_div_iff_of_pos_right (sub_pos.mpr hc)).mpr
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hz))

/--
@isnad1 id=analytic.1h2v.s6.f9471b7bd45a from=translated src=- shape=9b867806 vocab=d93f22b3
-/
theorem complexL_analyticOnNhd_ball {c r : ℝ} (hc : r < 1 + c) :
    AnalyticOnNhd ℂ complexL (Metric.ball (c : ℂ) r) := by
  intro z hz
  exact complexL_analyticAt ((sub_pos.mpr hc).trans (one_add_re_lower_bound hz))

end AbelFormalization
