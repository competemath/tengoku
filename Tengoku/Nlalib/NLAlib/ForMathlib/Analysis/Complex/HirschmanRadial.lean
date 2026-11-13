import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.HirschmanExponentialBoundary
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.HirschmanDiskSubmean
import Tengoku.Seed.Analysis.Complex.Hadamard
import Tengoku.Seed.MeasureTheory.Function.SpecialFunctions.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Radial boundary limits for the Stein--Hirschman conformal map

The upper-half-plane approach is retained at negative real boundary points,
so the principal logarithm has the boundary value used by the exact strip
densities. Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, Appendix D.
-/

noncomputable section

open Real Set Metric MeasureTheory Filter
open scoped Topology

namespace Complex

/-- The arctangent circle parametrization never takes the omitted point `1`.
@isnad1 id=ne.0h1v.s4.d0e31e7057b0 from=translated src=- shape=1c8609c1 vocab=b3b45854
-/
theorem circleMap_hirschmanBoundaryAngle_ne_one (q : ℝ) :
    circleMap 0 1 (hirschmanBoundaryAngle q) ≠ 1 := by
  rw [circleMap_hirschmanBoundaryAngle]
  have hden : (q : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  intro h
  have he := (div_eq_one_iff_eq hden).mp h
  have := congrArg Complex.im he
  norm_num at this

/-- Every real boundary coordinate maps into the closed vertical strip,
including the harmless convention at the single zero coordinate.
@isnad1 id=mem.0h1v.s5.9285ceca3289 from=translated src=- shape=c30129df vocab=4874150d
-/
theorem hirschmanLog_real_re_mem_Icc (w : ℝ) :
    (log (w : ℂ) * (-I) / (π : ℂ)).re ∈ Icc (0 : ℝ) 1 := by
  have heq : (log (w : ℂ) * (-I) / (π : ℂ)).re = arg (w : ℂ) / π := by
    simp [div_ofReal_re, mul_re, log_im]
  rw [heq]
  exact ⟨div_nonneg (arg_nonneg_iff.mpr (by simp)) pi_pos.le,
    (div_le_one pi_pos).mpr (arg_le_pi _)⟩

/-- Measurability of the real logarithmic boundary is available even though
the complex logarithm is not continuous across its branch cut.
@isnad1 id=measurab.0h0v.s5.ef7da587b18c from=translated src=- shape=8aa6f563 vocab=d8e75600
-/
theorem measurable_hirschmanLog_real :
    Measurable (fun w : ℝ => log (w : ℂ) * (-I) / (π : ℂ)) := by
  fun_prop

/-- A continuous function on the closed strip gives a measurable boundary
observable; no measurability outside the strip is required.
@isnad1 id=measurab.1h1v.s6.ec82b736c8c7 from=translated src=- shape=e40f34ec vocab=361ba97f
-/
theorem _root_.ContinuousOn.measurable_comp_hirschmanLog_real {g : ℂ → ℂ}
    (hg : ContinuousOn g (HadamardThreeLines.verticalClosedStrip 0 1)) :
    Measurable (fun w : ℝ => g (log (w : ℂ) * (-I) / (π : ℂ))) := by
  let f : ℝ → HadamardThreeLines.verticalClosedStrip 0 1 := fun w =>
    ⟨log (w : ℂ) * (-I) / (π : ℂ), hirschmanLog_real_re_mem_Icc w⟩
  have hgc : Continuous (fun z : HadamardThreeLines.verticalClosedStrip 0 1 => g z) :=
    continuousOn_iff_continuous_domRestrict.mp hg
  exact hgc.measurable.comp (show Measurable f from measurable_hirschmanLog_real.subtype_mk)

/-- Limits from the open disk give the principal logarithmic boundary value
at every finite boundary coordinate except the one mapping to zero.
@isnad1 id=tendsto.4h3v.s7.a249fcd1840d from=translated src=- shape=3bf1a8c6 vocab=78efac88
-/
theorem tendsto_hirschmanDiskToStrip_boundary {r q : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) {u : ℕ → ℂ}
    (hu : ∀ n, u n ∈ ball (0 : ℂ) 1)
    (hlim : Tendsto u atTop (𝓝 (circleMap 0 1 (hirschmanBoundaryAngle q))))
    (hw : Real.cos (π * r) + Real.sin (π * r) * q ≠ 0) :
    Tendsto (fun n => hirschmanDiskToStrip r (u n)) atTop
      (𝓝 (log ((Real.cos (π * r) + Real.sin (π * r) * q : ℝ) : ℂ) * (-I) / (π : ℂ))) := by
  have hs : 0 < Real.sin (π * r) := Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1)
    (by nlinarith [pi_pos, hr.2])
  have hM : ContinuousAt (hirschmanDiskToHalfPlane (Real.cos (π * r)) (Real.sin (π * r)))
      (circleMap 0 1 (hirschmanBoundaryAngle q)) := by
    unfold hirschmanDiskToHalfPlane
    fun_prop (disch := exact sub_ne_zero.mpr (circleMap_hirschmanBoundaryAngle_ne_one q).symm)
  have hMl : Tendsto
      (fun n => hirschmanDiskToHalfPlane (Real.cos (π * r)) (Real.sin (π * r)) (u n))
      atTop (𝓝 ((Real.cos (π * r) + Real.sin (π * r) * q : ℝ) : ℂ)) := by
    have ht := hM.tendsto.comp hlim
    rw [hirschmanDiskToHalfPlane_circleMap_boundary] at ht
    exact ht.congr' (Eventually.of_forall fun _ => rfl)
  have hlog : Tendsto
      (fun n => log (hirschmanDiskToHalfPlane (Real.cos (π * r)) (Real.sin (π * r)) (u n)))
      atTop (𝓝 (log ((Real.cos (π * r) + Real.sin (π * r) * q : ℝ) : ℂ))) := by
    by_cases hp : 0 < Real.cos (π * r) + Real.sin (π * r) * q
    · exact (differentiableAt_log (Or.inl hp)).continuousAt.tendsto.comp hMl
    · have hn : Real.cos (π * r) + Real.sin (π * r) * q < 0 := lt_of_le_of_ne (le_of_not_gt hp) hw
      exact (continuousWithinAt_log_of_re_neg_of_im_zero
        (z := ((Real.cos (π * r) + Real.sin (π * r) * q : ℝ) : ℂ)) hn rfl).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hMl, Eventually.of_forall fun n =>
          (hirschmanDiskToHalfPlane_im_pos (Real.cos (π * r)) hs (hu n)).le⟩)
  exact (hlog.mul_const (-I)).div_const (π : ℂ)

/-- Radial circles of radius strictly below one remain inside the conformal
domain and depend continuously on their real boundary parameter.
@isnad1 id=continuo.2h2v.s6.b82d3c7de581 from=translated src=- shape=b75b965e vocab=f5fcc78f
-/
theorem continuous_hirschmanDiskToStrip_radial {r ρ : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    Continuous (fun q : ℝ => hirschmanDiskToStrip r
      ((ρ : ℂ) * circleMap 0 1 (hirschmanBoundaryAngle q))) := by
  apply (analyticOnNhd_hirschmanDiskToStrip hr).continuousOn.comp_continuous
  · unfold hirschmanBoundaryAngle
    fun_prop
  · intro q
    have hn : ‖(ρ : ℂ) * circleMap 0 1 (hirschmanBoundaryAngle q)‖ < 1 := by
      simpa [norm_mul, norm_circleMap_zero, abs_of_pos hρ.1] using hρ.2
    simpa using hn

/-- A strictly positive regularization of the logarithmic norm.-/
def regularizedLogNorm (ε : ℝ) (z : ℂ) : ℝ :=
  Real.log (sqrt (‖z‖ ^ 2 + ε ^ 2))

/--
@isnad1 id=continuo.1h1v.s5.d7616b3b42f1 from=translated src=- shape=cc36a0cc vocab=afccdba4
-/
theorem continuous_regularizedLogNorm {ε : ℝ} (hε : 0 < ε) :
    Continuous (regularizedLogNorm ε) := by
  apply Continuous.log _ (fun z => ne_of_gt (sqrt_pos.mpr (by positivity)))
  exact ((continuous_norm.pow 2).add continuous_const).sqrt

/-- Both sides of the regularized logarithm have explicit uniform bounds.
@isnad1 id=and.3h3v.s6.84850ca801fd from=translated src=- shape=0b664976 vocab=75087eb4
-/
theorem regularizedLogNorm_bounds {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ B) :
    Real.log ε ≤ regularizedLogNorm ε z ∧
      regularizedLogNorm ε z ≤ Real.log (sqrt (B ^ 2 + ε ^ 2)) := by
  have hpos : 0 < sqrt (‖z‖ ^ 2 + ε ^ 2) := sqrt_pos.mpr (by positivity)
  constructor
  · apply Real.log_le_log hε
    calc
      ε = sqrt (ε ^ 2) := (sqrt_sq hε.le).symm
      _ ≤ _ := sqrt_le_sqrt (by nlinarith [sq_nonneg ‖z‖])
  · apply Real.log_le_log hpos
    apply sqrt_le_sqrt
    nlinarith [norm_nonneg z]

/-- A bounded strip function has a bounded regularized logarithmic boundary.
@isnad1 id=le.3h3v.s6.c1e8fe5e1b5d from=translated src=- shape=b644218f vocab=8076a4a3
-/
theorem abs_regularizedLogNorm_le {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ B) :
    |regularizedLogNorm ε z| ≤ |Real.log ε| + |Real.log (sqrt (B ^ 2 + ε ^ 2))| := by
  have h := regularizedLogNorm_bounds hε hB hz
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log ε), abs_nonneg (Real.log (sqrt (B ^ 2 + ε ^ 2)))]
  · linarith [le_abs_self (Real.log (sqrt (B ^ 2 + ε ^ 2))), abs_nonneg (Real.log ε)]

/-- The regularized boundary observable is genuinely Bochner integrable
against every Cauchy density.
@isnad1 id=integrab.4h5v.s7.98d740d296ba from=translated src=- shape=52fbc4a1 vocab=737f1832
-/
theorem integrable_cauchy_mul_regularizedLog_boundary {g : ℂ → ℂ}
    (hg : ContinuousOn g (HadamardThreeLines.verticalClosedStrip 0 1))
    {B ε : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z ∈ HadamardThreeLines.verticalClosedStrip 0 1, ‖g z‖ ≤ B)
    (hε : 0 < ε) (a : ℝ) (b : NNReal) :
    Integrable (fun w : ℝ => ProbabilityTheory.cauchyPDFReal a b w *
      regularizedLogNorm ε (g (log (w : ℂ) * (-I) / (π : ℂ)))) := by
  have hm := (continuous_regularizedLogNorm hε).measurable.comp
    hg.measurable_comp_hirschmanLog_real
  apply ((ProbabilityTheory.integrable_cauchyPDFReal a (γ := b)).const_mul
    (|Real.log ε| + |Real.log (sqrt (B ^ 2 + ε ^ 2))|)).mono'
    ((ProbabilityTheory.measurable_cauchyPDFReal a b).mul hm).aestronglyMeasurable
  exact ae_of_all _ fun w => by
    dsimp only [Pi.mul_apply, Function.comp_apply]
    have hp : 0 ≤ ProbabilityTheory.cauchyPDFReal a b w := by
      unfold ProbabilityTheory.cauchyPDFReal
      positivity
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hp, Real.norm_eq_abs]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (abs_regularizedLogNorm_le hε hB (hbound _ (hirschmanLog_real_re_mem_Icc w))) hp

/-- The standard Cauchy density is exactly the arctangent angular Jacobian.
@isnad1 id=eq.0h1v.s6.ab6af8a24107 from=translated src=- shape=12b485b1 vocab=4ccb3c3d
-/
theorem hirschmanBoundaryWeight_eq_cauchy (q : ℝ) :
    1 / (π * (1 + q ^ 2)) = ProbabilityTheory.cauchyPDFReal 0 1 q := by
  simp only [ProbabilityTheory.cauchyPDFReal, NNReal.coe_one, sub_zero, one_pow, mul_one]
  field_simp
  ring

/-- Scaling the circle radius can be moved into its integrand exactly.
@isnad1 id=eq.0h2v.s6.6f3e0ccfd6a6 from=translated src=- shape=c85dac05 vocab=ca133b61
-/
theorem circleAverage_zero_radius_eq_circleAverage_smul (F : ℂ → ℝ) (ρ : ℝ) :
    Real.circleAverage F 0 ρ = Real.circleAverage (fun z => F ((ρ : ℂ) * z)) 0 1 := by
  simp only [Real.circleAverage, circleMap, zero_add, ofReal_one, one_mul]

end Complex
