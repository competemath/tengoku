import Tengoku.Piirrationalitymeasure.Formalization.ContourDeformation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The square-root contour deformation for every holomorphic density in the disk. -/

namespace PiIrrationality

/--
@isnad1 id=ex.1h1v.s7.aac2fa31a957 from=translated src=- shape=bc25a3b0 vocab=dc9d7f2c
-/
theorem disk_density_primitive {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, ‖z‖ < 5 → DifferentiableAt ℂ f z) :
    ∃ F : ℂ → ℂ, ∀ z : ℂ, ‖z‖ < 5 → HasDerivAt F (f z) z := by
  have hd : DifferentiableOn ℂ f (Metric.ball 0 5) := by
    intro z hz
    exact (hf z (by simpa using hz)).differentiableWithinAt
  simpa only [Complex.IsExactOn, Metric.mem_ball, dist_zero_right] using hd.isExactOn_ball

/--
@isnad1 id=interval.3h4v.s8.07bce1e7ff2c from=translated src=- shape=c6feba8b vocab=2095d0bf
-/
theorem disk_density_path_integrable {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, ‖z‖ < 5 → DifferentiableAt ℂ f z)
    {g : ℝ → ℂ} {a b : ℝ} (hg : ContDiff ℝ 1 g)
    (hB : ∀ u ∈ Set.uIcc a b, ‖g u‖ < 5) :
    IntervalIntegrable (fun u => f (g u) * deriv g u) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  exact (((hf _ (hB u hu)).continuousAt.comp hg.continuous.continuousAt).mul
    hg.continuous_deriv_one.continuousAt).continuousWithinAt

/--
@isnad1 id=eq.4h5v.s8.95e8d0bc822d from=translated src=- shape=897fd2e3 vocab=1be0ee22
-/
theorem disk_density_path_primitive {f F : ℂ → ℂ}
    (hf : ∀ z : ℂ, ‖z‖ < 5 → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, ‖z‖ < 5 → HasDerivAt F (f z) z)
    {g : ℝ → ℂ} {a b : ℝ} (hg : ContDiff ℝ 1 g)
    (hB : ∀ u ∈ Set.uIcc a b, ‖g u‖ < 5) :
    (∫ u in a..b, f (g u) * deriv g u) = F (g b) - F (g a) :=
  complex_primitive_path_integral (fun u hu => hF _ (hB u hu))
    (fun u _ => (hg.differentiable (by norm_num) u).hasDerivAt)
    (disk_density_path_integrable hf hg hB)

/--
@isnad1 id=eq.2h2v.s8.23d9e0ff3a80 from=translated src=- shape=6c258199 vocab=4d436879
-/
theorem disk_density_vertical_primitive {f F : ℂ → ℂ}
    (hf : ∀ z : ℂ, ‖z‖ < 5 → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, ‖z‖ < 5 → HasDerivAt F (f z) z) :
    -(∫ s : ℝ in (-2)..2, f (verticalSegment s)) =
      Complex.I * (F (-1 + 2 * Complex.I) - F (-1 - 2 * Complex.I)) := by
  have hg : ContDiff ℝ 1 verticalSegment := by
    unfold verticalSegment
    exact contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hi := disk_density_path_integrable hf hg
    (fun s hs => verticalSegment_norm_lt_five hs)
  have h := complex_primitive_path_integral
    (fun s hs => hF _ (verticalSegment_norm_lt_five hs))
    (fun s _ => verticalSegment_hasDerivAt s)
    (show IntervalIntegrable (fun s => f (verticalSegment s) * Complex.I)
      MeasureTheory.volume (-2) 2 from by
        simpa only [(fun s => (verticalSegment_hasDerivAt s).deriv)] using hi)
  have he : verticalSegment 2 = -1 + 2 * Complex.I ∧
      verticalSegment (-2) = -1 - 2 * Complex.I := by
    constructor <;> norm_num [verticalSegment] <;> ring
  rw [he.1, he.2, intervalIntegral.integral_mul_const] at h
  rw [← h]
  calc
    -(∫ s : ℝ in (-2)..2, f (verticalSegment s)) =
        (Complex.I * Complex.I) * (∫ s : ℝ in (-2)..2, f (verticalSegment s)) := by
      rw [Complex.I_mul_I, neg_one_mul]
    _ = _ := by ring

/--
@isnad1 id=eq.3h2v.s8.f9f4b09845fc from=translated src=- shape=244e5936 vocab=17b8e8e5
-/
theorem disk_density_deformation {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, ‖z‖ < 5 → DifferentiableAt ℂ f z)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    -(∫ s : ℝ in (-2)..2, f (verticalSegment s)) = Complex.I *
      (-(∫ u in (0 : ℝ)..1, f (smoothTauPlus e u) * deriv (smoothTauPlus e) u) +
        (∫ u in (0 : ℝ)..1, f (smoothTauMinus e u) * deriv (smoothTauMinus e) u)) := by
  obtain ⟨F, hF⟩ := disk_density_primitive hf
  have hp := disk_density_path_primitive hf hF (smoothTauPlus_contDiff he0 he1)
    (a := 0) (b := 1) (fun u hu => smoothTauPlus_norm_lt_five he0 he1
      (by simpa using hu.1) (by simpa using hu.2))
  have hm := disk_density_path_primitive hf hF (smoothTauMinus_contDiff he0 he1)
    (a := 0) (b := 1) (fun u hu => smoothTauMinus_norm_lt_five he0 he1
      (by simpa using hu.1) (by simpa using hu.2))
  rw [smoothTauPlus_at_zero, smoothTauPlus_at_one] at hp
  rw [smoothTauMinus_at_zero, smoothTauMinus_at_one] at hm
  rw [disk_density_vertical_primitive hf hF, hp, hm]
  ring

end PiIrrationality
