import Tengoku.NavierStokesEuler.Euler.MeanCutoffTaylor
import Tengoku.Seed.Analysis.Calculus.Deriv.Slope

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Genuine directional derivatives of the localized Newtonian operator family in operator norm. -/

noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanGradientTest
  Filter
open scoped ContDiff Topology

private local instance : NormedAddCommGroup (Space →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space →L[ℝ] ℝ) := inferInstance

/--
@isnad1 id=eq.0h1v.s6.2f90e1e6b2a9 from=translated src=- shape=bb0110a5 vocab=4418bfd9
-/
@[simp] theorem Cutoff.translate_zero (χ : Cutoff) : χ.translate 0 = χ := by
  apply Cutoff.ext
  exact funext fun x => congrArg χ.field (add_zero x)

/--
@isnad1 id=eq.0h3v.s21.0e1f3db22fcc from=translated src=- shape=2cfc5193 vocab=5b3e8dc7
-/
theorem cutoffCurl_differenceError (χ : Cutoff) (a : Space) (h : ℝ) :
    cutoffCurl (χ.differenceError a h) =
      h⁻¹ • (cutoffCurl (χ.translate (h • a)) - cutoffCurl χ) - cutoffCurl (χ.directional a) := by
  rw [Cutoff.differenceError, cutoffCurl_sub, Cutoff.differenceQuotient,
    cutoffCurl_scale, cutoffCurl_sub]

/--
@isnad1 id=ex.0h1v.s14.008b22813a1a from=translated src=- shape=3e6aee81 vocab=d2b67583
-/
theorem Cutoff.exists_taylor_controls (χ : Cutoff) :
    ∃ R M₂ M₃ : ℝ, 0 ≤ M₂ ∧ 0 ≤ M₃ ∧
      tsupport χ.field ⊆ Metric.closedBall (0 : Space) R ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ χ.field) x‖ ≤ M₂) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ χ.field)) x‖ ≤ M₃) := by
  obtain ⟨R, hR⟩ := χ.compact.isBounded.subset_closedBall (0 : Space)
  have hs₂ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ χ.field)) :=
    (χ.smooth.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hs₃ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (fderiv ℝ χ.field))) :=
    hs₂.fderiv_right (m := ∞) (by simp)
  obtain ⟨M₂, h₂⟩ := ((χ.compact.fderiv ℝ).fderiv ℝ).exists_bound_of_continuous hs₂.continuous
  obtain ⟨M₃, h₃⟩ := (((χ.compact.fderiv ℝ).fderiv ℝ).fderiv ℝ).exists_bound_of_continuous hs₃.continuous
  exact ⟨R, M₂, M₃, (norm_nonneg _).trans (h₂ 0), (norm_nonneg _).trans (h₃ 0), hR, h₂, h₃⟩

/-- Translating the actual cutoff differentiates the bounded cutoff-curl map in operator norm.
@isnad1 id=hasderiv.0h2v.s19.cd0ba0f4aaa7 from=translated src=- shape=8fa400e5 vocab=7e385dae
-/
theorem cutoffCurl_hasDerivAt_zero (χ : Cutoff) (a : Space) :
    HasDerivAt (fun t : ℝ => cutoffCurl (χ.translate (t • a)))
      (cutoffCurl (χ.directional a)) 0 := by
  obtain ⟨R, M₂, M₃, hM₂, hM₃, hs, h₂, h₃⟩ := χ.exists_taylor_controls
  have hstep : ∀ᶠ h : ℝ in 𝓝 0, ‖h • a‖ ≤ 1 := by
    have hc : ContinuousAt (fun h : ℝ => ‖h • a‖) 0 := by fun_prop
    exact (hc.eventually (gt_mem_nhds (by simp : ‖(0 : ℝ) • a‖ < 1))).mono (fun _ hh => hh.le)
  apply (hasDerivAt_iff_tendsto_slope_zero
    (f := fun t : ℝ => cutoffCurl (χ.translate (t • a)))
    (f' := cutoffCurl (χ.directional a)) (x := 0)).mpr
  simp only [zero_add, zero_smul, Cutoff.translate_zero]
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm'
    (f := fun h : ℝ => h⁻¹ • (cutoffCurl (χ.translate (h • a)) - cutoffCurl χ) -
      cutoffCurl (χ.directional a))
    (t₀ := 𝓝[≠] (0 : ℝ))
    (a := fun h : ℝ => cutoffDifferenceConstant R M₂ M₃ * |h| * ‖a‖ ^ 2)
  · filter_upwards [self_mem_nhdsWithin, hstep.filter_mono nhdsWithin_le_nhds] with h hh hsmall
    have hne : h ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
    rw [← cutoffCurl_differenceError]
    exact (cutoffCurl_norm_le _).trans (cutoffBound_differenceError χ R M₂ M₃ hM₂ hM₃ hs h₂ h₃ a h hne hsmall)
  · have hc : Continuous (fun h : ℝ => cutoffDifferenceConstant R M₂ M₃ * |h| * ‖a‖ ^ 2) := by fun_prop
    simpa only [abs_zero, mul_zero, zero_mul] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/--
@isnad1 id=eq.0h3v.s21.dda96fe3e206 from=translated src=- shape=5d3e9566 vocab=f6918918
-/
theorem weakPotential_differenceError (χ : Cutoff) (a : Space) (h : ℝ) :
    weakPotential (χ.differenceError a h) =
      h⁻¹ • (weakPotential (χ.translate (h • a)) - weakPotential χ) - weakPotential (χ.directional a) := by
  calc
    _ = weakPotential (χ.differenceQuotient a h) - weakPotential (χ.directional a) :=
      weakPotential_sub _ _
    _ = h⁻¹ • weakPotential ((χ.translate (h • a)).sub χ) - weakPotential (χ.directional a) :=
      congrArg (fun B : L2 →L[ℝ] homogeneousSpace => B - weakPotential (χ.directional a))
        (weakPotential_scale ((χ.translate (h • a)).sub χ) h⁻¹)
    _ = _ := congrArg (fun B : L2 →L[ℝ] homogeneousSpace => h⁻¹ • B - weakPotential (χ.directional a))
      (weakPotential_sub (χ.translate (h • a)) χ)

/--
@isnad1 id=le.0h1v.s18.64cdaef10760 from=translated src=- shape=c5ea7f93 vocab=3e184129
-/
theorem weakPotential_operatorNorm_le (χ : Cutoff) : ‖weakPotential χ‖ ≤ cutoffBound χ := by
  change ‖(cutoffCurl χ).adjoint‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact cutoffCurl_norm_le χ

/-- The represented weak potential differentiates with the same actual cutoff derivative.
@isnad1 id=hasderiv.0h2v.s19.55ba2a875b2e from=translated src=- shape=7c553d24 vocab=137611fb
-/
theorem weakPotential_hasDerivAt_zero (χ : Cutoff) (a : Space) :
    HasDerivAt (fun t : ℝ => weakPotential (χ.translate (t • a)))
      (weakPotential (χ.directional a)) 0 := by
  obtain ⟨R, M₂, M₃, hM₂, hM₃, hs, h₂, h₃⟩ := χ.exists_taylor_controls
  have hstep : ∀ᶠ h : ℝ in 𝓝 0, ‖h • a‖ ≤ 1 := by
    have hc : ContinuousAt (fun h : ℝ => ‖h • a‖) 0 := by fun_prop
    exact (hc.eventually (gt_mem_nhds (by simp : ‖(0 : ℝ) • a‖ < 1))).mono (fun _ hh => hh.le)
  apply (hasDerivAt_iff_tendsto_slope_zero
    (f := fun t : ℝ => weakPotential (χ.translate (t • a)))
    (f' := weakPotential (χ.directional a)) (x := 0)).mpr
  simp only [zero_add, zero_smul, Cutoff.translate_zero]
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm'
    (f := fun h : ℝ => h⁻¹ • (weakPotential (χ.translate (h • a)) - weakPotential χ) -
      weakPotential (χ.directional a))
    (t₀ := 𝓝[≠] (0 : ℝ))
    (a := fun h : ℝ => cutoffDifferenceConstant R M₂ M₃ * |h| * ‖a‖ ^ 2)
  · filter_upwards [self_mem_nhdsWithin, hstep.filter_mono nhdsWithin_le_nhds] with h hh hsmall
    have hne : h ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
    rw [← weakPotential_differenceError]
    exact (weakPotential_operatorNorm_le _).trans (cutoffBound_differenceError χ R M₂ M₃ hM₂ hM₃ hs h₂ h₃ a h hne hsmall)
  · have hc : Continuous (fun h : ℝ => cutoffDifferenceConstant R M₂ M₃ * |h| * ‖a‖ ^ 2) := by fun_prop
    simpa only [abs_zero, mul_zero, zero_mul] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Both cutoff positions contribute to the actual operator-norm derivative.
@isnad1 id=hasderiv.0h3v.s18.e78d83fb5881 from=translated src=- shape=c4b91418 vocab=93c6962a
-/
theorem mixedBoundaryOperator_hasDerivAt_zero (χ ψ : Cutoff) (a : Space) :
    HasDerivAt (fun t : ℝ => mixedBoundaryOperator (χ.translate (t • a)) (ψ.translate (t • a)))
      (mixedBoundaryOperator (χ.directional a) ψ + mixedBoundaryOperator χ (ψ.directional a)) 0 := by
  have h := (cutoffCurl_hasDerivAt_zero χ a).clm_comp (weakPotential_hasDerivAt_zero ψ a)
  simpa only [zero_smul, Cutoff.translate_zero, mixedBoundaryOperator] using h

/-- The corresponding differential commutator has the source's duality bound.
@isnad1 id=le.0h3v.s18.0f341965773e from=translated src=- shape=2105c122 vocab=ade81fca
-/
theorem mixedBoundaryOperator_derivative_norm_le (χ ψ : Cutoff) (a : Space) :
    ‖mixedBoundaryOperator (χ.directional a) ψ + mixedBoundaryOperator χ (ψ.directional a)‖ ≤
      cutoffBound (χ.directional a) * cutoffBound ψ + cutoffBound χ * cutoffBound (ψ.directional a) :=
  (norm_add_le _ _).trans (add_le_add (mixedBoundaryOperator_norm_le _ _) (mixedBoundaryOperator_norm_le _ _))

end EulerMeanBoundary
