import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.OscillatoryReductionSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The exact oscillatory action on integrable inputs

The global annular amplitude bounds decay geometrically with the height.
They justify the actual height series and its high-pass integral for every
integrable input, without compact-support or convergence assumptions.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuadraticCarleson
namespace OscillatoryReduction

/--
@isnad1 id=eq.1h2v.s5.c1cfc39e47e9 from=translated src=- shape=87d9f704 vocab=0e204e89
-/
theorem fixedHeightRadius_eq_zero_mul_pow (lam : ℝ) (hlam : lam ≠ 0) (r : ℕ) :
    fixedHeightRadius lam r hlam = fixedHeightRadius lam 0 hlam * (2 : ℝ) ^ r := by
  unfold fixedHeightRadius
  rw [oscillatoryScaleIndex_eq_add]
  rw [show oscillatoryScaleIndex lam 0 hlam + (r : ℤ) - 1 =
    (oscillatoryScaleIndex lam 0 hlam - 1) + (r : ℤ) by ring]
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]

/--
@isnad1 id=summable.1h1v.s5.48a6122a5f0e from=translated src=- shape=3e167d61 vocab=f643e858
-/
theorem summable_fixedHeightKernelBounds (lam : ℝ) (hlam : lam ≠ 0) :
    Summable (fun r : ℕ ↦ (2 * positiveDyadicAmplitudeBound) /
      fixedHeightRadius lam r hlam) := by
  have hs : Summable (fun r : ℕ ↦ (1 / 2 : ℝ) ^ r) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  apply (hs.mul_left ((2 * positiveDyadicAmplitudeBound) /
    fixedHeightRadius lam 0 hlam)).congr
  intro r
  rw [fixedHeightRadius_eq_zero_mul_pow lam hlam r, div_pow]
  simp only [one_pow]
  ring

/--
@isnad1 id=summable.2h3v.s6.ab8f45ed12d4 from=translated src=- shape=0b8adcd1 vocab=97a86785
-/
theorem summable_integral_norm_fixedHeight (lam : ℝ) (hlam : lam ≠ 0)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Summable (fun r : ℕ ↦ ∫ y,
      ‖fixedHeightQuadraticKernel lam r hlam (x - y) * f y‖) := by
  apply Summable.of_nonneg_of_le (fun r ↦ integral_nonneg (fun y ↦ norm_nonneg _))
    (f := fun r ↦ ((2 * positiveDyadicAmplitudeBound) /
      fixedHeightRadius lam r hlam) * ∫ y, ‖f y‖)
  · intro r
    calc
      _ ≤ ∫ y, ((2 * positiveDyadicAmplitudeBound) /
          fixedHeightRadius lam r hlam) * ‖f y‖ := by
        apply integral_mono
        · exact (PositiveLowFullEstimate.integrable_fixedHeightQuadraticKernel_mul_locallyIntegrable
            hf.locallyIntegrable r lam hlam x).norm
        · exact hf.norm.const_mul _
        · intro y
          dsimp only
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (norm_fixedHeightQuadraticKernel_le lam r hlam (x-y))
            (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  · exact (summable_fixedHeightKernelBounds lam hlam).mul_right _

/--
@isnad1 id=hassum.2h3v.s7.da4d5cc4f181 from=translated src=- shape=44c43704 vocab=6a0b9d75
-/
theorem hasSum_oscillatoryIntegrals_of_integrable (lam : ℝ) (hlam : lam ≠ 0)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    HasSum (fun r : ℕ ↦ ∫ t, f (x - t) *
      (dyadicPsi (oscillatoryScaleIndex lam r hlam) t : ℂ) * phase (lam * t ^ 2))
      (∫ y, highPassKernel lam hlam (x - y) * f y) := by
  have hs := hasSum_integral_of_summable_integral_norm
    (fun r ↦ PositiveLowFullEstimate.integrable_fixedHeightQuadraticKernel_mul_locallyIntegrable
      hf.locallyIntegrable r lam hlam x)
    (summable_integral_norm_fixedHeight lam hlam hf x)
  have hp (y : ℝ) : (∑' r : ℕ, fixedHeightQuadraticKernel lam r hlam (x - y) * f y) =
      highPassKernel lam hlam (x - y) * f y :=
    ((hasSum_oscillatoryKernels lam hlam (x - y)).mul_right (f y)).tsum_eq
  simp_rw [hp] at hs
  exact hs.congr_fun (fun r ↦
    (fixedHeightQuadraticKernel_integral_eq_paper r lam hlam f x).symm)

/--
@isnad1 id=eq.2h3v.s6.123dd0ad2d24 from=translated src=- shape=1caf5176 vocab=dd36b027
-/
theorem paperOscillatoryAction_eq_integral_of_integrable (lam : ℝ) (hlam : lam ≠ 0)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    paperOscillatoryAction lam hlam f x =
      ∫ y, highPassKernel lam hlam (x - y) * f y :=
  (hasSum_oscillatoryIntegrals_of_integrable lam hlam hf x).tsum_eq

/--
@isnad1 id=integrab.2h3v.s6.922ea58267d7 from=translated src=- shape=d91ef5bb vocab=3f1b1fae
-/
theorem integrable_highPassKernel_mul (lam : ℝ) (hlam : lam ≠ 0)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Integrable (fun y ↦ highPassKernel lam hlam (x - y) * f y) := by
  exact hf.bdd_mul
    ((measurable_highPassKernel lam hlam).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y ↦ highPassKernel_norm_le lam hlam (x-y))

/-- Linearity of the genuine height series follows from its proved bounded
high-pass integral representation.
@isnad1 id=eq.3h4v.s7.23de0dec6423 from=translated src=- shape=a1f6db11 vocab=bb9bfcc1
-/
theorem paperOscillatoryAction_add_of_integrable (lam : ℝ) (hlam : lam ≠ 0)
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    paperOscillatoryAction lam hlam (f + g) x =
      paperOscillatoryAction lam hlam f x + paperOscillatoryAction lam hlam g x := by
  rw [paperOscillatoryAction_eq_integral_of_integrable lam hlam (hf.add hg),
    paperOscillatoryAction_eq_integral_of_integrable lam hlam hf,
    paperOscillatoryAction_eq_integral_of_integrable lam hlam hg]
  simp only [Pi.add_apply, mul_add]
  exact integral_add (integrable_highPassKernel_mul lam hlam hf x)
    (integrable_highPassKernel_mul lam hlam hg x)

end OscillatoryReduction
end QuadraticCarleson
