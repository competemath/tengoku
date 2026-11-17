import Tengoku.SingularityCompleteLean.Singularity.FourierReduction
import Tengoku.Seed.MeasureTheory.Function.Holder
import Tengoku.Seed.MeasureTheory.Group.Integral
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fourier translation covariance on L²

We first verify covariance on Schwartz functions, then extend by density and
continuity. All equalities involving representatives are almost-everywhere.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace Singularity

/-- The phase for translation by a in Mathlib's cycles-per-unit convention.-/
def translationPhase (a ξ : ℝ) : ℂ := Real.fourierChar (-a * ξ)

/--
@isnad1 id=continuo.0h1v.s4.9177a1348621 from=translated src=- shape=9bb0b988 vocab=8bf4c260
-/
theorem translationPhase_continuous (a : ℝ) : Continuous (translationPhase a) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_const.mul continuous_id))

/--
@isnad1 id=eq.0h2v.s4.0f9792ef2bf5 from=translated src=- shape=18e50d40 vocab=b9131ea7
-/
theorem translationPhase_norm (a ξ : ℝ) : ‖translationPhase a ξ‖ = 1 := Circle.norm_coe _

/-- The phase viewed as an L-infinity function.-/
def translationPhaseLinf (a : ℝ) : Lp ℂ ⊤ (volume : Measure ℝ) :=
  (memLp_top_of_bound (translationPhase_continuous a).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun ξ => (translationPhase_norm a ξ).le))).toLp
      (translationPhase a)

/-- Multiplication by the phase is a bounded operator on L².-/
def frequencyModulation (a : ℝ) : RealLineL2 →L[ℂ] RealLineL2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2 (translationPhaseLinf a)

/-- Its pointwise formula, interpreted almost everywhere.
@isnad1 id=eventual.0h2v.s12.7e7896a8eecf from=translated src=- shape=31244194 vocab=f1f6cb8b
-/
theorem frequencyModulation_apply_ae (a : ℝ) (f : RealLineL2) :
    (frequencyModulation a f : ℝ → ℂ) =ᵐ[volume] fun ξ => translationPhase a ξ * f ξ := by
  have hp : (translationPhaseLinf a : ℝ → ℂ) =ᵐ[volume] translationPhase a := MemLp.coeFn_toLp _
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (translationPhaseLinf a) f, hp]
    with ξ hξ hpξ
  exact hξ.trans (by rw [hpξ]; rfl)

/-- Translation on the actual Lebesgue L² space.-/
def realTranslation (a : ℝ) : RealLineL2 →ₗᵢ[ℂ] RealLineL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun t : ℝ => t - a) (measurePreserving_sub_right volume a)

/--
@isnad1 id=eventual.0h2v.s11.50bc0d8f40b3 from=translated src=- shape=ba07e249 vocab=4698809c
-/
theorem realTranslation_apply_ae (a : ℝ) (f : RealLineL2) :
    (realTranslation a f : ℝ → ℂ) =ᵐ[volume] fun t => f (t - a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume a)

/-- Translation commutes with the inclusion of Schwartz functions in L².
@isnad1 id=eq.0h2v.s11.38ca7807779d from=translated src=- shape=21e38e0f vocab=c3007581
-/
theorem realTranslation_schwartz (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    realTranslation a (f.toLp 2) = (f.compSubConstCLM ℂ a).toLp 2 := by
  apply Lp.ext
  have hf := (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae
    (f.coeFn_toLp 2 volume)
  filter_upwards [realTranslation_apply_ae a (f.toLp 2), hf,
    (f.compSubConstCLM ℂ a).coeFn_toLp 2] with t ht hf ht'
  exact ht.trans (hf.trans ht'.symm)

/-- The ordinary Fourier integral gives covariance for Schwartz functions.
@isnad1 id=eq.0h3v.s10.feafc704d863 from=translated src=- shape=3a4389c1 vocab=ce8426e6
-/
theorem schwartz_fourier_translation (a : ℝ) (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    (𝓕 (f.compSubConstCLM ℂ a)) ξ = translationPhase a ξ * (𝓕 f) ξ := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ ℝ) (f : ℝ → ℂ) (-a)) ξ
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
    (fun x => f (x - a)) ξ = (Real.fourierChar (-a * ξ) : ℂ) *
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) (f : ℝ → ℂ) ξ
  simpa [Function.comp_def, sub_eq_add_neg, Circle.smul_def, real_inner_comm, mul_comm] using h

/-- L² covariance follows by density, with no integrability assumption on f.
@isnad1 id=eq.0h2v.s14.fd3dc6eaf478 from=translated src=- shape=0cf7fe62 vocab=92e75306
-/
theorem fourier_realTranslation (a : ℝ) (f : RealLineL2) :
    Lp.fourierTransformₗᵢ ℝ ℂ (realTranslation a f) =
      frequencyModulation a (Lp.fourierTransformₗᵢ ℝ ℂ f) := by
  let p : RealLineL2 → Prop := fun f =>
    Lp.fourierTransformₗᵢ ℝ ℂ (realTranslation a f) =
      frequencyModulation a (Lp.fourierTransformₗᵢ ℝ ℂ f)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp (realTranslation a).continuous)
      ((frequencyModulation a).continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous)
  intro g
  change 𝓕 (realTranslation a (g.toLp 2)) = frequencyModulation a (𝓕 (g.toLp 2))
  rw [realTranslation_schwartz, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (g.compSubConstCLM ℂ a)).coeFn_toLp 2,
    frequencyModulation_apply_ae a ((𝓕 g).toLp 2), (𝓕 g).coeFn_toLp 2]
    with ξ hleft hright hg
  rw [hleft, hright, hg]
  exact schwartz_fourier_translation a g ξ

/-- The Fourier character is trivial on integer frequencies.
@isnad1 id=eq.0h1v.s6.23ae763dd4bb from=translated src=- shape=b3c55159 vocab=e684d0c2
-/
theorem fourierChar_integer (n : ℤ) : (Real.fourierChar (n : ℝ) : ℂ) = 1 := by
  rw [Real.fourierChar_apply]
  convert Complex.exp_int_mul_two_pi_mul_I n using 1
  congr 1
  push_cast
  ring

/-- Translation by n/q produces the same phase on adjacent bands of width q.
@isnad1 id=eq.1h4v.s6.201a5e72b31d from=translated src=- shape=f4b5127d vocab=e02edbbf
-/
theorem translationPhase_lattice {q : ℝ} (hq : q ≠ 0) (n : ℤ) (l : ℕ) (ω : ℝ) :
    translationPhase ((n : ℝ) / q) (ω + l * q) = translationPhase ((n : ℝ) / q) ω := by
  have heq : -((n : ℝ) / q) * (ω + l * q) =
      -((n : ℝ) / q) * ω + ((-n * (l : ℤ) : ℤ) : ℝ) := by
    push_cast
    field_simp
    ring
  unfold translationPhase
  rw [heq, AddChar.map_add_eq_mul, Circle.coe_mul, fourierChar_integer, mul_one]

end Singularity
