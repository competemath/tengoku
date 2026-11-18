import Tengoku.Seed.Analysis.Fourier.FourierTransform
import Tengoku.Seed.MeasureTheory.Measure.Haar.OfBasis
import Tengoku.FltAnthropic.Theorems.Thm_VectorFourier_ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MeasureTheory_exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=ex.6h6v.s9.0028765aa542 from=translated src=- shape=d027906d vocab=022586cf
-/
theorem solution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (_hB : B.Nondegenerate)
    (G : V → ℂ) (_hG : Integrable G μ)
    (U : Set V) (_hU : IsOpen U) (_hGU : ContinuousOn G U)
    (z₀ : V) (_hz₀ : z₀ ∈ U) (_h0 : G z₀ ≠ 0) :
    ∃ u : V, ∫ z, ((Real.fourierChar (B z u) : Circle) : ℂ) * G z ∂μ ≠ 0 := by
  classical
  by_contra hex
  have hall : ∀ u : V, ∫ z, ((Real.fourierChar (B z u) : Circle) : ℂ) * G z ∂μ = 0 :=
    fun u => Classical.byContradiction fun h => hex ⟨u, h⟩

  have hF : ∀ w : V, VectorFourier.fourierIntegral Real.fourierChar μ B G w = 0 := by
    intro w
    have e1 : (fun v : V => Real.fourierChar (-(B v w)) • G v)
        = fun z => ((Real.fourierChar (B z (-w)) : Circle) : ℂ) * G z := by
      funext z
      rw [(B z).map_neg w, Circle.smul_def, smul_eq_mul]
    show (∫ v, Real.fourierChar (-(B v w)) • G v ∂μ) = 0
    rw [e1]
    exact hall (-w)
  have hae : G =ᵐ[μ] 0 :=
    VectorFourier.ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero μ B _hB G _hG hF

  obtain ⟨O, hO, hUO⟩ := (continuousOn_iff'.mp _hGU) {0}ᶜ isOpen_compl_singleton
  have hz : z₀ ∈ O ∩ U := by
    rw [← hUO]
    exact ⟨_h0, _hz₀⟩
  have hpos : 0 < μ (O ∩ U) := (hO.inter _hU).measure_pos μ ⟨z₀, hz⟩
  have hnull : μ {z | ¬ G z = (0 : V → ℂ) z} = 0 := ae_iff.mp hae
  have hsub : O ∩ U ⊆ {z | ¬ G z = (0 : V → ℂ) z} := by
    intro z hz'
    rw [← hUO] at hz'
    exact hz'.1
  exact hpos.ne' (measure_mono_null hsub hnull)
