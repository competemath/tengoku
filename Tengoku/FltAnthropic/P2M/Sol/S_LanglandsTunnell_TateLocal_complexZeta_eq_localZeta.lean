import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchPlace
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.EqHaar
import Tengoku.Seed.LinearAlgebra.Complex.FiniteDimensional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_TateLocal_complexZeta_eq_localZeta.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_TateLocal_complexZeta_eq_localZeta

open MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace Metric
open scoped NNReal ENNReal Pointwise

namespace P7Rows
namespace ArchBridge

section ArchE1

/--
@isnad1 id=eq.0h1v.s7.837a47f93272 from=translated src=- shape=6a35519f vocab=70016a1b
-/
theorem distribHaarChar_complex_eq_nnnorm_sq (z : ℂˣ) :
    distribHaarChar ℂ z = ‖(z : ℂ)‖₊ ^ 2 := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (s := closedBall (0:ℂ) 1) (μ := volume)
    (measure_closedBall_pos volume (0:ℂ) one_pos).ne'
    measure_closedBall_lt_top.ne ?_
  rw [Units.smul_def, smul_closedBall' z.ne_zero, smul_zero, mul_one,
    show ‖(z:ℂ)‖ = ‖(z:ℂ)‖ * 1 from (mul_one _).symm,
    Measure.addHaar_closedBall_mul volume (0:ℂ) (norm_nonneg _) zero_le_one,
    Complex.finrank_real_complex]
  simp [ENNReal.ofReal_pow (norm_nonneg _), enorm_eq_nnnorm]

/--
@isnad1 id=eq.0h1v.s5.598a0775c5a3 from=translated src=- shape=2c770a6d vocab=6ed685d0
-/
theorem modulus_complex_eq_nnnorm_sq : ∀ (z : ℂ), modulus z = ‖z‖₊ ^ 2 := by
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [modulus_of_ne_zero hz, distribHaarChar_complex_eq_nnnorm_sq]
    simp

end ArchE1

section BR
variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K] [MeasurableSingletonClass K]

/--
@isnad1 id=eq.1h3v.s7.c0b90310b755 from=translated src=- shape=ce7f8d1d vocab=df34f76e
-/
theorem integral_mulMeasure (μ : Measure K) (F : K → ℂ)
    (hm : AEMeasurable (fun x : K => (modulus x)⁻¹) (μ.restrict {0}ᶜ)) :
    ∫ x, F x ∂(mulMeasure μ) = ∫ x in ({0}ᶜ : Set K), ((modulus x)⁻¹ : ℝ≥0) • F x ∂μ := by
  have hae : (fun x : K => ((modulus x : ℝ≥0∞))⁻¹)
      =ᵐ[μ.restrict {0}ᶜ] fun x : K => (((modulus x)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    refine (MeasureTheory.ae_restrict_iff' (MeasurableSet.singleton (0 : K)).compl).mpr ?_
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : x ≠ 0 := by simpa using hx
    show ((modulus x : ℝ≥0∞))⁻¹ = (((modulus x)⁻¹ : ℝ≥0) : ℝ≥0∞)
    rw [ENNReal.coe_inv (modulus_ne_zero hx0)]
  rw [mulMeasure, MeasureTheory.withDensity_congr_ae hae,
    integral_withDensity_eq_integral_smul₀ hm]

end BR

section BridgeComplex

/--
@isnad1 id=eq.1h4v.s6.866f938b4a11 from=translated src=- shape=98e897eb vocab=dbae6511
-/
theorem complexZeta_eq_localZeta_impl (μ : Measure ℂ) (f : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ)
    (hm : AEMeasurable (fun z : ℂ => (modulus z)⁻¹) (μ.restrict {0}ᶜ)) :
    complexZeta μ f χ s = localZeta μ f χ s := by
  rw [localZeta, integral_mulMeasure μ _ hm, complexZeta]
  rw [← MeasureTheory.integral_indicator (MeasurableSet.singleton (0:ℂ)).compl]
  congr 1
  funext z
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [Set.indicator_of_mem (show z ∈ ({0}ᶜ : Set ℂ) by simpa using hz)]
    have hmz : modulus z = ‖z‖₊ ^ 2 := modulus_complex_eq_nnnorm_sq z
    have hnz : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    simp only [NNReal.smul_def, Complex.real_smul, hmz]
    rw [show (f z * charExt χ z * (‖z‖ : ℂ) ^ (2 * s - 2) : ℂ)
          = (f z * charExt χ z) * ((‖z‖ : ℂ) ^ (2 * s - 2)) from by ring,
       show ((((‖z‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ) : ℂ) * (f z * charExt χ z * ((((‖z‖₊^2 : ℝ≥0) : ℝ) : ℂ)) ^ s)
          = (f z * charExt χ z) * (((((‖z‖₊^2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) : ℂ)
              * ((((‖z‖₊^2 : ℝ≥0) : ℝ) : ℂ)) ^ s) from by ring]
    congr 1
    have hsq : ((((‖z‖₊^2 : ℝ≥0) : ℝ) : ℂ)) = ((‖z‖ * ‖z‖ : ℝ) : ℂ) := by
      push_cast; ring
    have h1 : ((((‖z‖₊^2 : ℝ≥0) : ℝ) : ℂ))^s = (‖z‖ : ℂ)^((2:ℂ)*s) := by
      rw [hsq, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
        ← Complex.cpow_add _ _ hnz]; ring_nf
    have h2 : ((((‖z‖₊^2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) : ℂ) = (‖z‖ : ℂ)^(-(2:ℂ)) := by
      rw [show (-(2:ℂ)) = (-1) + (-1) from by ring, Complex.cpow_add _ _ hnz,
        Complex.cpow_neg_one]
      push_cast; ring
    rw [h1, h2, ← Complex.cpow_add _ _ hnz]
    ring_nf

end BridgeComplex

section BridgeReal

end BridgeReal

section HmDerived

/--
@isnad1 id=aemeasur.0h1v.s5.28057eacfed2 from=translated src=- shape=3c963df1 vocab=6b749699
-/
theorem hm_complex_any (μ : Measure ℂ) :
    AEMeasurable (fun z : ℂ => (modulus z)⁻¹) (μ.restrict {0}ᶜ) := by
  have heq : (fun z : ℂ => (modulus z)⁻¹) = fun z => (‖z‖₊ ^ 2)⁻¹ :=
    funext fun z => by rw [modulus_complex_eq_nnnorm_sq]
  rw [heq]
  exact ((measurable_nnnorm.pow_const 2).inv).aemeasurable

/--
@isnad1 id=eq.0h4v.s6.1e87c8efbb02 from=translated src=- shape=37a8975e vocab=9a1087d3
-/
theorem complexZeta_eq_localZeta_unc (μ : Measure ℂ) (f : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) :
    complexZeta μ f χ s = localZeta μ f χ s :=
  complexZeta_eq_localZeta_impl μ f χ s (hm_complex_any μ)

end HmDerived

end P7Rows.ArchBridge

/--
@isnad1 id=eq.0h4v.s6.1e87c8efbb02 from=translated src=- shape=37a8975e vocab=9a1087d3
-/
theorem solution (μ : Measure ℂ) (f : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) :
    complexZeta μ f χ s = localZeta μ f χ s :=
  P7Rows.ArchBridge.complexZeta_eq_localZeta_unc μ f χ s
