import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicFourier
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_WhittakerCoefficient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 3 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.NumberField open _root_.NumberField.AdelicFourier open _root_.NumberField.AdelicBox open _root_.AutomorphicForm open _root_.IsDedekindDomain open _root_.MeasureTheory

open scoped Classical FourierTransform nonZeroDivisors

namespace NumberField
namespace AdelicFourier
export _root_.NumberField.AdelicFourier (fourierIntegral fourierIntegral_def)
namespace Ws25Fcoset
open _root_.NumberField.AdelicFourier open _root_.NumberField

variable {F : Type} [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in

/--
@isnad1 id=iff.0h3v.s9.4281ba2792f4 from=translated src=- shape=37473a9c vocab=fb03a12f
-/
theorem addChar_neg_eq_one_iff (x : FiniteAdeleRing (𝓞 F) F) : ψf (-x) = 1 ↔ ψf x = 1 := by
  have key : ψf (-x) * ψf x = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  constructor
  · intro h
    rw [h, one_mul] at key
    exact key
  · intro h
    rw [h, mul_one] at key
    exact key

/--
@isnad1 id=eq.0h5v.s9.a24fb1cd6e43 from=translated src=- shape=1df3ccf2 vocab=6612e1a4
-/
theorem setIntegral_image_add_left (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    (c : FiniteAdeleRing (𝓞 F) F) (B : Set (FiniteAdeleRing (𝓞 F) F)) :
    ∫ v in (fun b => c + b) '' B, g v ∂ν = ∫ b in B, g (c + b) ∂ν := by
  have h := (measurePreserving_add_left ν c).setIntegral_preimage_emb
    (measurableEmbedding_addLeft c) g ((fun b => c + b) '' B)
  rw [Set.preimage_image_eq B (add_right_injective c)] at h
  exact h.symm

/--
@isnad1 id=eq.3h5v.s11.3ce6444a3a53 from=translated src=- shape=c0e0c8ad vocab=46154fce
-/
theorem setIntegral_addChar_eq_ite {B : Set (FiniteAdeleRing (𝓞 F) F)} (hBm : MeasurableSet B)
    (hadd : ∀ ⦃x y⦄, x ∈ B → y ∈ B → x + y ∈ B) (hneg : ∀ ⦃x⦄, x ∈ B → -x ∈ B)
    (ξ : FiniteAdeleRing (𝓞 F) F) :
    ∫ z in B, ψf (ξ * z) ∂ν = if (∀ z ∈ B, ψf (ξ * z) = 1) then ((ν B).toReal : ℂ) else 0 := by
  split_ifs with h
  · rw [setIntegral_congr_fun hBm (fun z hz => h z hz), setIntegral_const]
    simp [Measure.real, Complex.real_smul]
  · have h' : ∃ c ∈ B, ψf (ξ * c) ≠ 1 := by
      by_contra h'
      exact h (fun z hz => by_contra fun hz' => h' ⟨z, hz, hz'⟩)
    obtain ⟨c, hcB, hc⟩ := h'
    have hpre : (fun z : FiniteAdeleRing (𝓞 F) F => c + z) ⁻¹' B = B := by
      ext z
      simp only [Set.mem_preimage]
      exact ⟨fun hz => by simpa using hadd (hneg hcB) hz, fun hz => hadd hcB hz⟩
    have hshift : ∫ z in B, ψf (ξ * (c + z)) ∂ν = ∫ z in B, ψf (ξ * z) ∂ν := by
      have h := (measurePreserving_add_left ν c).setIntegral_preimage_emb
        (measurableEmbedding_addLeft c) (fun z => ψf (ξ * z)) B
      rwa [hpre] at h
    have hkey : ψf (ξ * c) * ∫ z in B, ψf (ξ * z) ∂ν = ∫ z in B, ψf (ξ * z) ∂ν := by
      calc ψf (ξ * c) * ∫ z in B, ψf (ξ * z) ∂ν
          = ∫ z in B, ψf (ξ * c) * ψf (ξ * z) ∂ν := (integral_const_mul _ _).symm
        _ = ∫ z in B, ψf (ξ * (c + z)) ∂ν := by
            refine setIntegral_congr_fun hBm (fun z _ => ?_)
            rw [mul_add, AddChar.map_add_eq_mul]
        _ = ∫ z in B, ψf (ξ * z) ∂ν := hshift
    by_contra hI
    apply hc
    have h1 : ψf (ξ * c) * ∫ z in B, ψf (ξ * z) ∂ν = 1 * ∫ z in B, ψf (ξ * z) ∂ν := by
      rw [hkey, one_mul]
    exact mul_right_cancel₀ hI h1

/--
@isnad1 id=eq.0h6v.s11.979a0a016f10 from=translated src=- shape=79f1b8d1 vocab=60ec32a2
-/
theorem fourierIntegral_indicator_coset (c a w : FiniteAdeleRing (𝓞 F) F) :
    fourierIntegral ψf ν
        (((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1) w
      = ψf (-(c * w))
        * ((ν ((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)
        * (if ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψf (a * w * z) = 1 then 1 else 0) := by

  have hO_cpt : IsCompact (integralFiniteAdeles (𝓞 F) F) := isCompact_integralFiniteAdeles (K := F)
  have hB_cpt : IsCompact ((fun z => a * z) '' integralFiniteAdeles (𝓞 F) F) :=
    hO_cpt.image (continuous_const.mul continuous_id)
  have hBm : MeasurableSet ((fun z => a * z) '' integralFiniteAdeles (𝓞 F) F) :=
    hB_cpt.isClosed.measurableSet
  have hS_eq : (fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F
      = (fun b => c + b) '' ((fun z => a * z) '' integralFiniteAdeles (𝓞 F) F) :=
    (Set.image_image (fun b => c + b) (fun z => a * z) (integralFiniteAdeles (𝓞 F) F)).symm
  have hS_cpt : IsCompact ((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F) :=
    hO_cpt.image (continuous_const.add (continuous_const.mul continuous_id))
  have hSm : MeasurableSet ((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F) :=
    hS_cpt.isClosed.measurableSet
  have hadd : ∀ ⦃x y⦄, x ∈ (fun z => a * z) '' integralFiniteAdeles (𝓞 F) F →
      y ∈ (fun z => a * z) '' integralFiniteAdeles (𝓞 F) F →
      x + y ∈ (fun z => a * z) '' integralFiniteAdeles (𝓞 F) F := by
    rintro x y ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, rfl⟩
    exact ⟨z₁ + z₂, fun v => add_mem (hz₁ v) (hz₂ v), by simp only [mul_add]⟩
  have hneg : ∀ ⦃x⦄, x ∈ (fun z => a * z) '' integralFiniteAdeles (𝓞 F) F →
      -x ∈ (fun z => a * z) '' integralFiniteAdeles (𝓞 F) F := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨-z, fun v => neg_mem (hz v), by simp only [mul_neg]⟩

  have h1 : fourierIntegral ψf ν
        (((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1) w
      = ∫ v in (fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F, ψf (-(v * w)) ∂ν := by
    rw [fourierIntegral_def]
    have hrw : (fun v => ψf (-(v * w))
          * ((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1 v)
        = ((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F).indicator
            (fun v => ψf (-(v * w))) := by
      funext v
      by_cases hv : v ∈ (fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, Pi.one_apply, mul_one]
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, mul_zero]
    rw [hrw, integral_indicator hSm]

  have h2 : ∫ v in (fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F, ψf (-(v * w)) ∂ν
      = ψf (-(c * w))
        * ∫ b in (fun z => a * z) '' integralFiniteAdeles (𝓞 F) F, ψf (-w * b) ∂ν := by
    rw [hS_eq, setIntegral_image_add_left ν (fun v => ψf (-(v * w))) c, ← integral_const_mul]
    refine setIntegral_congr_fun hBm (fun b _ => ?_)
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring

  have h3 := setIntegral_addChar_eq_ite ν ψf hBm hadd hneg (-w)

  have h4 : (∀ b ∈ (fun z => a * z) '' integralFiniteAdeles (𝓞 F) F, ψf (-w * b) = 1)
      ↔ (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψf (a * w * z) = 1) := by
    constructor
    · intro h z hz
      have hb := h (a * z) ⟨z, hz, rfl⟩
      have e : -w * (a * z) = -(a * w * z) := by ring
      rw [e, addChar_neg_eq_one_iff] at hb
      exact hb
    · rintro h b ⟨z, hz, rfl⟩
      have e : -w * (a * z) = -(a * w * z) := by ring
      rw [e, addChar_neg_eq_one_iff]
      exact h z hz

  have h5 : ν ((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F)
      = ν ((fun z => a * z) '' integralFiniteAdeles (𝓞 F) F) := by
    rw [hS_eq, Set.image_add_left, measure_preimage_add]
  rw [h1, h2, h3, h5]
  by_cases hc : ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψf (a * w * z) = 1
  · rw [ite_eq_left (h4.mpr hc), ite_eq_left hc, mul_one]
  · rw [ite_eq_right (fun h => hc (h4.mp h)), ite_eq_right hc, mul_zero, mul_zero]

end NumberField.AdelicFourier.Ws25Fcoset

end

open _root_.NumberField open _root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply.NumberField open _root_.NumberField.AdelicFourier open _root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply.NumberField.AdelicFourier open _root_.NumberField.AdelicBox open _root_.AutomorphicForm open _root_.IsDedekindDomain open _root_.MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

open scoped Classical in
/--
@isnad1 id=eq.2h6v.s12.8e765e4c7d33 from=translated src=- shape=38abc4c7 vocab=4d010f76
-/
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf)
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) (w : FiniteAdeleRing (𝓞 F) F) :
    fourierIntegral ψf ν
        (((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator 1)
        w
      = ψf (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) k * w))
        * ((ν ((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)
        * (if ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
              ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w * z) = 1
            then 1 else 0) :=
  NumberField.AdelicFourier.Ws25Fcoset.fourierIntegral_indicator_coset ν ψf
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) w
