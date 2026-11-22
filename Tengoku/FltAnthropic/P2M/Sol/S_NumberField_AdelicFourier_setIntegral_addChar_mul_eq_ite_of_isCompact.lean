import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicFourier
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_WhittakerCoefficient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.NumberField open _root_.NumberField.AdelicFourier open _root_.NumberField.AdelicBox open _root_.AutomorphicForm open _root_.IsDedekindDomain open _root_.MeasureTheory

open scoped Classical FourierTransform nonZeroDivisors

namespace NumberField
namespace AdelicFourier
namespace Ws25OrthK
open _root_.NumberField.AdelicFourier open _root_.NumberField

variable {F : Type} [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)
  (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))

omit [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in

/--
@isnad1 id=eq.1h5v.s10.b678d5dd4a37 from=translated src=- shape=ffd71044 vocab=d7e8ad24
-/
theorem setIntegral_comp_add_left_eq [MeasurableAdd (FiniteAdeleRing (𝓞 F) F)]
    (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    {c : FiniteAdeleRing (𝓞 F) F} (hc : c ∈ K) :
    ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), g (c + z) ∂ν
      = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), g z ∂ν := by
  have hpre : (fun z : FiniteAdeleRing (𝓞 F) F => c + z) ⁻¹' (K : Set (FiniteAdeleRing (𝓞 F) F))
      = (K : Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext z
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun h => by simpa using K.add_mem (K.neg_mem hc) h, fun h => K.add_mem hc h⟩
  have h := (measurePreserving_add_left ν c).setIntegral_preimage_emb
    (measurableEmbedding_addLeft c) g (K : Set (FiniteAdeleRing (𝓞 F) F))
  rwa [hpre] at h

/--
@isnad1 id=eq.2h6v.s11.5f5e125106a6 from=translated src=- shape=0a3755ba vocab=d05f47d2
-/
theorem char_mul_setIntegral_eq (hKm : MeasurableSet (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (ξ : FiniteAdeleRing (𝓞 F) F) {c : FiniteAdeleRing (𝓞 F) F} (hc : c ∈ K) :
    ψf (ξ * c) * ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
      = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν := by
  calc ψf (ξ * c) * ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
      = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * c) * ψf (ξ * z) ∂ν :=
        (integral_const_mul _ _).symm
    _ = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * (c + z)) ∂ν := by
        refine setIntegral_congr_fun hKm (fun z _ => ?_)
        rw [mul_add, AddChar.map_add_eq_mul]
    _ = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν :=
        setIntegral_comp_add_left_eq ν K (fun z => ψf (ξ * z)) hc

/--
@isnad1 id=eq.1h5v.s11.cf0685d8f3b3 from=translated src=- shape=34bb12fc vocab=6dc4a855
-/
theorem setIntegral_addChar_mul_eq_ite (hK : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (ξ : FiniteAdeleRing (𝓞 F) F) :
    ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
      = if (∀ z ∈ K, ψf (ξ * z) = 1) then ((ν K).toReal : ℂ) else 0 := by
  have hKm : MeasurableSet (K : Set (FiniteAdeleRing (𝓞 F) F)) := hK.isClosed.measurableSet
  split_ifs with h
  · rw [setIntegral_congr_fun hKm (fun z hz => h z hz), setIntegral_const]
    simp [Measure.real, Complex.real_smul]
  · have h' : ∃ c ∈ K, ψf (ξ * c) ≠ 1 := by
      by_contra h'
      exact h (fun z hz => by_contra fun hz' => h' ⟨z, hz, hz'⟩)
    obtain ⟨c, hcK, hc⟩ := h'
    have hkey := char_mul_setIntegral_eq ν ψf K hKm ξ hcK
    by_contra hI
    apply hc
    have h1 : ψf (ξ * c) * ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
        = 1 * ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν := by
      rw [hkey, one_mul]
    exact mul_right_cancel₀ hI h1

end NumberField.AdelicFourier.Ws25OrthK

end

open _root_.NumberField open _root_.P2MW.S_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact.NumberField open _root_.NumberField.AdelicFourier open _root_.P2MW.S_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact.NumberField.AdelicFourier open _root_.NumberField.AdelicBox open _root_.AutomorphicForm open _root_.IsDedekindDomain open _root_.MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

/--
@isnad1 id=eq.1h5v.s11.cf0685d8f3b3 from=translated src=- shape=34bb12fc vocab=6dc4a855
-/
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) (hK : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (ξ : FiniteAdeleRing (𝓞 F) F) :
    ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
      = if (∀ z ∈ K, ψf (ξ * z) = 1) then ((ν K).toReal : ℂ) else 0 :=
  NumberField.AdelicFourier.Ws25OrthK.setIntegral_addChar_mul_eq_ite ν ψf K hK ξ
