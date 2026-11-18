import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.Seed.MeasureTheory.Measure.Haar.DistribChar
import Tengoku.Seed.MeasureTheory.Measure.Haar.Unique
import Tengoku.FltAnthropic.Theorems.Thm_NumberField_AdeleRing_measurePreserving_mul_algebraMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdeleRing_distribHaarChar_algebraMap.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdeleRing_distribHaarChar_algebraMap

set_option autoImplicit false

open NumberField MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

namespace FltWs24
namespace AdelicModulusOneChar

/--
@isnad1 id=eq.1h3v.s7.00265c4e7568 from=translated src=- shape=dd786dec vocab=5630defd
-/
theorem addHaarScalarFactor_eq_one_of_integral_eq {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ' μ : Measure G) [μ.IsAddHaarMeasure] [IsFiniteMeasureOnCompacts μ'] [μ'.IsAddLeftInvariant]
    (h : ∀ f : G → ℝ, Continuous f → HasCompactSupport f → ∫ x, f x ∂μ' = ∫ x, f x ∂μ) :
    addHaarScalarFactor μ' μ = 1 := by
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_zero⟩ :
    ∃ f : C(G, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 0 ≠ 0 := exists_continuous_nonneg_pos 0
  have hpos : 0 < ∫ x, f x ∂μ :=
    f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_zero
  have h1 := integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport μ' μ f_cont f_comp
  rw [h f f_cont f_comp, integral_smul_nnreal_measure] at h1
  have h2 : (addHaarScalarFactor μ' μ : ℝ) = 1 := by
    rw [NNReal.smul_def, smul_eq_mul] at h1
    field_simp at h1
    linarith [h1, hpos]
  exact_mod_cast h2

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

/--
@isnad1 id=eq.0h2v.s11.6f8253c2900f from=translated src=- shape=ad9cd3ee vocab=05e0d30e
-/
theorem distribHaarChar_algebraMap_impl [MeasurableSpace 𝔸] [BorelSpace 𝔸] (a : Fˣ) :
    distribHaarChar 𝔸 (Units.map (algebraMap F 𝔸).toMonoidHom a) = 1 := by
  set u : 𝔸ˣ := Units.map (algebraMap F 𝔸).toMonoidHom a with hu

  let μ : Measure 𝔸 := Measure.addHaar
  haveI : μ.Regular := by
    show (Measure.addHaar : Measure 𝔸).Regular
    unfold Measure.addHaar; infer_instance

  have hmp : MeasurePreserving (fun x => (u : 𝔸) * x) μ μ :=
    NumberField.AdeleRing.measurePreserving_mul_algebraMap F μ (a : F) a.ne_zero

  have hsf : addHaarScalarFactor (DomMulAct.mk u⁻¹ • μ : Measure 𝔸) μ = 1 := by
    refine addHaarScalarFactor_eq_one_of_integral_eq _ μ fun f hf hfc => ?_
    rw [integral_domSMul]
    simp only [Equiv.symm_apply_apply, inv_inv]
    have hme : MeasurableEmbedding (fun x => (u : 𝔸) * x) :=
      (ContinuousAddEquiv.mulLeft u).toHomeomorph.measurableEmbedding
    exact hmp.integral_comp hme f
  have hinv : distribHaarChar 𝔸 u⁻¹ = 1 := by
    rw [← addHaarScalarFactor_smul_eq_distribHaarChar μ u⁻¹]
    exact hsf
  rwa [map_inv (distribHaarChar 𝔸) u, inv_eq_one] at hinv

end FltWs24.AdelicModulusOneChar

open NumberField

/--
@isnad1 id=eq.0h2v.s11.6f8253c2900f from=translated src=- shape=ad9cd3ee vocab=05e0d30e
-/
theorem solution (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (a : Fˣ) :
    MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F)
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1 :=
  FltWs24.AdelicModulusOneChar.distribHaarChar_algebraMap_impl F a
