import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.Seed.MeasureTheory.Measure.Haar.Unique

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

namespace FltWs24
namespace AdelicModulusOne

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

theorem isAddFundamentalDomain_preimage_mul [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (μ : Measure 𝔸) (a : F) (ha : a ≠ 0) :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x => algebraMap F 𝔸 a * x) ⁻¹' AdelicBox.adelicBox F) μ := by
  have hm : ‹MeasurableSpace 𝔸› = AdelicHaar.adeleBorel (𝓞 F) F := BorelSpace.measurable_eq
  subst hm
  letI : MeasurableSpace 𝔸 := AdelicHaar.adeleBorel (𝓞 F) F
  refine IsAddFundamentalDomain.mk' ?_ fun x => ?_
  · exact ((AdelicBox.measurableSet_adelicBox F).preimage
      (measurable_const_mul (algebraMap F 𝔸 a))).nullMeasurableSet
  · obtain ⟨k, hk, huniq⟩ :=
      AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F (algebraMap F 𝔸 a * x)
    refine ⟨⟨algebraMap F 𝔸 (a⁻¹ * k), a⁻¹ * k, rfl⟩, ?_, ?_⟩
    · show algebraMap F 𝔸 a * (algebraMap F 𝔸 (a⁻¹ * k) + x) ∈ AdelicBox.adelicBox F
      rwa [mul_add, ← map_mul, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    · rintro ⟨_, k', rfl⟩ hk'
      have hk'B : algebraMap F 𝔸 (a * k') + algebraMap F 𝔸 a * x ∈ AdelicBox.adelicBox F := by
        have h : algebraMap F 𝔸 a * (algebraMap F 𝔸 k' + x) ∈ AdelicBox.adelicBox F := hk'
        rwa [mul_add, ← map_mul] at h
      have hak : a * k' = k := huniq (a * k') hk'B
      have hk'eq : k' = a⁻¹ * k := by
        rw [← hak, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      subst hk'eq
      rfl

end FltWs24.AdelicModulusOne

open NumberField

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) (a : F) (ha : a ≠ 0) :
    MeasureTheory.IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) ⁻¹' AdelicBox.adelicBox F) μ :=
  FltWs24.AdelicModulusOne.isAddFundamentalDomain_preimage_mul F μ a ha
