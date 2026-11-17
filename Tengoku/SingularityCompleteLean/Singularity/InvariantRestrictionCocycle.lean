import Tengoku.SingularityCompleteLean.Singularity.RadonNikodymCoboundary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Restriction to an invariant measure carrier

Restricting both an absolutely continuous measure and its reference preserves
their derivative on the restricted space. For an invariant set, translation
commutes with restriction, so the actual logarithmic cocycle is unchanged.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Singularity

/-- Restricting both measures preserves their derivative on the restriction.
@isnad1 id=eventual.2h4v.s6.cf33618a7893 from=translated src=- shape=31acdb82 vocab=6e40bbf7
-/
theorem rnDeriv_restrict_both_of_absolutelyContinuous {B : Type*} [MeasurableSpace B]
    (ν m : Measure B) [SigmaFinite ν] [SigmaFinite m] (hac : ν ≪ m)
    {E : Set B} (hE : MeasurableSet E) :
    (ν.restrict E).rnDeriv (m.restrict E) =ᵐ[m.restrict E] ν.rnDeriv m := by
  have he : (m.restrict E).withDensity (ν.rnDeriv m) = ν.restrict E := by
    rw [← restrict_withDensity hE, Measure.withDensity_rnDeriv_eq _ _ hac]
  rw [← he]
  exact Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)

/-- A measure carried by E has the same density relative to the original
reference and its restriction, almost everywhere for the original measure.
@isnad1 id=eventual.3h4v.s6.700e6965d1fc from=translated src=- shape=e4a353b0 vocab=c1a3995a
-/
theorem rnDeriv_restrict_reference_of_conull {B : Type*} [MeasurableSpace B]
    (ν m : Measure B) [SigmaFinite ν] [SigmaFinite m] (hac : ν ≪ m)
    {E : Set B} (hE : MeasurableSet E) (hfull : ∀ᵐ ξ ∂ν, ξ ∈ E) :
    ν.rnDeriv (m.restrict E) =ᵐ[ν] ν.rnDeriv m := by
  have hr := rnDeriv_restrict_both_of_absolutelyContinuous ν m hac hE
  have hacE := hac.restrict E
  rw [Measure.restrict_eq_self_of_ae_mem hfull] at hr hacE
  exact hacE.ae_le hr

variable {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
  [MeasurableConstSMul Γ B]

/-- Translation commutes with restriction to an invariant measurable set.
@isnad1 id=eq.2h5v.s7.35dd72082783 from=translated src=- shape=8e4511ab vocab=f9294716
-/
theorem map_smul_invariant_restrict (m : Measure B) {E : Set B} (hE : MeasurableSet E)
    (hinv : ∀ g : Γ, (fun ξ : B => g • ξ) ⁻¹' E = E) (g : Γ) :
    Measure.map (fun ξ : B => g • ξ) (m.restrict E) =
      (Measure.map (fun ξ : B => g • ξ) m).restrict E := by
  rw [Measure.restrict_map (measurable_const_smul g) hE, hinv g]

/-- Restriction to an invariant set preserves quasi-invariance.
@isnad1 id=absolute.3h5v.s7.22a4992e08d9 from=translated src=- shape=94bd4bec vocab=b45d9527
-/
theorem invariant_restrict_quasiInvariant (m : Measure B) {E : Set B} (hE : MeasurableSet E)
    (hinv : ∀ g : Γ, (fun ξ : B => g • ξ) ⁻¹' E = E)
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) m ≪ m) (g : Γ) :
    Measure.map (fun ξ : B => g • ξ) (m.restrict E) ≪ m.restrict E := by
  rw [map_smul_invariant_restrict m hE hinv g]
  exact (hq g).restrict E

/-- The translated density is unchanged by invariant restriction.
@isnad1 id=eventual.3h5v.s7.53a88cf871cd from=translated src=- shape=ef0c4bb4 vocab=7059cd94
-/
theorem stationaryDensity_invariant_restrict (m : Measure B) [IsFiniteMeasure m]
    {E : Set B} (hE : MeasurableSet E)
    (hinv : ∀ g : Γ, (fun ξ : B => g • ξ) ⁻¹' E = E)
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) m ≪ m) (g : Γ) :
    stationaryDensity (m.restrict E) g =ᵐ[m.restrict E] stationaryDensity m g := by
  unfold stationaryDensity
  rw [map_smul_invariant_restrict m hE hinv g]
  exact rnDeriv_restrict_both_of_absolutelyContinuous _ _ (hq g) hE

/-- The actual logarithmic cocycle is unchanged on an invariant carrier.
@isnad1 id=eventual.3h5v.s7.f809c360394e from=translated src=- shape=ef0c4bb4 vocab=222355ae
-/
theorem stationaryLogCocycle_invariant_restrict (m : Measure B) [IsFiniteMeasure m]
    {E : Set B} (hE : MeasurableSet E)
    (hinv : ∀ g : Γ, (fun ξ : B => g • ξ) ⁻¹' E = E)
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) m ≪ m) (g : Γ) :
    stationaryLogCocycle (m.restrict E) g =ᵐ[m.restrict E] stationaryLogCocycle m g := by
  filter_upwards [stationaryDensity_invariant_restrict m hE hinv hq g⁻¹] with ξ hξ
  simp only [stationaryLogCocycle, stationaryRealDensity, hξ]

end Singularity
