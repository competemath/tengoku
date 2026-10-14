module

public import Tengoku

public section

open scoped ENNReal

namespace MeasureTheory
variable {Ω : Type*} {mΩ₀ mΩ : MeasurableSpace Ω} {P : Measure[mΩ₀] Ω} {X Y : Ω → ℝ≥0∞}

/--
@isnad1 id=eventual.1h5v.s6.6fe2bf4a1188 from=translated src=- shape=3ce5defe vocab=466aa1ad
-/
lemma tsub_add_cancel_of_eventuallyLE (hYX : Y ≤ᵐ[P] X) : X - Y + Y =ᵐ[P] X :=
  hYX.mono fun ω hω ↦ by simpa [Pi.sub_apply, Pi.add_apply] using tsub_add_cancel_of_le hω

/--
@isnad1 id=eventual.3h6v.s7.253fe99b9c8a from=translated src=- shape=36d7877e vocab=ca0548f6
-/
lemma condLExp_sub (hY : AEMeasurable[mΩ₀] Y P)
    (hYX : Y ≤ᵐ[P] X) (hY_ne_top : ∀ᵐ ω ∂P, P⁻[Y | mΩ] ω ≠ ∞) :
    P⁻[X - Y | mΩ] =ᵐ[P] P⁻[X | mΩ] - P⁻[Y | mΩ] := by
  have hsum : P⁻[X | mΩ] =ᵐ[P] P⁻[X - Y | mΩ] + P⁻[Y | mΩ] :=
    (condLExp_congr_ae (tsub_add_cancel_of_eventuallyLE hYX).symm).trans (condLExp_add_right _ hY)
  filter_upwards [hY_ne_top, hsum] with ω hω hx
  exact (ENNReal.sub_eq_of_eq_add_rev hω (by simpa [add_comm] using hx)).symm

/--
@isnad1 id=eventual.2h6v.s6.0db31e5e8619 from=translated src=- shape=f2056490 vocab=b5a12940
-/
theorem condLExp_condLExp_of_le {mΩ₁ mΩ₂ : MeasurableSpace Ω} (hm₁₂ : mΩ₁ ≤ mΩ₂)
    (hm₂ : mΩ₂ ≤ mΩ₀) (P : Measure[mΩ₀] Ω) [SigmaFinite (P.trim hm₂)] (X : Ω → ℝ≥0∞) :
    P⁻[P⁻[X | mΩ₂]|mΩ₁] =ᵐ[P] P⁻[X | mΩ₁] := by
  have hm₁ : mΩ₁ ≤ mΩ₀ := hm₁₂.trans hm₂
  by_cases hσ : SigmaFinite (P.trim hm₁)
  swap; · simp_rw [condLExp_of_not_sigmaFinite hm₁ hσ]; rfl
  refine ae_eq_condLExp (Y := P⁻[P⁻[X | mΩ₂]|mΩ₁]) hm₁ P X (measurable_condLExp _ _ _) fun s hs ↦ ?_
  rw [setLIntegral_condLExp hm₁ P _ hs, setLIntegral_condLExp hm₂ P X (hm₁₂ s hs)]

end MeasureTheory
