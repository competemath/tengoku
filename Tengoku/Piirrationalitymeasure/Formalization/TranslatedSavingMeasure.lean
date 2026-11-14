import Tengoku.Piirrationalitymeasure.Formalization.SavingEndpoints
import Tengoku.Piirrationalitymeasure.Formalization.ParameterSavingContinuity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Continuity of the translated one-period measure in Lemma 6.1. -/

namespace PiIrrationality

open MeasureTheory Set Filter
open scoped Topology

/--
@isnad1 id=measurab.0h4v.s4.777af542521b from=translated src=- shape=fd71a95c vocab=882ad7e9
-/
theorem measurable_translatedSavingChi (a b c : ℝ) (z : ℝ × ℝ) :
    Measurable (translatedSavingChi a b c z) := by
  have hA : Measurable (fun u : ℝ => Int.fract (a * u + z.1 + 1 / 2)) := by fun_prop
  have hB : Measurable (fun u : ℝ => 2 * Int.fract (b * u + z.2)) := by fun_prop
  have hC : Measurable (fun u : ℝ => Int.fract (c * u)) := by fun_prop
  exact Measurable.ite (measurableSet_lt (hA.add hB) hC) measurable_const measurable_const

/--
@isnad1 id=eventual.4h4v.s7.6b31e2034bbf from=translated src=- shape=4417da9a vocab=78c8f113
-/
theorem ae_continuousAt_translatedSavingChi {a b c : ℝ} (z : ℝ × ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hq : a + 2 * b - c ≠ 0) :
    ∀ᵐ u : ℝ, ContinuousAt (fun v : ℝ × ℝ => translatedSavingChi a b c v u) z := by
  filter_upwards [ae_affine_ne_intCast ha (z.1 + 1 / 2),
    ae_affine_ne_intCast hb z.2, ae_affine_ne_intCast hc 0,
    ae_affine_ne_intCast hq (1 / 2 + z.1 + 2 * z.2)] with u hA hB hC hQ
  have hneq : Int.fract (a * u + z.1 + 1 / 2) + 2 * Int.fract (b * u + z.2) ≠
      Int.fract (c * u) := by
    intro he
    apply hQ (⌊a * u + z.1 + 1 / 2⌋ + 2 * ⌊b * u + z.2⌋ - ⌊c * u⌋)
    simp only [Int.fract] at he
    push_cast
    nlinarith only [he]
  have heq : (fun v : ℝ × ℝ => translatedSavingChi a b c v u) =ᶠ[𝓝 z]
      (fun _ => translatedSavingChi a b c z u) :=
    savingChi_eventuallyEq_of_continuousAt (by fun_prop) (by fun_prop) (by fun_prop)
      (by simpa only [add_assoc] using hA ⌊a * u + z.1 + 1 / 2⌋)
      (hB _) (by simpa only [add_zero] using hC ⌊c * u⌋) hneq
  exact continuousAt_const.congr_of_eventuallyEq heq

/--
@isnad1 id=continuo.4h3v.s6.aee292f7fc7d from=translated src=- shape=f1645c0e vocab=c6ebe476
-/
theorem continuous_translatedSavingMeasure {a b c : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hq : a + 2 * b - c ≠ 0) :
    Continuous (translatedSavingMeasure a b c) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => (1 : ℝ))
  · exact Eventually.of_forall (fun v => (measurable_translatedSavingChi a b c v).aestronglyMeasurable)
  · exact Eventually.of_forall fun v => Eventually.of_forall fun u _ => by
      rw [translatedSavingChi, Real.norm_eq_abs, abs_of_nonneg (savingChi_nonneg _ _ _)]
      exact savingChi_le_one _ _ _
  · exact intervalIntegrable_const
  · filter_upwards [ae_continuousAt_translatedSavingChi z ha hb hc hq] with u hu _
    exact hu

end PiIrrationality
