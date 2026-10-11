module
public import Tengoku.Causalean.Causalean.Stat.Privacy.LaplaceMechanism

/-!
# Centered Laplace mean

Reflection invariance and the exact zero mean of the existing density-defined
Laplace measure. Absolute integrability is reused from the primary library.
This file is independent of the second-moment proof chain.
-/

public section

namespace Causalean.Stat.Privacy

open MeasureTheory Causalean.Stat.Privacy

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a centered
Laplace draw has an integrable signed value](goal).
@isnad1 id=integrab.1h1v.s5.d0e3c38625c1 from=translated src=- shape=3c93f67d vocab=5b6b7a18
-/
theorem laplaceMeasure_integrable_id (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => x) (laplaceMeasure b) := by
  exact (laplaceMeasure_integrable_abs b hb).mono' (by fun_prop)
    (ae_of_all _ fun x => by simp)

/-- At [a real scale](hyp:b), [reflecting the centered Laplace measure about zero
preserves that measure](goal).

Prove this directly from `laplaceMeasure`, `abs_neg`, and the invariance of
Lebesgue measure under negation. No distribution moment is assumed.
@isnad1 id=eq.0h1v.s4.bfa40fea7fb3 from=translated src=- shape=ecae0a8b vocab=fc6e0b0e
-/
theorem laplaceMeasure_map_neg (b : ℝ) :
    (laplaceMeasure b).map (fun x : ℝ => -x) = laplaceMeasure b := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, laplaceMeasure,
    withDensity_apply _ (hs.preimage (by fun_prop)), withDensity_apply _ hs]
  calc
    (∫⁻ x in (fun x : ℝ => -x) ⁻¹' s, ENNReal.ofReal (laplacePDF b x)) =
        ∫⁻ x in (fun x : ℝ => -x) ⁻¹' s, ENNReal.ofReal (laplacePDF b (-x)) := by
      simp only [laplacePDF, abs_neg]
    _ = ∫⁻ x in s, ENNReal.ofReal (laplacePDF b x)
        ∂(volume.map (fun x : ℝ => -x)) :=
      (setLIntegral_map hs (measurable_laplacePDF b).ennreal_ofReal
        (by fun_prop)).symm
    _ = _ := by rw [Measure.map_neg_eq_self]

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a centered
Laplace draw has mean zero](goal).

Use reflection invariance to equate the mean with its negative. Integrability
is supplied separately by `laplaceMeasure_integrable_id`.
@isnad1 id=eq.1h1v.s5.74c7f40858f7 from=translated src=- shape=8c8c1771 vocab=f8b2462f
-/
theorem laplaceMeasure_integral_id (b : ℝ) (hb : 0 < b) :
    ∫ x : ℝ, x ∂laplaceMeasure b = 0 := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x)
      ((laplaceMeasure b).map (fun x : ℝ => -x)) := by
    rw [laplaceMeasure_map_neg b]
    exact (laplaceMeasure_integrable_id b hb).aestronglyMeasurable
  have hreflection := integral_map (μ := laplaceMeasure b)
    (φ := fun x : ℝ => -x) (by fun_prop) hmeas
  rw [laplaceMeasure_map_neg b, integral_neg] at hreflection
  linarith

end Causalean.Stat.Privacy
