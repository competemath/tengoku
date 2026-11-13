import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Tengoku.Seed.MeasureTheory.Measure.HasOuterApproxClosed
import Tengoku.Seed.MeasureTheory.Integral.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Chebyshev measure as a cosine pushforward

The unnormalized arcsine measure has mass `π`. Cosine pushes Lebesgue measure
on `(0, π]` to this measure, so finite products admit the same change of variables.
-/

noncomputable section

open MeasureTheory Set Real

namespace Polynomial.Chebyshev

/-- The unnormalized Chebyshev measure is finite, including its integrable
endpoint singularities.
@isnad1 id=isfinite.0h0v.s2.a9e1aed805ae from=translated src=- shape=54c8eceb vocab=f0b64bf0
-/
instance isFiniteMeasure_measureT : IsFiniteMeasure measureT :=
  (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
    (integrable_measureT continuousOn_const)

/-- Cosine transports ordinary Lebesgue measure on `(0, π]` to the
unnormalized Chebyshev measure on `(-1,1]`.
@isnad1 id=measurep.0h0v.s4.88173a35a5a7 from=translated src=- shape=4bb68a79 vocab=b1529ac6
-/
theorem measurePreserving_cos_chebyshev :
    MeasurePreserving cos (volume.restrict (Ioc (0 : ℝ) π)) measureT := by
  refine ⟨continuous_cos.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map continuous_cos.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  rw [integral_measureT_eq_integral_cos, intervalIntegral.integral_of_le pi_pos.le]

/-- Coordinatewise cosine transports every finite product of angle measures
to the corresponding product of Chebyshev measures.
@isnad1 id=measurep.0h1v.s6.027765b63342 from=translated src=- shape=229c0176 vocab=d0a85c62
-/
theorem measurePreserving_pi_cos_chebyshev {ι : Type*} [Fintype ι] :
    MeasurePreserving (fun θ : ι → ℝ => fun i => cos (θ i))
      (Measure.pi (fun _ => volume.restrict (Ioc (0 : ℝ) π)))
      (Measure.pi (fun _ => measureT)) :=
  measurePreserving_pi _ _ (fun _ => measurePreserving_cos_chebyshev)

end Polynomial.Chebyshev
