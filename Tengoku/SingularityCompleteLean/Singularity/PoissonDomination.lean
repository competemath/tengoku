import Tengoku.SingularityCompleteLean.Singularity.PoissonMobius
import Tengoku.SingularityCompleteLean.Singularity.BoundaryMeasureAnalysis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transport of bounded densities relative to Poisson measures

A measure bounded by B times the Poisson measure at z remains bounded by the
same B times the Poisson measure at g·z after a Möbius pushforward. The resulting
real Radon–Nikodym bound is exactly the input needed by boundary-measure analysis.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal MatrixGroups UpperHalfPlane

namespace Singularity

/-- A real multiple of a Poisson measure has the expected real density.-/
theorem smul_halfPlanePoissonMeasure (x y : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ENNReal.ofReal B • halfPlanePoissonMeasure x y =
      volume.withDensity (fun u => ENNReal.ofReal (B * halfPlanePoisson x y u)) := by
  rw [halfPlanePoissonMeasure, ← withDensity_smul _ (measurable_halfPlanePoisson x y).ennreal_ofReal]
  congr 1
  funext u
  exact (ENNReal.ofReal_mul hB).symm

/-- Domination by the Poisson measure implies absolute continuity with
respect to Lebesgue measure in the real boundary chart.-/
theorem absolutelyContinuous_of_poisson_bound (ν : Measure ℝ) (z : ℍ) (B : ℝ)
    (hbound : ν ≤ ENNReal.ofReal B • poissonBoundaryMeasure z) : ν ≪ volume :=
  (Measure.absolutelyContinuous_of_le_smul hbound).trans
    (halfPlanePoissonMeasure_measureClass z.re z.im_pos).1

/-- A measure bound yields the corresponding a.e. real Radon–Nikodym bound.-/
theorem rnDeriv_le_poisson_of_measure_bound (ν : Measure ℝ) [SigmaFinite ν]
    (z : ℍ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ν ≤ ENNReal.ofReal B • poissonBoundaryMeasure z) :
    ∀ᵐ u ∂volume, (ν.rnDeriv volume u).toReal ≤ B * halfPlanePoisson z.re z.im u := by
  have hle : ν ≤ volume.withDensity (fun u => ENNReal.ofReal (B * halfPlanePoisson z.re z.im u)) := by
    simpa only [poissonBoundaryMeasure, smul_halfPlanePoissonMeasure z.re z.im hB] using hbound
  have h := ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν volume)
    (g := fun u => ENNReal.ofReal (B * halfPlanePoisson z.re z.im u)) (fun s hs _ => by
      calc
        ∫⁻ u in s, ν.rnDeriv volume u ∂volume ≤ ν s := Measure.setLIntegral_rnDeriv_le s
        _ ≤ (volume.withDensity (fun u => ENNReal.ofReal (B * halfPlanePoisson z.re z.im u))) s := hle s
        _ = ∫⁻ u in s, ENNReal.ofReal (B * halfPlanePoisson z.re z.im u) ∂volume := withDensity_apply _ hs)
  filter_upwards [h] with u hu
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  simpa only [ENNReal.toReal_ofReal (mul_nonneg hB (halfPlanePoisson_nonneg z.re z.im_pos u))] using ht

end Singularity
