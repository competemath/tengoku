import Tengoku.TdaLib.TDA.Persistence.BoundaryTransportAttainment
import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Tengoku.Seed.Probability.Kernel.Disintegration.StandardBorel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Fixed-space `Lᵖ` notation for reservoir transport. -/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal
namespace TDA.Persistence.BoundaryTransport

/-- The literal metric `Lᵖ` norm is the rooted powered integral, including infinite values.
@isnad1 id=eq.1h2v.s7.ecd6a970b566 from=translated src=- shape=e4c232b8 vocab=64275d4e
-/
theorem eLpNorm_dist_eq_collapsedPowerCost (p : ℝ) (hp : 0 < p)
    (γ : Measure (Space × Space)) :
    eLpNorm (fun z : Space × Space => dist z.1 z.2) (ENNReal.ofReal p) γ =
      (∫⁻ z, collapsedPowerCost p z ∂γ) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  congr 1
  apply lintegral_congr
  intro z
  simp only [collapsedPowerCost]
  rw [Real.enorm_eq_ofReal (dist_nonneg : 0 ≤ dist z.1 z.2),
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp.le]

/-- On the collapsed metric space, the extended metric and real metric give the same
coupling `Lᵖ` norm.
@isnad1 id=eq.0h2v.s7.0850218bb46e from=translated src=- shape=d92e05cb vocab=2aa0d441
-/
theorem eLpNorm_edist_eq_dist (q : ℝ≥0∞) (γ : Measure (Space × Space)) :
    eLpNorm (fun z : Space × Space => edist z.1 z.2) q γ =
      eLpNorm (fun z : Space × Space => dist z.1 z.2) q γ := by
  apply eLpNorm_congr_enorm_ae
  exact Filter.Eventually.of_forall fun z => by
    rw [enorm_eq_self, edist_dist, Real.enorm_eq_ofReal dist_nonneg]

end TDA.Persistence.BoundaryTransport
