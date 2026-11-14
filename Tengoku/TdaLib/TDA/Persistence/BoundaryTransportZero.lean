import Tengoku.TdaLib.TDA.Persistence.BoundaryTransportComparison
import Tengoku.TdaLib.TDA.Persistence.ReservoirMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Boundary transport to the zero measure

The powered value against zero equals the source's diagonal persistence moment.
The equality includes an infinite moment and uses only finite original mass.
The rooted and powered-distance forms follow with the same exponent convention.
-/

noncomputable section

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace TDA.Persistence.BoundaryTransport

private theorem collapsedPowerCost_lintegral_eq_depthMoment
    (p : ℝ) (hp : 0 < p) (μ : Measure Interior) (R : ℝ≥0∞)
    (γ : Measure (Space × Space))
    (hfirst : γ.map Prod.fst = reservoirMeasure μ R)
    (hsecond : γ.map Prod.snd = reservoirMeasure (0 : Measure Interior) R) :
    (∫⁻ z, collapsedPowerCost p z ∂γ) =
      ∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ := by
  have hboundary_map : ∀ᵐ y ∂γ.map Prod.snd, y = Space.boundary := by
    rw [hsecond, reservoirMeasure_zero]
    exact Measure.ae_smul_measure (by simp) R
  have hboundary_set : MeasurableSet {y : Space | y = Space.boundary} := by
    have hset : {y : Space | y = Space.boundary} = {Space.boundary} := by
      ext y
      simp
    rw [hset]
    exact measurableSet_singleton _
  have hboundary : ∀ᵐ z ∂γ, z.2 = Space.boundary :=
    (ae_map_iff (by fun_prop : AEMeasurable Prod.snd γ)
      hboundary_set).1 hboundary_map
  have hp0 : 0 ≤ p := hp.le
  have hdist : Continuous (fun x : Space => dist x Space.boundary) := by
    exact continuous_dist.comp (continuous_id.prodMk continuous_const)
  have hmeasurable : Measurable (boundaryMomentIntegrand p) :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_rpow_const hp0).comp hdist).measurable
  calc
    (∫⁻ z, collapsedPowerCost p z ∂γ) =
        ∫⁻ z, boundaryMomentIntegrand p z.1 ∂γ := by
      apply lintegral_congr_ae
      filter_upwards [hboundary] with z hz
      simp [collapsedPowerCost, boundaryMomentIntegrand, hz]
    _ = ∫⁻ x, boundaryMomentIntegrand p x ∂γ.map Prod.fst := by
      symm
      exact lintegral_map hmeasurable (by fun_prop : Measurable Prod.fst)
    _ = ∫⁻ x, boundaryMomentIntegrand p x ∂reservoirMeasure μ R := by
      rw [hfirst]
    _ = ∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ :=
      reservoirMeasure_boundary_moment μ R p hp

/-- The all-boundary-plan infimum against zero is the source's diagonal persistence moment.
@isnad1 id=eq.2h2v.s7.9de43c367bd3 from=translated src=- shape=a91fdfbc vocab=edb98e7a
-/
theorem boundaryTransportPowerValue_zero_target
    (p : ℝ) (hp : 1 ≤ p) (μ : Measure Interior) (hμtop : μ Set.univ < ∞) :
    boundaryTransportPowerValue p μ 0 =
      ∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ := by
  let R : ℝ≥0∞ := μ Set.univ
  have hRtop : R < ∞ := hμtop
  have htotal : μ Set.univ + (0 : Measure Interior) Set.univ ≤ R := by
    simp [R]
  have hreservoir : reservoirPowerValue p μ 0 R =
      ∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ := by
    apply le_antisymm
    · have hπ : IsBoundaryPlan (diagonalBoundaryPlan μ 0) μ 0 :=
        diagonalBoundaryPlan_admissible μ 0
      have hforward := collapsedAugmentation_forward hπ R hRtop htotal p hp
      calc
        reservoirPowerValue p μ 0 R ≤
            ∫⁻ z, collapsedPowerCost p z ∂collapsedAugmentation (diagonalBoundaryPlan μ 0) R :=
          reservoirPowerValue_le_plan p μ 0 R _ hforward.1 hforward.2.1
        _ ≤ ∫⁻ z, planPowerCost p z ∂diagonalBoundaryPlan μ 0 := hforward.2.2
        _ = ∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ := by
          rw [diagonalBoundaryPlan_cost]
          simp
    · unfold reservoirPowerValue
      refine le_iInf fun γ => le_iInf fun hγ => ?_
      exact (collapsedPowerCost_lintegral_eq_depthMoment p
        (lt_of_lt_of_le zero_lt_one hp) μ R γ hγ.1 hγ.2).symm.le
  calc
    boundaryTransportPowerValue p μ 0 = reservoirPowerValue p μ 0 R :=
      boundaryTransportPowerValue_eq_reservoirPowerValue p hp μ 0 R hRtop htotal
    _ = ∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ := hreservoir

/-- The rooted zero-target value is the reciprocal-p root of the diagonal moment.
@isnad1 id=eq.2h2v.s8.48828891ae27 from=translated src=- shape=1a7c95c6 vocab=fcd0932a
-/
theorem boundaryTransportDistance_zero_target
    (p : ℝ) (hp : 1 ≤ p) (μ : Measure Interior) (hμtop : μ Set.univ < ∞) :
    boundaryTransportDistance p μ 0 =
      (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) ^ (1 / p) := by
  rw [boundaryTransportDistance, boundaryTransportPowerValue_zero_target p hp μ hμtop]

/-- The p-th power of distance to zero is exactly the diagonal persistence moment.
@isnad1 id=eq.2h2v.s7.c2fa94f4b4f1 from=translated src=- shape=9d405cf5 vocab=fe421bae
-/
theorem boundaryTransportDistance_zero_target_rpow
    (p : ℝ) (hp : 1 ≤ p) (μ : Measure Interior) (hμtop : μ Set.univ < ∞) :
    boundaryTransportDistance p μ 0 ^ p =
      ∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ := by
  rw [boundaryTransportDistance_zero_target p hp μ hμtop, ← ENNReal.rpow_mul,
    one_div_mul_cancel (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)), ENNReal.rpow_one]

end TDA.Persistence.BoundaryTransport
