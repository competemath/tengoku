import Tengoku.NavierStokesEuler.Euler.SobolevSmoothProduct
import Tengoku.NavierStokesEuler.Euler.SobolevSmoothApproximation

/-! Cauchy convergence of actual smooth cylinder products in the complete Sobolev space. -/

noncomputable section

namespace EulerSobolevL2Product

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSpatialSobolevInverse EulerStrongSmoothJet EulerVectorCylinder
  EulerMetricTransport EulerCylinderMollifier EulerMollifierRepresentative
open scoped Topology ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Differences of actual smooth representatives remain actual smooth representatives. -/
theorem smooth_representative_sub {q : ℕ} (u v : SobolevSpace period q)
    (hu : ∃ f : LiftDomain period → Vector3,
      (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hv : ∃ g : LiftDomain period → Vector3,
      (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ∃ f : LiftDomain period → Vector3,
      (value period (u-v) : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x) := by
  obtain ⟨f, hfu, hf⟩ := hu
  obtain ⟨g, hgv, hg⟩ := hv
  refine ⟨f-g, ?_, fun x => (hf x).sub (hg x)⟩
  filter_upwards [Lp.coeFn_sub (value period u) (value period v), hfu, hgv] with x h1 h2 h3
  exact h1.trans (by simp only [Pi.sub_apply, h2, h3])

/-- A quantitative difference estimate transfers Cauchy convergence through a bilinear operation. -/
theorem cauchySeq_of_product_control {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [PseudoMetricSpace Z] (u : ℕ → X) (v : ℕ → Y) (p : ℕ → Z) (A B : ℝ)
    (hu : CauchySeq u) (hv : CauchySeq v)
    (h : ∀ n m, dist (p n) (p m) ≤ A * dist (u n) (u m) + B * dist (v n) (v m)) :
    CauchySeq p := by
  rw [cauchySeq_iff_tendsto_dist_atTop_0] at hu hv ⊢
  apply squeeze_zero (fun nm : ℕ × ℕ => (dist_nonneg : 0 ≤ dist (p nm.1) (p nm.2))) (fun nm => h nm.1 nm.2)
  simpa only [mul_zero, add_zero] using (hu.const_mul A).add (hv.const_mul B)

end EulerSobolevL2Product
