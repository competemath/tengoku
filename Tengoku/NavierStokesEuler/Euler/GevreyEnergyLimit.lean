import Tengoku.NavierStokesEuler.Euler.GevreyRestriction
import Tengoku.NavierStokesEuler.Euler.GevreyMetricEstimate
import Tengoku.NavierStokesEuler.Euler.MetricPathConvergence

namespace EulerGevreyEnergyLimit
end EulerGevreyEnergyLimit
namespace Set
end Set
namespace EulerLiftedGradientSpace
end EulerLiftedGradientSpace
namespace EulerCylinderSobolevSpace
end EulerCylinderSobolevSpace
namespace EulerGevreyMetricComparison
end EulerGevreyMetricComparison
namespace EulerGevreyDifferentiatedEquation
end EulerGevreyDifferentiatedEquation
namespace EulerGevreyMetricEstimate
end EulerGevreyMetricEstimate
namespace EulerGevreyRestriction
end EulerGevreyRestriction
namespace EulerMetricPathConvergence
end EulerMetricPathConvergence
namespace EulerWeightedCylinderEnergy
end EulerWeightedCylinderEnergy
namespace EulerFiniteMetricEnergy
end EulerFiniteMetricEnergy
namespace Topology
end Topology

namespace NavierStokesEulerFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual finite Gevrey metric energy passes to strong Sobolev limits. -/

noncomputable section

namespace EulerGevreyEnergyLimit
open _root_.EulerGevreyEnergyLimit

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGevreyMetricComparison
  EulerGevreyDifferentiatedEquation EulerGevreyMetricEstimate EulerGevreyRestriction
  EulerMetricPathConvergence EulerWeightedCylinderEnergy EulerFiniteMetricEnergy
open _root_.Set _root_.EulerLiftedGradientSpace _root_.EulerCylinderSobolevSpace _root_.EulerGevreyMetricComparison _root_.EulerGevreyDifferentiatedEquation _root_.EulerGevreyMetricEstimate _root_.EulerGevreyRestriction _root_.EulerMetricPathConvergence _root_.EulerWeightedCylinderEnergy _root_.EulerFiniteMetricEnergy
open scoped Topology _root_.Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Actual energy coordinates depend continuously on the Sobolev field. -/
theorem energyValues_continuous {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) :
    Continuous (energyValues period q N hN) := by
  apply continuous_pi
  intro I
  apply continuous_pi
  intro a
  exact (energyWordOperator period q N hN I a).continuous.congr
    (fun u => energyWordOperator_apply period q N hN I a u)

/-- The actual finite Gevrey metric energy is continuous in its Sobolev field, including zero energy. -/
theorem energyNorm_continuous {s : ℕ} (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) :
    Continuous (energyNorm period N hN ρ K) := by
  unfold energyNorm weightedMetricSum
  apply continuous_finsetSum
  intro I _
  apply Continuous.const_mul
  exact familyMetricNorm_continuous.comp
    (continuous_const.prodMk ((continuous_apply I).comp (energyValues_continuous period 6 N hN)))

/-- Restriction preserving the derivative cutoff leaves the actual Gevrey energy unchanged. -/
theorem energyNorm_restrict {p q : ℕ} (hqp : q ≤ p) (N : ℕ) (hN : N+6 ≤ q) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period p) :
    energyNorm period N hN ρ K (restrictOperator period hqp u) =
      energyNorm period N (hN.trans hqp) ρ K u := by
  unfold energyNorm
  rw [energyValues_restrict]

/-- A genuine strong lower-order limit retains every finite metric-energy bound whose derivative cutoff is retained. -/
theorem energyNorm_limit_bound {p q : ℕ} (hqp : q ≤ p) (N : ℕ) (hN : N+6 ≤ q) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : ℕ → SobolevSpace period p) (e : SobolevSpace period q)
    (h : Filter.Tendsto (fun n => restrictOperator period hqp (u n)) Filter.atTop (𝓝 e))
    (M : ℝ) (hb : ∀ n, energyNorm period N (hN.trans hqp) ρ K (u n) ≤ M) :
    energyNorm period N hN ρ K e ≤ M := by
  apply le_of_tendsto ((energyNorm_continuous period N hN ρ K).continuousAt.tendsto.comp h)
  exact Filter.Eventually.of_forall (fun n => by
    change energyNorm period N hN ρ K (restrictOperator period hqp (u n)) ≤ M
    rw [energyNorm_restrict]
    exact hb n)

end EulerGevreyEnergyLimit
