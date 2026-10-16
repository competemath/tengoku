import Tengoku.NavierStokesEuler.Euler.HeatAllOrders
import Tengoku.NavierStokesEuler.Euler.UnshiftedProducts
import Tengoku.NavierStokesEuler.Euler.H6NonlinearPressure
import Tengoku.NavierStokesEuler.Euler.SobolevProduct

/-! The actual complete Sobolev product obeys the finite Gevrey H⁶ algebra bound, including nonsmooth inputs. -/

noncomputable section

namespace EulerSobolevGevreyProduct

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMetricTransport EulerSobolevL2Product EulerH6Nonlinear
  EulerH6Pressure EulerJetProductBounds EulerPacketWeights EulerSobolevHeat EulerVectorCylinder
open scoped Topology ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

local instance gevreySobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
local instance gevreySobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The external Hq block is a continuous function of the actual finite Sobolev class. -/
theorem continuous_blockNorm {s q n : ℕ} (h : n+q ≤ s) :
    Continuous (fun u : SobolevSpace period s => blockNorm period (toJet period u) q n) := by
  unfold blockNorm
  apply continuous_finsetSum
  intro r hr
  have hnr : n+r ≤ s := by have := Finset.mem_range.mp hr; omega
  simp only [levelNorm_eq_words]
  apply continuous_finsetSum
  intro w _
  have he : (fun u : SobolevSpace period s => ‖(toJet period u).word w‖) =
      fun u => ‖wordOperator period (q := s) ⟨⟨n+r, Nat.lt_succ_of_le hnr⟩, w⟩ u‖ := by
    funext u
    rw [toJet_word period u hnr]
    rfl
  rw [he]
  exact (wordOperator period (q := s) ⟨⟨n+r, Nat.lt_succ_of_le hnr⟩, w⟩).continuous.norm

/-- Every truncated weighted block norm is continuous on its genuine Sobolev domain. -/
theorem continuous_weighted_blockNorm {s q : ℕ} (N : ℕ) (h : N+q ≤ s) (ρ : ℝ) :
    Continuous (fun u : SobolevSpace period s =>
      ∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period (toJet period u) q n) := by
  apply continuous_finsetSum
  intro n hn
  exact (continuous_blockNorm period (by have := Finset.mem_range.mp hn; omega : n+q ≤ s)).const_mul _

end EulerSobolevGevreyProduct
