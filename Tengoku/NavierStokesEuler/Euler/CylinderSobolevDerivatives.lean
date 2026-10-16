import Tengoku.NavierStokesEuler.Euler.CylinderSobolevOperators

/-! Actual coordinate derivatives and truncations between the complete cylinder Sobolev spaces. -/

noncomputable section

namespace EulerCylinderSobolevSpace

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
open scoped Topology

/-- An old word viewed in the next Sobolev order. -/
def truncateIndex {q : ℕ} (w : SobolevWord q) : SobolevWord (q + 1) :=
  ⟨⟨w.1.val, Nat.lt_succ_of_lt w.1.isLt⟩, w.2⟩

/-- Appending a direction indexes a derivative of the corresponding underlying derivative field. -/
def derivativeIndex {q : ℕ} (i : Fin 4) (w : SobolevWord q) : SobolevWord (q + 1) :=
  ⟨⟨w.1.val + 1, Nat.succ_lt_succ w.1.isLt⟩, Fin.snoc w.2 i⟩

variable (period : ℝ) [Fact (0 < period)]

end EulerCylinderSobolevSpace
