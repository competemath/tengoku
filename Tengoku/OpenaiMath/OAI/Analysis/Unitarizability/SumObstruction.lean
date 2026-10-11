import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.KernelObstruction
import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.HilbertSum
import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.Unitarizer
import Tengoku

namespace OAI

/-! The operator-theoretic direct-sum obstruction, constructed from stage operators
without any uniform bound on their norms. -/
noncomputable section
namespace Dixmier
namespace DirectSumObstruction
open Filter
open scoped Topology
variable {G : Type*} [Group G]

abbrev Stage (G : Type*) (k : ℕ → ℕ) (j : ℕ) : Type _ := KernelObstruction.Space G (Fin (k j))
abbrev Total (G : Type*) (k : ℕ → ℕ) : Type _ := HilbertSum.Space (Stage G k)
abbrev Carrier (G : Type*) (k : ℕ → ℕ) := Triangular.Double (Total G k)

omit [Group G] in
/-- The concrete carrier is separable when the group is countable. -/
theorem carrier_separable [Countable G] (k : ℕ → ℕ) :
    TopologicalSpace.SeparableSpace (Carrier G k) := by
  have (j : ℕ) : TopologicalSpace.SeparableSpace (Stage G k j) := HilbertSum.separableSpace
  have : TopologicalSpace.SeparableSpace (Total G k) := HilbertSum.separableSpace
  infer_instance

end DirectSumObstruction
end Dixmier

end

end OAI
