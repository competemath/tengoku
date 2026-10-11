import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.WUCFunctions

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local instance : NormedAddCommGroup (Space H) := inferInstance
local instance : NormedSpace ℝ (Space H) := inferInstance
local instance (K : Set H) : NormedAddCommGroup (supported K) := inferInstance
local instance (K : Set H) : NormedSpace ℝ (supported K) := inferInstance

end LipschitzCounterexample.CompactWSC
end

end OAI
