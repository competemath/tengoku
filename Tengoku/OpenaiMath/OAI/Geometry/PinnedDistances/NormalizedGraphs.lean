import Tengoku.OpenaiMath.OAI.Geometry.PinnedDistances.LimitObstruction

namespace OAI

universe u1 u2

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace WeakPinned.Bounded
local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {V : ℕ → Type u1} {I : ℕ → Type u2} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (I n)]

end WeakPinned.Bounded

end
end

end OAI
