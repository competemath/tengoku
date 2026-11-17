import Tengoku.Seed.Topology.ContinuousMap.ZeroAtInfty
import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinate summands of multilinear maps on c₀

For an array of coefficients `c`, the summand at a tuple `a` is the multilinear map
`x ↦ (∏ r, x r (a r)) • c a` on `C₀(I, K)`, with its sup-norm bound.
-/

open scoped BigOperators ZeroAtInfty

namespace CZero

variable {I K W : Type*} [TopologicalSpace I] [NontriviallyNormedField K]
  [NormedAddCommGroup W] [NormedSpace K W] {n : ℕ}

private def coordinateLinearMap (i : I) : C₀(I, K) →ₗ[K] K where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The multilinear map `x ↦ (∏ r, x r (a r)) • c a`.-/
noncomputable def arraySummand (c : (Fin n → I) → W) (a : Fin n → I) :
    MultilinearMap K (fun _ : Fin n => C₀(I, K)) W :=
  ((MultilinearMap.mkPiAlgebra K (Fin n) K).compLinearMap
    (fun r => coordinateLinearMap (a r))).smulRight (c a)

@[simp]
theorem arraySummand_apply (c : (Fin n → I) → W) (a : Fin n → I)
    (x : Fin n → C₀(I, K)) :
    arraySummand c a x = (∏ r, x r (a r)) • c a :=
  rfl

end CZero
