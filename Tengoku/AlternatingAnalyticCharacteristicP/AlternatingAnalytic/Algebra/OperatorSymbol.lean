import Tengoku.Seed.LinearAlgebra.ExteriorPower.Basic
import Tengoku.Seed.LinearAlgebra.TensorPower.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Operator tensor wedge evaluation

A tensor of endomorphisms acts on a tuple of vectors by applying each operator to its
corresponding vector and taking the exterior product.
-/

open scoped TensorProduct

namespace AlternatingAnalytic

variable (L : Type*) [CommRing L] (V : Type*) [AddCommGroup V] [Module L V] (k : ℕ)

/-- Evaluate a tensor of endomorphisms on vector inputs and take their exterior product.-/
noncomputable def operatorTensorEval :
    (⨂[L]^k (Module.End L V)) →ₗ[L]
      MultilinearMap L (fun _ : Fin k ↦ V) (⋀[L]^k V) :=
  PiTensorProduct.lift (MultilinearMap.piLinearMap (exteriorPower.ιMulti L k).toMultilinearMap)

@[simp]
theorem operatorTensorEval_tprod (A : Fin k → Module.End L V) (x : Fin k → V) :
    operatorTensorEval L V k (PiTensorProduct.tprod L A) x =
      exteriorPower.ιMulti L k (fun i ↦ A i (x i)) := by
  simp [operatorTensorEval]

end AlternatingAnalytic
