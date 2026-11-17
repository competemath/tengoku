import Tengoku.FormalizeTubalDemystPaper.TubalTensor.Modules.TensorMatrix

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/LinearMaps/StarMLinear.lean
  Definition 21: ⋆_M-linear maps.

  A function T : K_M^p → K_M^m is ⋆_M-linear if
    T(r ⋆_M U + s ⋆_M V) = r ⋆_M T(U) + s ⋆_M T(V)
  for all U, V ∈ K_M^p and r, s ∈ K_M.

  Since OrientedMatrix is a Module over KM, this is precisely
  Mathlib's `LinearMap (KM n td)`.
-/

namespace TubalTensor

variable {n : ℕ} {td : TubalData n} {m p l : ℕ}

/-! ## Definition 21: ⋆_M-linear maps -/

/-- **Definition 21**: A ⋆_M-linear map from K_M^p to K_M^m.
    This is just `LinearMap` over the ring `KM n td`.-/
abbrev StarMLinearMap (p m : ℕ) (n : ℕ) (td : TubalData n) :=
  OrientedMatrix p n td →ₗ[KM n td] OrientedMatrix m n td

/-- Every matrix A ∈ K_M^{m×p} defines a ⋆_M-linear map X ↦ A ⋆_M X
    (matrix-vector multiplication over KM).-/
noncomputable def TubalMatrix.toLinearMap (A : TubalMatrix m p n td) :
    StarMLinearMap p m n td :=
  (Matrix.mulVecLin A).restrictScalars (KM n td)

/-- The ⋆_M-linear map induced by A sends X to A.mulVec X.
@isnad1 id=eq.0h6v.s7.09fa18bfb610 from=translated src=- shape=ae492431 vocab=8ca12dfb
-/
theorem TubalMatrix.toLinearMap_apply (A : TubalMatrix m p n td)
    (X : OrientedMatrix p n td) :
    A.toLinearMap X = A.mulVec X := rfl

end TubalTensor
