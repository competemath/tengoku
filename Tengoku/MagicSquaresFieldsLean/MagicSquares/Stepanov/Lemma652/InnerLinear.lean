import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Unknowns
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-!
# The coefficient polynomial e_{ij} as a linear map

Batch 3 defined `stepanovInnerPolynomial v i j`.  For the construction
of `e_{ij,n}` we need the stronger fact that, for fixed `i,j`, this
polynomial depends linearly on the scalar unknown vector `v`.
-/

/-- Select the `D+1` scalar coefficients belonging to one fixed pair
`(i,j)`.-/
def stepanovCoefficientSlice
    {m u D : ℕ}
    (i : Fin m) (j : Fin (u + 1)) :
    StepanovUnknowns F m u D →ₗ[F] (Fin (D + 1) → F) where
  toFun := fun v l => v (i, (j, l))
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl

/-- The polynomial `e_{ij}` as a linear map from the full coefficient
vector.-/
noncomputable def stepanovInnerLinear
    {m u D : ℕ}
    (i : Fin m) (j : Fin (u + 1)) :
    StepanovUnknowns F m u D →ₗ[F] Polynomial F :=
  (Polynomial.ofFn (D + 1)).comp
    (stepanovCoefficientSlice (F := F) i j)

@[simp]
theorem stepanovInnerLinear_apply
    {m u D : ℕ}
    (v : StepanovUnknowns F m u D)
    (i : Fin m) (j : Fin (u + 1)) :
    stepanovInnerLinear (F := F) i j v =
      stepanovInnerPolynomial v i j := by
  rfl

end LN97
end MagicSquares
