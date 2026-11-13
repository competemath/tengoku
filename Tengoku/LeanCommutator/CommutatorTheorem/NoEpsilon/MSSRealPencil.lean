import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSBarrier

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real coefficients of a Hermitian determinant pencil

Conjugating the coefficients transposes the matrix pencil and therefore fixes its
determinant. This supplies an actual real polynomial to the real MSS barrier lemmas.
-/

open scoped BigOperators ComplexOrder
open Matrix MvPolynomial

namespace NoEpsilon.MSSRealPencil

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

-- Preserve the existing parameter list for downstream callers.

/-- A determinant pencil with an arbitrary Hermitian constant term.-/
noncomputable def affinePencil (B : Matrix ι ι ℂ) (A : κ → Matrix ι ι ℂ) :
    MvPolynomial κ ℂ :=
  (B.map MvPolynomial.C +
    ∑ i, (MvPolynomial.X i : MvPolynomial κ ℂ) • (A i).map MvPolynomial.C).det

-- Preserve the existing parameter list for downstream callers.

end NoEpsilon.MSSRealPencil
