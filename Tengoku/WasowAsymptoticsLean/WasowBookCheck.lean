import Tengoku.Seed.Data.Complex.Basic
import Tengoku.Seed.Data.Matrix.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.Notation
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms WasowBookCheck.zero_solution` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowBookCheck.nonzero_solution` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowBookCheck.output_rows_distinct` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowBookCheck.not_existsUnique_unnormalized_last_row` (it only prints; the queue checks the axioms of every declaration). -/

/-!
A local check of the literal, unnormalized uniqueness assertion in Wasow's
Lemma 19.1.  For h = 1 and k = 2 there are no first h - 1 rows to constrain.
The last row of H X - X K is not unique as X varies.  This counterexample does
not refute solvability, a suitably normalized statement, or Theorem 19.1.
-/
set_option autoImplicit false
noncomputable section

namespace WasowBookCheck

def Hshift : Matrix (Fin 1) (Fin 1) ℂ := 0
def Kshift : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
def Xzero : Matrix (Fin 1) (Fin 2) ℂ := !![0, 0]
def Xone : Matrix (Fin 1) (Fin 2) ℂ := !![1, 0]
def Mzero : Matrix (Fin 1) (Fin 2) ℂ := !![0, 0]
def Mone : Matrix (Fin 1) (Fin 2) ℂ := !![0, -1]

/--
@isnad1 id=eq.0h0v.s7.03a1eae64007 from=translated src=- shape=ec55e86f vocab=a73025f2
-/
theorem zero_solution : Hshift * Xzero - Xzero * Kshift = Mzero := by
  ext i j
  fin_cases i
  fin_cases j <;>
    norm_num [Hshift, Kshift, Xzero, Mzero, Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h0v.s7.0897bc588b36 from=translated src=- shape=ec55e86f vocab=719c9314
-/
theorem nonzero_solution : Hshift * Xone - Xone * Kshift = Mone := by
  ext i j
  fin_cases i
  fin_cases j <;>
    norm_num [Hshift, Kshift, Xone, Mone, Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=ne.0h0v.s4.476dd5e15f7f from=translated src=- shape=8b913b8d vocab=b49d5df8
-/
theorem output_rows_distinct : Mzero ≠ Mone := by
  intro h
  have hh := congrFun (congrFun h 0) 1
  norm_num [Mzero, Mone] at hh

/-- With one row, the missing first-row constraints are vacuous.  The literal
claim that the output last row is unique is already false in these dimensions.
@isnad1 id=not.0h0v.s8.edbe37daa001 from=translated src=- shape=c8d00c6a vocab=e12b6127
-/
theorem not_existsUnique_unnormalized_last_row :
    ¬ ∃! M : Matrix (Fin 1) (Fin 2) ℂ,
      ∃ X : Matrix (Fin 1) (Fin 2) ℂ,
        (0 : Matrix (Fin 1) (Fin 1) ℂ) * X - X * Kshift = M := by
  rintro ⟨M, _, huniq⟩
  have hzero := huniq Mzero ⟨Xzero, zero_solution⟩
  have hone := huniq Mone ⟨Xone, nonzero_solution⟩
  exact output_rows_distinct (hzero.trans hone.symm)

end WasowBookCheck

