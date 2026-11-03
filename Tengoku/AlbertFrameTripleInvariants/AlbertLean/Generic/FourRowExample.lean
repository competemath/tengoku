import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowUniqueness
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms two_distinct_goodSolutions` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms goodSolution_iff` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Two distinct rational solutions on the reconstruction open

This is an ordinary 3×3 matrix example. It supplies no Albert model,
frame normalization, ledger descent, or generic invariant-field claim.
-/

namespace AlbertLean.Generic.FourRowExample

open AlbertLean.Generic.FourRowUniqueness

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℚ

def U : Mat3 := 1
def V : Mat3 := !![-2, 0, 0; 0, -6, 0; 0, 0, 3 / 16]
def X : Mat3 := !![1, 0, 0; 0, 2, 0; 0, 0, -3 / 4]
def Y : Mat3 := !![-2, 0, 0; 0, -3, 0; 0, 0, -1 / 4]
def c : ℚ := -3 / 2
def d : ℚ := -3 / 2
def E : Mat3 := !![5, 0, 0; 0, 9, 0; 0, 0, 45 / 16]

theorem c_ne_zero : c ≠ 0 := by norm_num [c]
theorem d_ne_zero : d ≠ 0 := by norm_num [d]

theorem V_det : V.det = c ^ 2 := by
  norm_num [V, c, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] <;> decide +kernel

theorem one_sub_U_add_V_det : (1 - U + V).det = d ^ 2 := by
  simpa [U, d, c] using V_det

theorem X_quadratic : X ^ 2 + X * U + V = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X, U, V, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

theorem Y_quadratic : Y ^ 2 + Y * U + V = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Y, U, V, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

theorem X_det : X.det = c := by
  norm_num [X, c, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] <;> decide +kernel

theorem Y_det : Y.det = c := by
  norm_num [Y, c, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] <;> decide +kernel

theorem one_add_X_det : (1 + X).det = -d := by
  norm_num [X, d, Matrix.det_fin_three, Matrix.one_apply,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> decide +kernel

theorem one_add_Y_det : (1 + Y).det = -d := by
  norm_num [Y, d, Matrix.det_fin_three, Matrix.one_apply,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> decide +kernel

/-- Here the reconstruction denominator is constant in the trace parameter.-/
theorem denominator_eq (t : ℚ) : reconstructionDenominator U V c d t = E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reconstructionDenominator, U, V, c, d, E, pow_two,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem E_det : E.det = 2025 / 16 := by
  norm_num [E, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] <;> decide +kernel

theorem denominator_det_ne_zero (t : ℚ) :
    (reconstructionDenominator U V c d t).det ≠ 0 := by
  rw [denominator_eq, E_det]
  norm_num

theorem X_good : GoodSolution U V c d X where
  quadratic := X_quadratic
  det_eq := X_det
  det_one_add_eq := one_add_X_det
  denominator_det_ne_zero := denominator_det_ne_zero _

theorem Y_good : GoodSolution U V c d Y where
  quadratic := Y_quadratic
  det_eq := Y_det
  det_one_add_eq := one_add_Y_det
  denominator_det_ne_zero := denominator_det_ne_zero _

theorem X_ne_Y : X ≠ Y := by
  intro h
  have h00 := congrArg (fun M : Mat3 => M 0 0) h
  norm_num [X, Y] at h00

/-- The determinant open contains at least two distinct rational solutions.-/
theorem two_distinct_goodSolutions :
    GoodSolution U V c d X ∧ GoodSolution U V c d Y ∧ X ≠ Y :=
  ⟨X_good, Y_good, X_ne_Y⟩

/-- The abstract upper bound is attained by this explicit rational example.-/
theorem goodSolution_iff (W : Mat3) :
    GoodSolution U V c d W ↔ W = X ∨ W = Y := by
  constructor
  · intro hW
    rcases three_goodSolutions_pairwise_eq U V c d c_ne_zero d_ne_zero
      V_det one_sub_U_add_V_det X Y W X_good Y_good hW with hXY | hXW | hYW
    · exact False.elim (X_ne_Y hXY)
    · exact Or.inl hXW.symm
    · exact Or.inr hYW.symm
  · rintro (rfl | rfl)
    · exact X_good
    · exact Y_good

end AlbertLean.Generic.FourRowExample
