import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The (3,1) signature of the trace form of K = ℚ[x]/(x⁴ − x − 1)

The trace form (Gram matrix in the power basis {1, x, x², x³}) is the
integer matrix `M` with `M_{ij} = p_{i+j}`, the power sums of the roots of
`x⁴ − x − 1`. Newton's identities (e₁=0, e₂=0, e₃=1, e₄=−1) give
`p₀=4, p₁=0, p₂=0, p₃=3, p₄=4, p₅=0, p₆=3`, hence

  `M = !![4,0,0,3; 0,0,3,4; 0,3,4,0; 3,4,0,3]`.

We prove, all kernel-checked:

* `det_M`        : `det M = -283`  (negative ⇒ an odd number of negative
                   eigenvalues, hence at least one),
* `congruence`   : an explicit invertible rational `P` (with `det P = -1`)
                   carries `M` to a diagonal form `Pᵀ M P = D`,
                   `D = diag(4, 4, -9/4, 283/36)`,
* the diagonal of `D` has exactly THREE positive entries and ONE negative
  entry (`D00_pos`, `D11_pos`, `D33_pos`, `D22_neg`).

By Sylvester's law of inertia the signature of `M` equals the signs of the
diagonal of any such `D`, i.e. **(3, 1)**. The bundled statement is
`signature_3_1`.

The matrix `P` was produced by symmetric Gaussian elimination with a
permutation to dodge the zero leading 2×2 minor (`M₁₁ = M₂₂ over the
{x,x²} block is singular`).

NOTE ON TACTICS: the two determinant evaluations use `decide +kernel`
(kernel-trusted reduction of a `Decidable` equality of explicit rationals;
this is NOT `native_decide` and adds no compiler trust). The axiom set of
every theorem below is exactly `{propext, Classical.choice, Quot.sound}`.
-/

namespace PDT

open Matrix

/-- The trace-form Gram matrix of `K = ℚ[x]/(x⁴ − x − 1)` in the power basis.-/
def M : Matrix (Fin 4) (Fin 4) ℚ :=
  !![4,0,0,3; 0,0,3,4; 0,3,4,0; 3,4,0,3]

/-- The explicit rational congruence matrix (symmetric Gaussian elimination
with a permutation to dodge the zero leading 2×2 minor).-/
def P : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, -3/4;
     0, 0, 1, 16/9;
     0, 1, -3/4, -4/3;
     0, 0, 0, 1]

/-- The diagonalised trace form `D = Pᵀ M P`.-/
def D : Matrix (Fin 4) (Fin 4) ℚ :=
  !![4, 0, 0, 0;
     0, 4, 0, 0;
     0, 0, -9/4, 0;
     0, 0, 0, 283/36]

/-- `M` is symmetric (it is a Gram matrix).
@isnad1 id=issymm.0h0v.s3.f684c1941bdb from=translated src=- shape=d3a93718 vocab=2bcef70a
-/
theorem M_symm : M.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, Matrix.IsSymm, Matrix.transpose_apply]

/-- The determinant of the trace form is `-283`. Negative determinant forces
an odd number of negative eigenvalues, hence at least one.
@isnad1 id=eq.0h0v.s5.4f0815cdbbf3 from=translated src=- shape=e5ac977b vocab=c7a4e95f
-/
theorem det_M : M.det = -283 := by
  simp only [M, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, Matrix.submatrix_apply, Fin.succAbove, Fin.castSucc_zero,
    Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  decide +kernel

/-- The congruence `Pᵀ * M * P = D` holds exactly over `ℚ`.
@isnad1 id=eq.0h0v.s7.6674ac9de9f1 from=translated src=- shape=a8c27b39 vocab=430e0bd1
-/
theorem congruence : P.transpose * M * P = D := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P, M, D, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> norm_num

/-- `P` is invertible: its determinant is `-1`.
@isnad1 id=eq.0h0v.s5.9207e6b61e7b from=translated src=- shape=e5ac977b vocab=37c67987
-/
theorem det_P : P.det = -1 := by
  simp only [P, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, Matrix.submatrix_apply, Fin.succAbove, Fin.castSucc_zero,
    Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  decide +kernel

/-- `P` is a unit (its determinant is a unit), so the congruence is genuine.
@isnad1 id=isunit.0h0v.s4.c28cf7614cb4 from=translated src=- shape=4d15e069 vocab=434b99c6
-/
theorem P_isUnit : IsUnit P.det := by
  rw [det_P]; exact isUnit_one.neg

/-- `D` is diagonal.
@isnad1 id=isdiag.0h0v.s3.596acc93976c from=translated src=- shape=d3a93718 vocab=80af7afc
-/
theorem D_isDiag : D.IsDiag := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [D]

/-! ### The (3,1) signature, read off from the signs of the diagonal of `D`. -/

/--
@isnad1 id=lt.0h0v.s5.35257c64c7b5 from=translated src=- shape=2a8c603f vocab=5bd62cac
-/
theorem D00_pos : (0 : ℚ) < D 0 0 := by show (0 : ℚ) < (4 : ℚ); norm_num
/--
@isnad1 id=lt.0h0v.s5.fe98b041a363 from=translated src=- shape=2a8c603f vocab=5bd62cac
-/
theorem D11_pos : (0 : ℚ) < D 1 1 := by show (0 : ℚ) < (4 : ℚ); norm_num
/--
@isnad1 id=lt.0h0v.s5.e9ea1eeb1ae2 from=translated src=- shape=2a8c603f vocab=5bd62cac
-/
theorem D33_pos : (0 : ℚ) < D 3 3 := by show (0 : ℚ) < (283 / 36 : ℚ); norm_num
/--
@isnad1 id=lt.0h0v.s5.4e6146eadca6 from=translated src=- shape=b4dc571a vocab=5bd62cac
-/
theorem D22_neg : D 2 2 < (0 : ℚ) := by show (-9 / 4 : ℚ) < 0; norm_num

/-- **The (3,1) signature theorem (concrete Sylvester form).**

There is an invertible rational congruence `P` carrying the trace form `M`
to the diagonal form `D` whose diagonal has exactly three positive entries
and one negative entry. By Sylvester's law of inertia the signature of the
real quadratic form `M` is therefore `(3, 1)`. Together with `det_M = -283`
(`< 0`, forcing an odd number of negative signs) this pins the signature
uniquely.
@isnad1 id=and.0h0v.s8.9d86dd6055ed from=translated src=- shape=24852430 vocab=c91ef8f6
-/
theorem signature_3_1 :
    M.IsSymm ∧
    P.transpose * M * P = D ∧
    IsUnit P.det ∧
    D.IsDiag ∧
    (0 < D 0 0 ∧ 0 < D 1 1 ∧ 0 < D 3 3) ∧ D 2 2 < 0 ∧
    M.det = -283 := by
  exact ⟨M_symm, congruence, P_isUnit, D_isDiag,
    ⟨D00_pos, D11_pos, D33_pos⟩, D22_neg, det_M⟩

end PDT
