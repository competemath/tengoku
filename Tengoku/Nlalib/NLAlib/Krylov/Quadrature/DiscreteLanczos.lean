import Tengoku.Nlalib.NLAlib.Krylov.Quadrature.DiscreteStieltjes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Actual finite-node Lanczos and Stieltjes Jacobi construction

Distinct nodes with positive weights give grade exactly `N`. The actual diagonal Lanczos
recursion therefore produces the full orthogonal basis and the canonical moment Jacobi
matrix. The actual weighted Stieltjes procedure has the same coefficients, with an explicit
monic mass convention at beta zero and zero coupling at termination. Its computed node values
also satisfy dual orthogonality.

Source: Gautschi (2004), Theorem 1.9 and §§2.2.3.1–2.2.3.2.
Atlas: `discrete-measure-jacobi-matrix`.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix

namespace NLAlib

variable {N : ℕ}

private theorem recurrenceMatrix_eq_arnoldiMatrix {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ) (q : ℕ) :
    (Matrix.of fun r (j : Fin q) => lanczosRecurrence A b j.val r) = arnoldiMatrix A b q := by
  ext r j
  simp only [Matrix.of_apply, arnoldiMatrix, lanczosRecurrence_eq_arnoldiBasis hA]

/-- The square-root weight vector has Euclidean norm equal to square-root total mass.
This is the monic beta-zero normalization in the discrete Jacobi bordered identity.-/
private theorem norm_toLp_sqrt_eq_sqrt_sum {n : Type*} [Fintype n] (w : n → ℝ)
    (hw : ∀ r, 0 ≤ w r) :
    ‖WithLp.toLp 2 (fun r => Real.sqrt (w r))‖ = Real.sqrt (∑ r, w r) := by
  have hs : ‖WithLp.toLp 2 (fun r => Real.sqrt (w r))‖ ^ 2 = ∑ r, w r := by
    rw [norm_toLp_sq_eq_dotProduct_self]
    simp only [dotProduct, ← pow_two, Real.sq_sqrt (hw _)]
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

/-- Actual Lanczos on the diagonal nodes produces an orthonormal square basis of full
order `N`, including the empty discrete measure.
Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial)
@isnad1 id=hasortho.2h3v.s7.ed59642b6262 from=translated src=- shape=183ee8cc vocab=7197b390
-/
theorem hasOrthonormalCols_lanczosRecurrence_diagonal_sqrt
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r) :
    HasOrthonormalCols (Matrix.of fun r (j : Fin N) =>
      lanczosRecurrence (diagonal t) (fun r => Real.sqrt (w r)) j.val r) := by
  rw [recurrenceMatrix_eq_arnoldiMatrix (Matrix.isHermitian_diagonal t)]
  apply hasOrthonormalCols_arnoldiMatrix
  rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]

/-- The full basis produced by actual diagonal Lanczos has orthonormal rows as well.
Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial)
@isnad1 id=other.2h3v.s7.ebe6b9379aa1 from=translated src=- shape=f239cebd vocab=5a830194
-/
theorem lanczosRecurrence_diagonal_sqrt_mul_conjTranspose_eq_one
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r) :
    let Q := Matrix.of fun r (j : Fin N) =>
      lanczosRecurrence (diagonal t) (fun r => Real.sqrt (w r)) j.val r
    Q * Qᴴ = 1 :=
  (hasOrthonormalCols_lanczosRecurrence_diagonal_sqrt t w ht hw).mul_conjTranspose_self

/-- The full actual Lanczos basis has the positive bordered mass identity, with monic
Stieltjes beta zero equal to total mass. The first coordinate is used only in positive order.
Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial)
@isnad1 id=other.3h3v.s7.758a79ab7e8e from=translated src=- shape=4414656c vocab=57ec8910
-/
theorem transpose_lanczosRecurrence_diagonal_sqrt_mulVec_sqrt_eq_single
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r) (hN : 0 < N) :
    let Q := Matrix.of fun r (j : Fin N) =>
      lanczosRecurrence (diagonal t) (fun r => Real.sqrt (w r)) j.val r
    Qᵀ *ᵥ (fun r => Real.sqrt (w r)) =
      Pi.single ⟨0, hN⟩ (Real.sqrt (discreteStieltjesMonicBeta t w 0)) := by
  dsimp only
  rw [recurrenceMatrix_eq_arnoldiMatrix (Matrix.isHermitian_diagonal t),
    discreteStieltjesMonicBeta_zero, ← norm_toLp_sqrt_eq_sqrt_sum w (fun r => (hw r).le)]
  apply transpose_arnoldiMatrix_mulVec_eq_single (diagonal t) _ hN
  rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]

/-- Before exact finite-support termination every positive-index actual Lanczos coupling
is positive. Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial)
@isnad1 id=lt.4h4v.s6.be6d4eda2f49 from=translated src=- shape=6ab7f38f vocab=712fe0e9
-/
theorem lanczosBeta_diagonal_sqrt_pos (t w : Fin N → ℝ) (ht : Function.Injective t)
    (hw : ∀ r, 0 < w r) {j : ℕ} (hj0 : 0 < j) (hj : j < N) :
    0 < lanczosBeta (diagonal t) (fun r => Real.sqrt (w r)) j := by
  apply lanczosBeta_pos (Matrix.isHermitian_diagonal t) _ hj0
  rwa [krylovGrade_diagonal_sqrt_eq_card t w ht hw]

/-- The actual finite-node Lanczos coupling vanishes at exact order `N`.
Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial)
@isnad1 id=eq.2h3v.s5.7d52de147f7e from=translated src=- shape=0dad9367 vocab=712fe0e9
-/
theorem lanczosBeta_diagonal_sqrt_eq_zero (t w : Fin N → ℝ) (ht : Function.Injective t)
    (hw : ∀ r, 0 < w r) :
    lanczosBeta (diagonal t) (fun r => Real.sqrt (w r)) N = 0 := by
  apply lanczosBeta_eq_zero_of_krylovGrade_le (Matrix.isHermitian_diagonal t)
  rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]

/-- Computed Stieltjes values are the actual Lanczos orthonormal polynomials evaluated at
the nodes. This identifies the value-only implementation with the polynomial procedure.
Source: Gautschi (2004), §2.2.3.1.
atlas: discrete-measure-jacobi-matrix (partial)
@isnad1 id=eq.3h5v.s6.226019774537 from=translated src=- shape=7941de13 vocab=331f18ea
-/
theorem discreteStieltjesValues_eq_eval_lanczosPoly
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r) {j : ℕ} (hj : j < N)
    (r : Fin N) :
    discreteStieltjesValues t w j r =
      (LanczosDecomp.poly (arnoldiDecomp (diagonal t) (fun r => Real.sqrt (w r)) N
        (by rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw])) j).eval (t r) := by
  have hq : N ≤ krylovGrade (diagonal t) (fun r => Real.sqrt (w r)) := by
    rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]
  let D : LanczosDecomp (diagonal t) (fun r => Real.sqrt (w r)) N :=
    arnoldiDecomp (diagonal t) (fun r => Real.sqrt (w r)) N hq
  have hpoly := D.Q_apply_diagonal_sqrt_eq_eval_poly_mul r ⟨j, hj⟩
  have hcur : D.Q r ⟨j, hj⟩ = lanczosRecurrence (diagonal t) (fun r => Real.sqrt (w r)) j r := by
    simp only [D, arnoldiDecomp_Q, arnoldiMatrix, lanczosRecurrence_eq_arnoldiBasis
      (Matrix.isHermitian_diagonal t), Matrix.of_apply]
  rw [hcur, lanczosRecurrence_diagonal_sqrt_eq_mul_discreteStieltjesValues t w
    (fun r => (hw r).le)] at hpoly
  exact mul_left_cancel₀ (Real.sqrt_pos.mpr (hw r)).ne' hpoly

/-- Values produced by the actual Stieltjes procedure obey the exact reciprocal-weight
dual orthogonality identity. Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial)
@isnad1 id=eq.2h5v.s6.c2f8528b8932 from=translated src=- shape=e13c4b5b vocab=1e19e483
-/
theorem sum_discreteStieltjesValues_mul_eq_div_weight
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r) (r s : Fin N) :
    (∑ j : Fin N, discreteStieltjesValues t w j.val r * discreteStieltjesValues t w j.val s) =
      (if r = s then 1 else 0) / w r := by
  have hq : N ≤ krylovGrade (diagonal t) (fun r => Real.sqrt (w r)) := by
    rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]
  let D : LanczosDecomp (diagonal t) (fun r => Real.sqrt (w r)) N :=
    arnoldiDecomp (diagonal t) (fun r => Real.sqrt (w r)) N hq
  have heval (j : Fin N) (r : Fin N) :
      discreteStieltjesValues t w j.val r = (D.poly j.val).eval (t r) :=
    discreteStieltjesValues_eq_eval_lanczosPoly t w ht hw j.isLt r
  simp_rw [heval]
  exact D.sum_eval_poly_mul_eval_poly_eq_div_weight hw r s

end NLAlib
