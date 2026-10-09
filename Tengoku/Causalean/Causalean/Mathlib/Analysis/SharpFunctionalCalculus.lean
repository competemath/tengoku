module
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.DiagonalizableFunctionalCalculus

/-! # Sharp collision-safe two-diagonalizer functional calculus -/

@[expose] public section

namespace Causalean.Mathlib.Analysis

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- A columnwise Euclidean envelope controls the operator norm with only the square root of the
number of columns. -/
lemma matrix_norm_le_sqrt_card_mul_of_column_norm_le
    {rows cols : ℕ} (A : RectMatrix rows cols) {M : ℝ} (hM : 0 ≤ M)
    (hcol : ∀ j, ‖(WithLp.toLp 2 (fun i => A i j) : Euc rows)‖ ≤ M) :
    ‖A‖ ≤ Real.sqrt cols * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) hM)
  intro x
  let c : Fin cols → Euc rows := fun j => WithLp.toLp 2 (fun i => A i j)
  have haction : Matrix.toEuclideanLin A x = ∑ j, x j • c j := by
    apply PiLp.ext
    intro i
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, c, mul_comm]
  change ‖Matrix.toEuclideanLin A x‖ ≤ _
  rw [haction]
  calc
    ‖∑ j, x j • c j‖ ≤ ∑ j, ‖x j • c j‖ := norm_sum_le Finset.univ _
    _ ≤ ∑ j, |x j| * M := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hcol j) (abs_nonneg _)
    _ = M * ∑ j, |x j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ M * (Real.sqrt cols * ‖x‖) := by
      gcongr
      let one : Euc cols := WithLp.toLp 2 (fun _ => (1 : ℝ))
      let ax : Euc cols := WithLp.toLp 2 (fun j => |x j|)
      have hinner : ∑ j, |x j| = inner ℝ one ax := by
        simp [one, ax, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      rw [hinner]
      calc
        inner ℝ one ax ≤ |inner ℝ one ax| := le_abs_self _
        _ ≤ ‖one‖ * ‖ax‖ := abs_real_inner_le_norm _ _
        _ = Real.sqrt cols * ‖x‖ := by
          congr 1
          · rw [EuclideanSpace.norm_eq]
            simp [one]
          · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
            simp [ax, Real.norm_eq_abs]
    _ = (Real.sqrt cols * M) * ‖x‖ := by ring

/-- Collision-safe divided differences in the two unrelated eigenbases. -/
noncomputable def crossDividedDifference {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B) (f : ℝ → ℝ) :
    RectMatrix n n := fun i j =>
  if DA.eigenvalue i = DB.eigenvalue j then 0
  else (f (DA.eigenvalue i) - f (DB.eigenvalue j)) /
    (DA.eigenvalue i - DB.eigenvalue j)

/-- Cross-coordinate perturbation between two unrelated diagonalizers. -/
noncomputable def crossPerturbation {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B) : RectMatrix n n :=
  DA.basisInv * (A - B) * DB.basis

/-- [Two real diagonalizations and a scalar function](hyp:n,A,B,DA,DB,f) determine [their entrywise divided-difference perturbation matrix](goal). -/
noncomputable def crossHadamard {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B) (f : ℝ → ℝ) :
    RectMatrix n n := fun i j =>
  crossDividedDifference DA DB f i j * crossPerturbation DA DB i j

/-- [Two real diagonalizations and coordinate indices](hyp:n,A,B,DA,DB,i,j) give [the eigenvalue-difference formula for one cross-coordinate perturbation](goal). -/
lemma crossPerturbation_entry
    {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B) (i j : Fin n) :
    crossPerturbation DA DB i j =
      (DA.eigenvalue i - DB.eigenvalue j) * (DA.basisInv * DB.basis) i j := by
  have hA : DA.basisInv * A * DB.basis =
      Matrix.diagonal DA.eigenvalue * (DA.basisInv * DB.basis) := by
    have hr := congrArg (fun X : RectMatrix n n => DA.basisInv * X * DB.basis)
      DA.reconstruct
    calc
      _ = DA.basisInv * (DA.basis * Matrix.diagonal DA.eigenvalue * DA.basisInv) *
          DB.basis := hr
      _ = _ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc DA.basisInv DA.basis, DA.inv_mul_basis,
          Matrix.one_mul]
  have hB : DA.basisInv * B * DB.basis =
      (DA.basisInv * DB.basis) * Matrix.diagonal DB.eigenvalue := by
    have hr := congrArg (fun X : RectMatrix n n => DA.basisInv * X * DB.basis)
      DB.reconstruct
    calc
      _ = DA.basisInv * (DB.basis * Matrix.diagonal DB.eigenvalue * DB.basisInv) *
          DB.basis := hr
      _ = _ := by
        simp only [Matrix.mul_assoc]
        rw [DB.inv_mul_basis, Matrix.mul_one]
  have hE : crossPerturbation DA DB =
      Matrix.diagonal DA.eigenvalue * (DA.basisInv * DB.basis) -
        (DA.basisInv * DB.basis) * Matrix.diagonal DB.eigenvalue := by
    unfold crossPerturbation
    rw [Matrix.mul_sub, Matrix.sub_mul, hA, hB]
  rw [hE]
  simp [Matrix.mul_apply, Matrix.diagonal_apply]
  ring

/-- [Two real diagonalizations and a scalar function](hyp:n,A,B,DA,DB,f) give [the factorization of their functional-calculus difference through the cross Hadamard matrix](goal). -/
lemma applyFunction_sub_eq_crossHadamard
    {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B) (f : ℝ → ℝ) :
    DA.applyFunction f - DB.applyFunction f =
      DA.basis * crossHadamard DA DB f * DB.basisInv := by
  let C := DA.basisInv * DB.basis
  let H : RectMatrix n n := fun i j =>
    crossDividedDifference DA DB f i j * crossPerturbation DA DB i j
  have hH (i j : Fin n) : H i j =
      (f (DA.eigenvalue i) - f (DB.eigenvalue j)) * C i j := by
    dsimp [H, crossDividedDifference]
    rw [crossPerturbation_entry DA DB]
    by_cases hij : DA.eigenvalue i = DB.eigenvalue j
    · simp [hij]
    · rw [ite_eq_right hij]
      field_simp [sub_ne_zero.mpr hij]
      rfl
  have hcoord : H = Matrix.diagonal (f ∘ DA.eigenvalue) * C -
      C * Matrix.diagonal (f ∘ DB.eigenvalue) := by
    ext i j
    rw [hH]
    simp [C, Matrix.mul_apply, Matrix.diagonal_apply, Function.comp_apply]
    ring
  unfold RealDiagonalization.applyFunction
  change _ = DA.basis * H * DB.basisInv
  rw [show DA.basis * H * DB.basisInv =
      DA.basis * (Matrix.diagonal (f ∘ DA.eigenvalue) * C) * DB.basisInv -
        DA.basis * (C * Matrix.diagonal (f ∘ DB.eigenvalue)) * DB.basisInv by
      rw [hcoord, Matrix.mul_sub, Matrix.sub_mul]]
  dsimp [C]
  simp only [Matrix.mul_assoc]
  rw [DB.basis_mul_inv, Matrix.mul_one,
    ← Matrix.mul_assoc DA.basis DA.basisInv, DA.basis_mul_inv, Matrix.one_mul]

end

end Causalean.Mathlib.Analysis
