import Tengoku.Seed.Analysis.CStarAlgebra.Matrix
import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Seed.Data.Matrix.Block
import Tengoku.Seed.LinearAlgebra.Matrix.Hermitian
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The recursive skew-Hadamard family

The indexing type records the original recursive coordinates. All matrix norms in this file are
the Euclidean operator norm.
-/

open scoped ComplexConjugate
open Matrix

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedSpace Matrix.instCStarRing

namespace PavingSeparation

/-- Original coordinates of a matrix of order `2 ^ m`.-/
@[reducible] def Cube : ℕ → Type
  | 0 => Fin 1
  | m + 1 => Cube m ⊕ Cube m

@[reducible] def cubeFintype : (m : ℕ) → Fintype (Cube m)
  | 0 => inferInstanceAs (Fintype (Fin 1))
  | m + 1 => letI := cubeFintype m; inferInstanceAs (Fintype (Cube m ⊕ Cube m))

attribute [instance] cubeFintype

@[reducible] def cubeDecidableEq : (m : ℕ) → DecidableEq (Cube m)
  | 0 => inferInstanceAs (DecidableEq (Fin 1))
  | m + 1 => letI := cubeDecidableEq m; inferInstanceAs (DecidableEq (Cube m ⊕ Cube m))

attribute [instance] cubeDecidableEq

def origin : (m : ℕ) → Cube m
  | 0 => 0
  | m + 1 => Sum.inl (origin m)

instance (m : ℕ) : Inhabited (Cube m) := ⟨origin m⟩

@[simp] theorem card_cube (m : ℕ) : Fintype.card (Cube m) = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change Fintype.card (Cube m ⊕ Cube m) = 2 ^ (m + 1)
      simp [ih, pow_succ, Nat.mul_two]

/-- The skew-Hadamard doubling recursion in the original coordinates.-/
noncomputable def skewMatrix : (m : ℕ) → Matrix (Cube m) (Cube m) ℂ
  | 0 => 0
  | m + 1 => fromBlocks (skewMatrix m) (skewMatrix m + 1) (skewMatrix m - 1) (-skewMatrix m)

@[simp] theorem skew_zero : skewMatrix 0 = 0 := rfl

theorem skew_succ (m : ℕ) :
    skewMatrix (m + 1) =
      fromBlocks (skewMatrix m) (skewMatrix m + 1) (skewMatrix m - 1) (-skewMatrix m) := rfl

@[simp] theorem skew_inl_inl (m : ℕ) (i j : Cube m) :
    skewMatrix (m + 1) (Sum.inl i) (Sum.inl j) = skewMatrix m i j := rfl

@[simp] theorem skew_inr_inr (m : ℕ) (i j : Cube m) :
    skewMatrix (m + 1) (Sum.inr i) (Sum.inr j) = -skewMatrix m i j := rfl

@[simp] theorem skew_inl_inr (m : ℕ) (i j : Cube m) :
    skewMatrix (m + 1) (Sum.inl i) (Sum.inr j) = (skewMatrix m + 1) i j := rfl

@[simp] theorem skew_inr_inl (m : ℕ) (i j : Cube m) :
    skewMatrix (m + 1) (Sum.inr i) (Sum.inl j) = (skewMatrix m - 1) i j := rfl

@[simp] theorem skew_diag (m : ℕ) (i : Cube m) : skewMatrix m i i = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => cases i <;> simp [ih]

theorem skew_offdiag_eq_one_or_neg_one (m : ℕ) {i j : Cube m} (hij : i ≠ j) :
    skewMatrix m i j = 1 ∨ skewMatrix m i j = -1 := by
  induction m with
  | zero => exact (hij (Subsingleton.elim _ _)).elim
  | succ m ih =>
      cases i with
      | inl i =>
          cases j with
          | inl j => exact ih (fun h ↦ hij (congrArg Sum.inl h))
          | inr j =>
              by_cases h : i = j
              · subst j; simp
              · simpa [h] using ih h
      | inr i =>
          cases j with
          | inl j =>
              by_cases h : i = j
              · subst j; simp
              · simpa [h] using ih h
          | inr j =>
              rcases ih (fun h ↦ hij (congrArg Sum.inr h)) with h | h
              · simp [h]
              · simp [h]

@[simp] theorem skew_offdiag_norm (m : ℕ) {i j : Cube m} (hij : i ≠ j) :
    ‖skewMatrix m i j‖ = 1 := by
  rcases skew_offdiag_eq_one_or_neg_one m hij with h | h <;> simp [h]

@[simp] theorem skew_conj_apply (m : ℕ) (i j : Cube m) :
    star (skewMatrix m i j) = skewMatrix m i j := by
  by_cases hij : i = j
  · subst j; simp
  · rcases skew_offdiag_eq_one_or_neg_one m hij with h | h <;> simp [h]

theorem skew_conjTranspose (m : ℕ) : (skewMatrix m)ᴴ = -skewMatrix m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [skew_succ, fromBlocks_conjTranspose, fromBlocks_neg]
      simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_neg, conjTranspose_one, ih]
      congr 1 <;> abel

theorem skew_transpose (m : ℕ) : (skewMatrix m)ᵀ = -skewMatrix m := by
  ext i j
  have h := congrFun (congrFun (skew_conjTranspose m) i) j
  simpa only [conjTranspose_apply, skew_conj_apply, transpose_apply] using h

/-- The normalized Hermitian skew-Hadamard family; at depth zero it is zero.-/
noncomputable def pavingMatrix (m : ℕ) : Matrix (Cube m) (Cube m) ℂ :=
  (Complex.I / (Real.sqrt ((2 : ℝ) ^ m - 1) : ℂ)) • skewMatrix m

@[simp] theorem family_zero : pavingMatrix 0 = 0 := by simp [pavingMatrix]

@[simp] theorem family_diag (m : ℕ) (i : Cube m) : pavingMatrix m i i = 0 := by
  simp [pavingMatrix]

@[simp] theorem family_trace (m : ℕ) : Matrix.trace (pavingMatrix m) = 0 := by
  simp [Matrix.trace]

end PavingSeparation
