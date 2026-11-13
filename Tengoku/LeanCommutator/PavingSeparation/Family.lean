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

/--
@isnad1 id=eq.0h1v.s4.212c6aad77bd from=translated src=- shape=5b09d1d5 vocab=50063f55
-/
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

/--
@isnad1 id=eq.0h0v.s6.a9a7739e7985 from=translated src=- shape=b96ef4e3 vocab=7cc312bb
-/
@[simp] theorem skew_zero : skewMatrix 0 = 0 := rfl

/--
@isnad1 id=eq.0h1v.s7.1c18c236dc36 from=translated src=- shape=2bbd2bd2 vocab=ba81373b
-/
theorem skew_succ (m : ℕ) :
    skewMatrix (m + 1) =
      fromBlocks (skewMatrix m) (skewMatrix m + 1) (skewMatrix m - 1) (-skewMatrix m) := rfl

/--
@isnad1 id=eq.0h3v.s5.3ba1e50fe63f from=translated src=- shape=656be366 vocab=c1752135
-/
@[simp] theorem skew_inl_inl (m : ℕ) (i j : Cube m) :
    skewMatrix (m + 1) (Sum.inl i) (Sum.inl j) = skewMatrix m i j := rfl

/--
@isnad1 id=eq.0h3v.s5.47be3c3de3d4 from=translated src=- shape=70a192fb vocab=ac6adfab
-/
@[simp] theorem skew_inr_inr (m : ℕ) (i j : Cube m) :
    skewMatrix (m + 1) (Sum.inr i) (Sum.inr j) = -skewMatrix m i j := rfl

/--
@isnad1 id=eq.0h3v.s6.a28fe514b0d7 from=translated src=- shape=d6f1d1f4 vocab=c5f4d286
-/
@[simp] theorem skew_inl_inr (m : ℕ) (i j : Cube m) :
    skewMatrix (m + 1) (Sum.inl i) (Sum.inr j) = (skewMatrix m + 1) i j := rfl

/--
@isnad1 id=eq.0h3v.s6.424cb0b459ba from=translated src=- shape=0a3d624c vocab=c0ecf619
-/
@[simp] theorem skew_inr_inl (m : ℕ) (i j : Cube m) :
    skewMatrix (m + 1) (Sum.inr i) (Sum.inl j) = (skewMatrix m - 1) i j := rfl

/--
@isnad1 id=eq.0h2v.s4.c328cb54702c from=translated src=- shape=48892474 vocab=c1bc6751
-/
@[simp] theorem skew_diag (m : ℕ) (i : Cube m) : skewMatrix m i i = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => cases i <;> simp [ih]

/--
@isnad1 id=or.1h3v.s5.d66a85342462 from=translated src=- shape=a0de62c7 vocab=4af955dc
-/
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

/--
@isnad1 id=eq.1h3v.s4.443f819f471c from=translated src=- shape=532784c3 vocab=ddf7eac3
-/
@[simp] theorem skew_offdiag_norm (m : ℕ) {i j : Cube m} (hij : i ≠ j) :
    ‖skewMatrix m i j‖ = 1 := by
  rcases skew_offdiag_eq_one_or_neg_one m hij with h | h <;> simp [h]

/--
@isnad1 id=eq.0h3v.s5.43bd9267a981 from=translated src=- shape=b9ce62d4 vocab=f4985746
-/
@[simp] theorem skew_conj_apply (m : ℕ) (i j : Cube m) :
    star (skewMatrix m i j) = skewMatrix m i j := by
  by_cases hij : i = j
  · subst j; simp
  · rcases skew_offdiag_eq_one_or_neg_one m hij with h | h <;> simp [h]

/--
@isnad1 id=eq.0h1v.s5.72ac308e8ab5 from=translated src=- shape=61ced77b vocab=32490e0b
-/
theorem skew_conjTranspose (m : ℕ) : (skewMatrix m)ᴴ = -skewMatrix m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [skew_succ, fromBlocks_conjTranspose, fromBlocks_neg]
      simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_neg, conjTranspose_one, ih]
      congr 1 <;> abel

/--
@isnad1 id=eq.0h1v.s5.078c31872aa0 from=translated src=- shape=61ced77b vocab=63f41316
-/
theorem skew_transpose (m : ℕ) : (skewMatrix m)ᵀ = -skewMatrix m := by
  ext i j
  have h := congrFun (congrFun (skew_conjTranspose m) i) j
  simpa only [conjTranspose_apply, skew_conj_apply, transpose_apply] using h

/-- The normalized Hermitian skew-Hadamard family; at depth zero it is zero.-/
noncomputable def pavingMatrix (m : ℕ) : Matrix (Cube m) (Cube m) ℂ :=
  (Complex.I / (Real.sqrt ((2 : ℝ) ^ m - 1) : ℂ)) • skewMatrix m

/--
@isnad1 id=eq.0h0v.s6.18cdc4ee4366 from=translated src=- shape=b96ef4e3 vocab=37c849b2
-/
@[simp] theorem family_zero : pavingMatrix 0 = 0 := by simp [pavingMatrix]

/--
@isnad1 id=eq.0h2v.s4.346391aad9aa from=translated src=- shape=48892474 vocab=f8c93648
-/
@[simp] theorem family_diag (m : ℕ) (i : Cube m) : pavingMatrix m i i = 0 := by
  simp [pavingMatrix]

/--
@isnad1 id=eq.0h1v.s4.c35e3c9589dd from=translated src=- shape=5dbf83be vocab=cacdc700
-/
@[simp] theorem family_trace (m : ℕ) : Matrix.trace (pavingMatrix m) = 0 := by
  simp [Matrix.trace]

end PavingSeparation
