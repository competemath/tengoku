import Tengoku.WasowAsymptoticsLean.WasowShiftReduction
import Tengoku.Seed.Data.Matrix.Block

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms WasowMultiShiftReduction.block_assemble` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowMultiShiftReduction.block_jordanShift_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowMultiShiftReduction.block_mul_jordanShift` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowMultiShiftReduction.exists_multishift_step` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowMultiShiftReduction.exists_formal_multishift_reduction` (it only prints; the queue checks the axioms of every declaration). -/

/-! All-order formal row normalization for any finite family of nilpotent
Jordan shift blocks. Each rectangular coefficient equation is solved using the
proved row recurrence, then assembled into the actual full matrix equation.
A leading matrix in the given Jordan-block coordinates is the only normal-form
hypothesis; neither a formal gauge nor a future reduction is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowMultiShiftReduction
open WasowShiftReduction

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Each block has positive size `h a + 1`; the whole family may be empty.-/
abbrev Index (h : σ → ℕ) := Σ a, Fin (h a + 1)

/-- The actual dependent block diagonal matrix of nilpotent shifts.-/
def jordanShift (h : σ → ℕ) : Matrix (Index h) (Index h) ℂ :=
  Matrix.blockDiagonal' (fun a => shift (h a))

/-- Extract the rectangular block with row block `a` and column block `b`.-/
def block {h : σ → ℕ} (P : Matrix (Index h) (Index h) ℂ) (a b : σ) :
    Matrix (Fin (h a + 1)) (Fin (h b + 1)) ℂ :=
  fun i j => P ⟨a, i⟩ ⟨b, j⟩

/-- Assemble all rectangular blocks, including off-diagonal ones.-/
def assemble {h : σ → ℕ}
    (P : ∀ a b, Matrix (Fin (h a + 1)) (Fin (h b + 1)) ℂ) :
    Matrix (Index h) (Index h) ℂ :=
  fun i j => P i.1 j.1 i.2 j.2

omit [Fintype σ] [DecidableEq σ] in
/--
@isnad1 id=eq.0h5v.s6.d62af6b0ce15 from=translated src=- shape=18b8ce0e vocab=2245c44b
-/
@[simp] theorem block_assemble {h : σ → ℕ}
    (P : ∀ a b, Matrix (Fin (h a + 1)) (Fin (h b + 1)) ℂ) (a b : σ) :
    block (assemble P) a b = P a b := rfl

/-- Left multiplication selects exactly the corresponding row shift block.
@isnad1 id=eq.0h5v.s8.35b4c94c61fe from=translated src=- shape=5526c85e vocab=59ac3878
-/
theorem block_jordanShift_mul (h : σ → ℕ)
    (P : Matrix (Index h) (Index h) ℂ) (a b : σ) :
    block (jordanShift h * P) a b = shift (h a) * block P a b := by
  ext i j
  simp only [block, jordanShift, Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single a]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro c hca
    apply Finset.sum_eq_zero
    intro l hl
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hca.symm, zero_mul]

/-- Right multiplication selects exactly the corresponding column shift block.
@isnad1 id=eq.0h5v.s8.1065b1bc849d from=translated src=- shape=215f35bb vocab=59ac3878
-/
theorem block_mul_jordanShift (h : σ → ℕ)
    (P : Matrix (Index h) (Index h) ℂ) (a b : σ) :
    block (P * jordanShift h) a b = block P a b * shift (h b) := by
  ext i j
  simp only [block, jordanShift, Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single b]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro c hcb
    apply Finset.sum_eq_zero
    intro l hl
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hcb, mul_zero]

/-- An actual full coefficient step for arbitrary many shift blocks. The first
row of every gauge block vanishes; only the last row of each transformed block
is allowed to remain. Existence, rather than an unnecessary uniqueness claim,
is the conclusion.
@isnad1 id=ex.0h3v.s9.c1f04ea8e96f from=translated src=- shape=3debd5e2 vocab=08ac5bd0
-/
theorem exists_multishift_step (h : σ → ℕ)
    (H : Matrix (Index h) (Index h) ℂ) :
    ∃ P B : Matrix (Index h) (Index h) ℂ,
      (∀ a b j, P ⟨a, 0⟩ ⟨b, j⟩ = 0) ∧
      (∀ a b i j, i.val < h a → B ⟨a, i⟩ ⟨b, j⟩ = 0) ∧
      jordanShift h * P - P * jordanShift h = B + H := by
  choose p b hp hb heq using fun a b =>
    exists_rectangular_step (shift (h b)) (block H a b)
  refine ⟨assemble p, assemble b, ?_, ?_, ?_⟩
  · intro a c j
    exact hp a c j
  · intro a c i j hi
    exact hb a c i j hi
  · ext ⟨a, i⟩ ⟨c, j⟩
    change (block (jordanShift h * assemble p) a c) i j -
      (block (assemble p * jordanShift h) a c) i j =
      b a c i j + (block H a c) i j
    rw [block_jordanShift_mul, block_mul_jordanShift, block_assemble]
    exact congrFun (congrFun (heq a c) i) j

/-- The complete formal coefficient recursion for an arbitrary finite family
of nilpotent shift blocks. Constant coefficients are retained, and the row
normalizations apply to every positive order.
@isnad1 id=ex.2h4v.s9.60b27b45f5e6 from=translated src=- shape=76225744 vocab=62dab193
-/
theorem exists_formal_multishift_reduction (h : σ → ℕ)
    (A : ℕ → Matrix (Index h) (Index h) ℂ)
    (hA : A 0 = jordanShift h) {q : ℕ} (hq : 0 < q) :
    ∃ P B : ℕ → Matrix (Index h) (Index h) ℂ,
      P 0 = 1 ∧ B 0 = A 0 ∧
      (∀ k a b j, P (k + 1) ⟨a, 0⟩ ⟨b, j⟩ = 0) ∧
      (∀ k a b i j, i.val < h a → B (k + 1) ⟨a, i⟩ ⟨b, j⟩ = 0) ∧
      ∀ k, (∑ i ∈ Finset.range (k + 1),
        (A (k - i) * P i - P i * B (k - i))) =
          -WasowFormalRecurrence.derivativeCoeff q P k := by
  apply WasowRecurrencePrinciple.exists_formal_reduction_of_step A hq
    (fun p => ∀ a b j, p ⟨a, 0⟩ ⟨b, j⟩ = 0)
    (fun b => ∀ a c i j, i.val < h a → b ⟨a, i⟩ ⟨c, j⟩ = 0)
  intro H
  simpa only [hA] using exists_multishift_step h H

end WasowMultiShiftReduction
