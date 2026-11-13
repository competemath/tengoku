import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.Shear
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.BlockCompression
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.NormBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Absorption in an arbitrary ambient coordinate space

The formulas use rectangular isometries for the first, second, and selected outside
blocks. This lets the same two shears be iterated without changing the ambient index type.
All norms below are Euclidean operator norms.
-/

open scoped Matrix.Norms.L2Operator
open Matrix

namespace NoEpsilon.Absorption

variable {n r k l : Type*}
  [Fintype n] [Fintype r] [Fintype k] [Fintype l]
  [DecidableEq n] [DecidableEq r] [DecidableEq k] [DecidableEq l]

/-- Conjugation by an elementary shear and its explicit inverse.-/
noncomputable def shear (A N : Matrix n n ℂ) : Matrix n n ℂ := (1 - N) * A * (1 + N)

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] in
/--
@isnad1 id=eq.2h7v.s7.99a9050418c6 from=translated src=- shape=ab72a7fd vocab=e2f721f7
-/
theorem compression_shear_eq (A N : Matrix n n ℂ)
    (L : Matrix k n ℂ) (R : Matrix n l ℂ) (hL : L * N = 0) (hR : N * R = 0) :
    L * shear A N * R = L * A * R := by
  have hleft : L * (1 - N) = L := by simp [Matrix.mul_sub, hL]
  have hright : (1 + N) * R = R := by simp [Matrix.add_mul, hR]
  calc
    L * shear A N * R = (L * (1 - N)) * A * ((1 + N) * R) := by
      simp only [shear, Matrix.mul_assoc]
    _ = L * A * R := by rw [hleft, hright]

omit [DecidableEq n] [DecidableEq r] [DecidableEq k] in
/--
@isnad1 id=eq.1h6v.s8.79a713b10d33 from=translated src=- shape=b5f8c207 vocab=c36fd414
-/
theorem square_zero_insertion (Q : Matrix n r ℂ) (X : Matrix r k ℂ)
    (V : Matrix n k ℂ) (hVQ : Vᴴ * Q = 0) :
    (Q * X * Vᴴ) * (Q * X * Vᴴ) = 0 := by
  calc
    _ = Q * X * (Vᴴ * Q) * X * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hVQ]; simp

/--
@isnad1 id=eq.1h3v.s6.616817197774 from=translated src=- shape=c96e2ae1 vocab=04059f83
-/
theorem shear_trace (A N : Matrix n n ℂ) (hN : N * N = 0) :
    trace (shear A N) = trace A := by
  rw [shear, trace_mul_cycle, NoEpsilon.Shear.one_add_mul_one_sub N hN, Matrix.one_mul]

omit [DecidableEq r] [DecidableEq k] in
/--
@isnad1 id=eq.2h8v.s8.98fb56a20d99 from=translated src=- shape=2a35e8e8 vocab=7eaf108e
-/
theorem first_shear_bridge (A : Matrix n n ℂ)
    (P Q : Matrix n r ℂ) (V : Matrix n k ℂ) (X : Matrix r k ℂ)
    (hPQ : Pᴴ * Q = 0) (hVQ : Vᴴ * Q = 0) :
    Pᴴ * shear A (Q * X * Vᴴ) * Q = Pᴴ * A * Q := by
  apply compression_shear_eq
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ]; simp
  · rw [Matrix.mul_assoc, hVQ]; simp

/--
@isnad1 id=eq.3h8v.s9.943c24ccf42f from=translated src=- shape=dc9870b5 vocab=9755d986
-/
theorem first_shear_new_bridge (A : Matrix n n ℂ)
    (P Q : Matrix n r ℂ) (V : Matrix n k ℂ) (J : Matrix r k ℂ)
    (hPQ : Pᴴ * Q = 0) (hVV : Vᴴ * V = 1) (hA : Pᴴ * A * Q = 1) :
    Pᴴ * shear A (Q * (J - Pᴴ * A * V) * Vᴴ) * V = J := by
  let X := J - Pᴴ * A * V
  have hleft : Pᴴ * (1 - Q * X * Vᴴ) = Pᴴ := by
    simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPQ, Matrix.zero_mul, sub_zero]
  have hright : (1 + Q * X * Vᴴ) * V = V + Q * X := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hVV, Matrix.mul_one]
  calc
    Pᴴ * shear A (Q * X * Vᴴ) * V =
        (Pᴴ * (1 - Q * X * Vᴴ)) * A * ((1 + Q * X * Vᴴ) * V) := by
      simp only [shear, Matrix.mul_assoc]
    _ = Pᴴ * A * (V + Q * X) := by rw [hleft, hright]
    _ = Pᴴ * A * V + (Pᴴ * A * Q) * X := by rw [Matrix.mul_add, ← Matrix.mul_assoc]
    _ = J := by rw [hA, Matrix.one_mul]; dsimp [X]; abel

omit [DecidableEq r] [DecidableEq k] in
/--
@isnad1 id=eq.2h8v.s8.906808191d2b from=translated src=- shape=d680d650 vocab=7eaf108e
-/
theorem second_shear_bridge (A : Matrix n n ℂ)
    (P Q : Matrix n r ℂ) (V : Matrix n k ℂ) (Y : Matrix k r ℂ)
    (hPV : Pᴴ * V = 0) (hPQ : Pᴴ * Q = 0) :
    Pᴴ * shear A (V * Y * Pᴴ) * Q = Pᴴ * A * Q := by
  apply compression_shear_eq
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPV]; simp
  · rw [Matrix.mul_assoc, hPQ]; simp

omit [DecidableEq r] in
/--
@isnad1 id=eq.4h7v.s9.6fca35a6d35d from=translated src=- shape=a2b3bba7 vocab=7eaf108e
-/
theorem second_shear_zero (A : Matrix n n ℂ)
    (P : Matrix n r ℂ) (V : Matrix n k ℂ) (J : Matrix r k ℂ)
    (hPV : Pᴴ * V = 0) (hVV : Vᴴ * V = 1) (hJ : Jᴴ * J = 1)
    (hA : Pᴴ * A * V = J) :
    Vᴴ * shear A (V * (Vᴴ * A * V * Jᴴ) * Pᴴ) * V = 0 := by
  let Y := Vᴴ * A * V * Jᴴ
  have hleft : Vᴴ * (1 - V * Y * Pᴴ) = Vᴴ - Y * Pᴴ := by
    simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hVV, Matrix.one_mul]
  have hright : (1 + V * Y * Pᴴ) * V = V := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hPV, Matrix.mul_zero, add_zero]
  calc
    Vᴴ * shear A (V * Y * Pᴴ) * V =
        (Vᴴ * (1 - V * Y * Pᴴ)) * A * ((1 + V * Y * Pᴴ) * V) := by
      simp only [shear, Matrix.mul_assoc]
    _ = (Vᴴ - Y * Pᴴ) * A * V := by rw [hleft, hright]
    _ = Vᴴ * A * V - Y * (Pᴴ * A * V) := by simp only [Matrix.sub_mul, Matrix.mul_assoc]
    _ = 0 := by
      rw [hA]
      dsimp [Y]
      rw [Matrix.mul_assoc (Vᴴ * A * V) Jᴴ J, hJ, Matrix.mul_one, sub_self]

omit [DecidableEq r] [DecidableEq k] [Fintype l] [DecidableEq l] in
/--
@isnad1 id=eq.2h9v.s8.6ce75c5facc4 from=translated src=- shape=dd55f36f vocab=7eaf108e
-/
theorem outside_shear_unchanged (A : Matrix n n ℂ)
    (Q : Matrix n r ℂ) (V : Matrix n k ℂ) (W : Matrix n l ℂ)
    (X : Matrix r k ℂ) (hWQ : Wᴴ * Q = 0) (hVW : Vᴴ * W = 0) :
    Wᴴ * shear A (Q * X * Vᴴ) * W = Wᴴ * A * W := by
  apply compression_shear_eq
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hWQ]; simp
  · rw [Matrix.mul_assoc, hVW]; simp

/-- The two shears preserve the identity corner and clear the selected outside block.
@isnad1 id=other.6h8v.s10.be8a7f4f6512 from=translated src=- shape=6c813b7d vocab=480852d8
-/
theorem two_shear_elimination (A : Matrix n n ℂ)
    (P Q : Matrix n r ℂ) (V : Matrix n k ℂ) (J : Matrix r k ℂ)
    (hPQ : Pᴴ * Q = 0) (hPV : Pᴴ * V = 0) (hVQ : Vᴴ * Q = 0)
    (hVV : Vᴴ * V = 1) (hJ : Jᴴ * J = 1) (hA : Pᴴ * A * Q = 1) :
    let N := Q * (J - Pᴴ * A * V) * Vᴴ
    let A' := shear A N
    let M := V * (Vᴴ * A' * V * Jᴴ) * Pᴴ
    Pᴴ * shear A' M * Q = 1 ∧ Vᴴ * shear A' M * V = 0 ∧
      trace (shear A' M) = trace A := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [second_shear_bridge _ P Q V _ hPV hPQ,
      first_shear_bridge _ P Q V _ hPQ hVQ, hA]
  · exact second_shear_zero _ P V J hPV hVV hJ
      (first_shear_new_bridge A P Q V J hPQ hVV hA)
  · rw [shear_trace _ _ (square_zero_insertion V _ P hPV),
      shear_trace _ _ (square_zero_insertion Q _ V hVQ)]

omit [DecidableEq n] in
/-- Any rectangular isometry has operator norm at most one, including an empty domain.
@isnad1 id=le.1h3v.s6.c805e48d0009 from=translated src=- shape=d0d178c1 vocab=0a2d07c7
-/
theorem isometry_norm_le (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) : ‖V‖ ≤ 1 := by
  have hs := Matrix.l2_opNorm_conjTranspose_mul_self V
  rw [hV] at hs
  have hn := NoEpsilon.matrix_norm_one_le (ι := k)
  rw [hs] at hn
  nlinarith [norm_nonneg V]

/--
@isnad1 id=le.2h6v.s7.0e6feba87957 from=translated src=- shape=592ed40c vocab=c84693a9
-/
theorem compression_norm_le (A : Matrix n n ℂ)
    (P : Matrix n r ℂ) (V : Matrix n k ℂ) (hP : ‖P‖ ≤ 1) (hV : ‖V‖ ≤ 1) :
    ‖Pᴴ * A * V‖ ≤ ‖A‖ := by
  calc
    _ ≤ (‖Pᴴ‖ * ‖A‖) * ‖V‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1 * ‖A‖) * 1 := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = ‖A‖ := by ring

/--
@isnad1 id=le.2h6v.s7.c9ebe8b9c261 from=translated src=- shape=eee561a8 vocab=c84693a9
-/
theorem insertion_norm_le (Q : Matrix n r ℂ) (V : Matrix n k ℂ)
    (X : Matrix r k ℂ) (hQ : ‖Q‖ ≤ 1) (hV : ‖V‖ ≤ 1) :
    ‖Q * X * Vᴴ‖ ≤ ‖X‖ := by
  calc
    _ ≤ (‖Q‖ * ‖X‖) * ‖Vᴴ‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1 * ‖X‖) * 1 := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = ‖X‖ := by ring

set_option maxHeartbeats 2000000 in
-- Matrix and finite-sum calculations require additional elaboration steps.
/--
@isnad1 id=and.0h2v.s7.5f61fea59142 from=translated src=- shape=f64c7fdb vocab=17ff3725
-/
theorem shear_factor_norm_le (N : Matrix n n ℂ) :
    ‖1 - N‖ ≤ 1 + ‖N‖ ∧ ‖1 + N‖ ≤ 1 + ‖N‖ := by
  have hOne : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := NoEpsilon.matrix_norm_one_le
  constructor
  · exact (norm_sub_le (1 : Matrix n n ℂ) N).trans (add_le_add hOne le_rfl)
  · exact (norm_add_le (1 : Matrix n n ℂ) N).trans (add_le_add hOne le_rfl)

/-- Norm growth after the first of the two outside-block shears.-/
def firstBudget (a : ℝ) : ℝ := a * (a + 2) ^ 2

/-- Norm growth after clearing one outside block.-/
def stepBudget (a : ℝ) : ℝ := firstBudget a * (1 + firstBudget a) ^ 2

/-- The condition-number budget of one complete absorption step.-/
def stepCondition (a : ℝ) : ℝ := (a + 2) ^ 2 * (1 + firstBudget a) ^ 2

universe u

-- Preserve the existing parameter list for downstream callers.

end NoEpsilon.Absorption
