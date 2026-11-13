import Tengoku.Nlalib.NLAlib.Matrix.Norms.Core
import Tengoku.Seed.Analysis.Matrix.Order
import Tengoku.Seed.Tactic.Module
import Tengoku.Seed.Data.Matrix.ColumnRowPartitioned

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite Stein Gramians and Smith doubling

All iterates are actual finite sums. The exact error and residual identities
hold for any solution, independent of convergence assumptions.
-/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib

variable {K n : Type*} [RCLike K] [Fintype n] [DecidableEq n]

/-- The first `N` terms of the Stein Gramian series.-/
def steinPartialSum (A Q : Matrix n n K) (N : ℕ) : Matrix n n K :=
  ∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j

/--
@isnad1 id=eq.0h4v.s6.80ec9184db37 from=translated src=- shape=8ed3772e vocab=98201606
-/
@[simp] theorem steinPartialSum_zero (A Q : Matrix n n K) : steinPartialSum A Q 0 = 0 := by
  simp [steinPartialSum]

/-- The sum update adds the actual next Gramian term.
@isnad1 id=eq.0h5v.s8.c1afd0b02af4 from=translated src=- shape=6f4198c9 vocab=467cd25f
-/
theorem steinPartialSum_succ (A Q : Matrix n n K) (N : ℕ) :
    steinPartialSum A Q (N + 1) = steinPartialSum A Q N + A ^ N * Q * (Aᴴ) ^ N := by
  exact Finset.sum_range_succ _ _

/-- Splitting a finite Gramian sum at an arbitrary point.
@isnad1 id=eq.0h6v.s8.ea5731113e43 from=translated src=- shape=482502fd vocab=467cd25f
-/
theorem steinPartialSum_add (A Q : Matrix n n K) (M N : ℕ) :
    steinPartialSum A Q (M + N) = steinPartialSum A Q M +
      A ^ M * steinPartialSum A Q N * (Aᴴ) ^ M := by
  unfold steinPartialSum
  rw [Finset.sum_range_add]
  congr 1
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [pow_add, Matrix.mul_assoc]
  rw [pow_mul_comm (Aᴴ) j M]

/-- Exact finite-prefix error for every solution of the Stein equation.
Source: user derivations, equation (G5).
atlas: stein-gramian-smith-doubling (partial)
@isnad1 id=eq.1h6v.s9.673c99f10372 from=translated src=- shape=1912fbbc vocab=478bf723
-/
theorem sub_steinPartialSum_eq (A Q X : Matrix n n K) (hX : X - A * X * Aᴴ = Q) (N : ℕ) :
    X - steinPartialSum A Q N = A ^ N * X * (Aᴴ) ^ N := by
  induction N with
  | zero => simp
  | succ N hN =>
    rw [steinPartialSum_succ, ← sub_sub, hN, ← hX, Matrix.mul_sub, Matrix.sub_mul]
    rw [pow_succ, pow_succ']
    simp only [Matrix.mul_assoc]
    abel

/-- The residual is precisely the shifted next Gramian term.
atlas: stein-gramian-smith-doubling (partial)
@isnad1 id=eq.0h5v.s9.f97b01a97d01 from=translated src=- shape=6fc57b28 vocab=03b36188
-/
theorem steinPartialSum_residual (A Q : Matrix n n K) (N : ℕ) :
    Q - steinPartialSum A Q N + A * steinPartialSum A Q N * Aᴴ =
      A ^ N * Q * (Aᴴ) ^ N := by
  induction N with
  | zero => simp
  | succ N hN =>
    rw [steinPartialSum_succ]
    simp only [Matrix.mul_add, Matrix.add_mul]
    have heq : Q - (steinPartialSum A Q N + A ^ N * Q * (Aᴴ) ^ N) +
        (A * steinPartialSum A Q N * Aᴴ + A * (A ^ N * Q * (Aᴴ) ^ N) * Aᴴ) =
        (Q - steinPartialSum A Q N + A * steinPartialSum A Q N * Aᴴ) -
          A ^ N * Q * (Aᴴ) ^ N + A * (A ^ N * Q * (Aᴴ) ^ N) * Aᴴ := by abel
    rw [heq, hN, sub_self, zero_add, pow_succ', pow_succ]
    simp only [Matrix.mul_assoc]

/-- Finite Stein sums are PSD for PSD forcing.
@isnad1 id=possemid.1h5v.s6.aa86375464e7 from=translated src=- shape=eba9f829 vocab=9ffb4d6d
-/
theorem posSemidef_steinPartialSum (A Q : Matrix n n K) (hQ : Q.PosSemidef) (N : ℕ) :
    (steinPartialSum A Q N).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro j _
  simpa only [Matrix.conjTranspose_pow] using hQ.mul_mul_conjTranspose_same (A ^ j)

/-- The actual finite Gramian sequence is Loewner monotone.
@isnad1 id=monotone.1h4v.s6.fd7029fbdd3f from=translated src=- shape=1ee14d7f vocab=5bf54977
-/
theorem monotone_steinPartialSum (A Q : Matrix n n K) (hQ : Q.PosSemidef) :
    Monotone (steinPartialSum A Q) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [Matrix.le_iff, steinPartialSum_succ, add_sub_cancel_left]
  simpa only [Matrix.conjTranspose_pow] using hQ.mul_mul_conjTranspose_same (A ^ N)

/-- The actual Smith doubling process, storing its current power and Gramian.-/
def smithDoubling (A Q : Matrix n n K) : ℕ → Matrix n n K × Matrix n n K
  | 0 => (A, Q)
  | j + 1 => let (P, G) := smithDoubling A Q j
             (P * P, G + P * G * Pᴴ)

/-- Smith doubling produces the exact dyadic power and finite Gramian.
Source: user derivations, Smith doubling.
atlas: stein-gramian-smith-doubling (partial)
@isnad1 id=eq.0h5v.s7.35e15aad60fd from=translated src=- shape=298d1147 vocab=acfa50b0
-/
theorem smithDoubling_eq (A Q : Matrix n n K) (j : ℕ) :
    smithDoubling A Q j = (A ^ (2 ^ j), steinPartialSum A Q (2 ^ j)) := by
  induction j with
  | zero => simp [smithDoubling, steinPartialSum]
  | succ j hj =>
    rw [smithDoubling, hj]
    simp only [pow_succ, Nat.mul_two]
    rw [pow_add, steinPartialSum_add]
    simp [Matrix.conjTranspose_pow]

omit [DecidableEq n] in
/-- Factored Smith doubling concatenates the old factor and its propagated
copy. This is an exact factor update; column counts double without compression.
@isnad1 id=eq.0h5v.s9.daab14a51ee5 from=translated src=- shape=f6e0bcb2 vocab=3cc6b9f6
-/
theorem smithDoubling_factor_step {s : Type*} [Fintype s] (P : Matrix n n K)
    (Z : Matrix n s K) :
    Z * Zᴴ + P * (Z * Zᴴ) * Pᴴ =
      Matrix.fromCols Z (P * Z) * (Matrix.fromCols Z (P * Z))ᴴ := by
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows]
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end NLAlib
