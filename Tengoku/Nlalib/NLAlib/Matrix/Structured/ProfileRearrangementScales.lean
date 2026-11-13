import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
import Tengoku.Seed.Analysis.Real.Sqrt
import Tengoku.Seed.Order.Monotone.Basic
import Tengoku.Seed.Order.WellFounded
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cutoff scales for finite profile rearrangement

The double-exponential cutoffs and their neighboring-set budgets used in
Latała--van Handel--Youssef 2018, Lemma 3.10. The indexing starts with the
previous cutoff `2` and main cutoff `4`.
-/

noncomputable section
set_option autoImplicit false
namespace NLAlib

/-- Previous cutoff `2^(2^k)` in the profile rearrangement construction.-/
def profilePreviousCutoff (k : ℕ) : ℕ := 2 ^ (2 ^ k)

/-- Main cutoff `2^(2^(k+1))` in the profile rearrangement construction.-/
def profileCutoff (k : ℕ) : ℕ := 2 ^ (2 ^ (k + 1))

/-- Budget for a main cutoff and its neighboring entries.-/
def profileNeighborCutoff (k : ℕ) : ℕ :=
  profileCutoff k + profileCutoff k * profilePreviousCutoff k

/-- Every main cutoff is the square of its previous cutoff.
@isnad1 id=eq.0h1v.s4.e0f0e70b4482 from=translated src=- shape=90d3826a vocab=52b0cb3b
-/
theorem profileCutoff_eq_previous_sq (k : ℕ) :
    profileCutoff k = profilePreviousCutoff k ^ 2 := by
  unfold profileCutoff profilePreviousCutoff
  rw [← pow_mul]
  congr 1

/-- Advancing the previous cutoff gives the current main cutoff.
@isnad1 id=eq.0h1v.s4.112f2d1bbf13 from=translated src=- shape=d1abe3da vocab=1d44d2f5
-/
@[simp] theorem profilePreviousCutoff_succ (k : ℕ) :
    profilePreviousCutoff (k + 1) = profileCutoff k := rfl

/-- Consecutive main cutoffs are related by squaring.
@isnad1 id=eq.0h1v.s5.58a59da375b1 from=translated src=- shape=530baa75 vocab=9c781bc5
-/
@[simp] theorem profileCutoff_succ (k : ℕ) :
    profileCutoff (k + 1) = profileCutoff k ^ 2 := by
  rw [profileCutoff_eq_previous_sq, profilePreviousCutoff_succ]

/-- Previous cutoffs are at least two.
@isnad1 id=le.0h1v.s3.70f30f19ca23 from=translated src=- shape=8a62b088 vocab=bfe9d52e
-/
theorem two_le_profilePreviousCutoff (k : ℕ) : 2 ≤ profilePreviousCutoff k := by
  exact (show 2 ^ 1 ≤ 2 ^ (2 ^ k) from
    Nat.pow_le_pow_right (by decide) (Nat.one_le_pow k 2 (by decide)))

/-- Main cutoffs are at least four.
@isnad1 id=le.0h1v.s3.531f4f360e05 from=translated src=- shape=8a62b088 vocab=0f5e4e4c
-/
theorem four_le_profileCutoff (k : ℕ) : 4 ≤ profileCutoff k := by
  rw [profileCutoff_eq_previous_sq]
  nlinarith [two_le_profilePreviousCutoff k]

/-- The previous cutoff never exceeds the main cutoff.
@isnad1 id=le.0h1v.s3.c8fe6b097a06 from=translated src=- shape=0fc427d2 vocab=19d9a75f
-/
theorem profilePreviousCutoff_le (k : ℕ) : profilePreviousCutoff k ≤ profileCutoff k := by
  rw [profileCutoff_eq_previous_sq]
  nlinarith [two_le_profilePreviousCutoff k]

/-- Previous cutoffs increase monotonically.
@isnad1 id=monotone.0h0v.s2.ff0ef1c061b2 from=translated src=- shape=e3d48bcb vocab=8c44e0cf
-/
theorem monotone_profilePreviousCutoff : Monotone profilePreviousCutoff := by
  intro i j hij
  exact Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) hij)

/-- Main cutoffs increase strictly at every step.
@isnad1 id=strictmo.0h0v.s2.334c9c11411d from=translated src=- shape=e3d48bcb vocab=de90b80c
-/
theorem strictMono_profileCutoff : StrictMono profileCutoff := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [profileCutoff_succ]
  nlinarith [four_le_profileCutoff k]

/-- Main cutoffs increase monotonically.
@isnad1 id=monotone.0h0v.s2.0630bf666451 from=translated src=- shape=e3d48bcb vocab=4e60304e
-/
theorem monotone_profileCutoff : Monotone profileCutoff := strictMono_profileCutoff.monotone

/-- The neighboring-entry budgets increase monotonically.
@isnad1 id=monotone.0h0v.s2.7b50ae10372c from=translated src=- shape=e3d48bcb vocab=d7059463
-/
theorem monotone_profileNeighborCutoff : Monotone profileNeighborCutoff := by
  intro i j hij
  exact Nat.add_le_add (monotone_profileCutoff hij)
    (Nat.mul_le_mul (monotone_profileCutoff hij) (monotone_profilePreviousCutoff hij))

/-- The neighboring-entry budget contains its main cutoff.
@isnad1 id=le.0h1v.s3.1131ff743107 from=translated src=- shape=0fc427d2 vocab=42a02e80
-/
theorem profileCutoff_le_neighborCutoff (k : ℕ) :
    profileCutoff k ≤ profileNeighborCutoff k := Nat.le_add_right _ _

/-- Exact adjacent-block budget: the neighboring set and the next previous
cutoff fit inside the next main cutoff.
@isnad1 id=le.0h1v.s5.590ebd3cdf99 from=translated src=- shape=e1edd771 vocab=9a9725be
-/
theorem profileNeighborCutoff_add_previous_succ_le (k : ℕ) :
    profileNeighborCutoff k + profilePreviousCutoff (k + 1) ≤ profileCutoff (k + 1) := by
  have hbase : profilePreviousCutoff k + 2 ≤ profileCutoff k := by
    rw [profileCutoff_eq_previous_sq]
    nlinarith [two_le_profilePreviousCutoff k]
  have hmul := Nat.mul_le_mul_left (profileCutoff k) hbase
  rw [profilePreviousCutoff_succ, profileCutoff_succ, profileNeighborCutoff]
  nlinarith

/-- Each neighboring-entry budget lies strictly below the next main cutoff.
@isnad1 id=lt.0h1v.s4.310031f55579 from=translated src=- shape=04942a0e vocab=e60516ed
-/
theorem profileNeighborCutoff_lt_cutoff_succ (k : ℕ) :
    profileNeighborCutoff k < profileCutoff (k + 1) := by
  have h := profileNeighborCutoff_add_previous_succ_le k
  have hp := two_le_profilePreviousCutoff (k + 1)
  omega

/-- Main cutoffs dominate their index, so every finite dimension is eventually
covered without an extra growth hypothesis.
@isnad1 id=le.0h1v.s3.098616323b0c from=translated src=- shape=e63234f4 vocab=0f5e4e4c
-/
theorem le_profileCutoff (k : ℕ) : k ≤ profileCutoff k := strictMono_profileCutoff.le_apply

/-- Every finite natural budget lies below some main cutoff.
@isnad1 id=ex.0h1v.s3.af1b34b0862a from=translated src=- shape=0b95ec6c vocab=0f5e4e4c
-/
theorem exists_le_profileCutoff (b : ℕ) : ∃ k, b ≤ profileCutoff k := ⟨b, le_profileCutoff b⟩

/-- Exact natural logarithm of a main cutoff, viewed as a real number.
@isnad1 id=eq.0h1v.s5.404bed83aa31 from=translated src=- shape=6d901a47 vocab=54c8fad0
-/
theorem log_profileCutoff (k : ℕ) :
    Real.log (profileCutoff k : ℝ) = (2 : ℝ) ^ (k + 1) * Real.log 2 := by
  simp [profileCutoff, Real.log_pow]

/-- Previous cutoffs have strictly positive real square roots.
@isnad1 id=lt.0h1v.s4.74afb4196389 from=translated src=- shape=5157d5e1 vocab=f19bfa8a
-/
theorem sqrt_profilePreviousCutoff_pos (k : ℕ) :
    0 < Real.sqrt (profilePreviousCutoff k : ℝ) := by
  apply Real.sqrt_pos.2
  exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (two_le_profilePreviousCutoff k)

/-- The inverse square root of a previous cutoff is strictly positive.
@isnad1 id=lt.0h1v.s4.c75ad2187564 from=translated src=- shape=3b024469 vocab=9563e196
-/
theorem inv_sqrt_profilePreviousCutoff_pos (k : ℕ) :
    0 < (Real.sqrt (profilePreviousCutoff k : ℝ))⁻¹ :=
  inv_pos.mpr (sqrt_profilePreviousCutoff_pos k)

/-- The real square root of a main cutoff is exactly its previous cutoff.
@isnad1 id=eq.0h1v.s3.ab9250cb80ef from=translated src=- shape=df0095c1 vocab=9aa344ae
-/
theorem sqrt_profileCutoff_eq_previous (k : ℕ) :
    Real.sqrt (profileCutoff k : ℝ) = (profilePreviousCutoff k : ℝ) := by
  rw [profileCutoff_eq_previous_sq, Nat.cast_pow, Real.sqrt_sq (by positivity)]

end NLAlib
