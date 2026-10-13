/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul.Defs
public import Tengoku

/-!
# Width-driven binary shift-and-add multiplication -- pure proofs

This file proves the generalized arithmetic invariant of the little-endian
shift-and-add fold, its multiplication specialization, and width bounds for
every partial accumulator and shifted multiplicand.
-/

public section

namespace Complexity

namespace BinaryShiftMul

/-- The generalized shift-and-add fold accumulates `shift` times the decoded
bit string and doubles `shift` once per consumed bit.
@isnad1 id=eq.0h3v.s6.7c7a0811be86 from=translated src=- shape=35ee16ab vocab=4bea034e
-/
theorem fold_eq_internal (bits : List Bool) (acc shift : ℕ) :
    fold bits acc shift =
      (acc + shift * Nat.fromBitsLE bits, shift * 2 ^ bits.length) := by
  induction bits generalizing acc shift with
  | nil => simp [fold, Nat.fromBitsLE, Nat.fromBits]
  | cons bit bits ih =>
      cases bit <;>
        simp [fold, step, ih, Nat.fromBitsLE_cons, pow_succ,
          Prod.ext_iff] <;>
        constructor <;> ring

/-- Taking a low-order prefix cannot increase its little-endian decoded
value.
@isnad1 id=le.0h2v.s3.a8a234941518 from=translated src=- shape=33043f13 vocab=aba4a886
-/
theorem fromBitsLE_take_le_internal (bits : List Bool) (i : ℕ) :
    Nat.fromBitsLE (bits.take i) ≤ Nat.fromBitsLE bits := by
  induction bits generalizing i with
  | nil => simp [Nat.fromBitsLE]
  | cons bit bits ih =>
      cases i with
      | zero =>
          simp only [List.take_zero]
          exact Nat.zero_le _
      | succ i =>
          rw [List.take_succ_cons, Nat.fromBitsLE_cons,
            Nat.fromBitsLE_cons]
          exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 (ih i)) _

/-- If the iteration index is within the canonical multiplier width, folding
its prefix produces the advertised partial accumulator and shift.
@isnad1 id=eq.1h3v.s5.f2cd06f2ef60 from=translated src=- shape=e8f2a3f8 vocab=322d6dab
-/
theorem fold_take_eq_internal (lhs rhs i : ℕ) (hi : i ≤ rhs.size) :
    fold (rhs.bits.take i) 0 lhs =
      (partialAcc lhs rhs i, partialShift lhs i) := by
  rw [fold_eq_internal]
  simp [partialAcc, partialShift, List.length_take, Nat.size_eq_bits_len,
    min_eq_left hi]

private theorem fold_append (xs ys : List Bool) (acc shift : ℕ) :
    fold (xs ++ ys) acc shift =
      let middle := fold xs acc shift
      fold ys middle.1 middle.2 := by
  induction xs generalizing acc shift with
  | nil => rfl
  | cons bit xs ih =>
      simp only [List.cons_append, fold]
      rw [ih]

/-- One live multiplier bit advances the partial arithmetic invariant by one
iteration.
@isnad1 id=eq.1h3v.s6.ced3427bd4ca from=translated src=- shape=f8351cc5 vocab=08f2fa67
-/
theorem step_partial_internal (lhs rhs i : ℕ) (hi : i < rhs.size) :
    step (rhs.bits.get ⟨i, by simpa [Nat.size_eq_bits_len] using hi⟩)
        (partialAcc lhs rhs i) (partialShift lhs i) =
      (partialAcc lhs rhs (i + 1), partialShift lhs (i + 1)) := by
  have hcurrent := fold_take_eq_internal lhs rhs i (Nat.le_of_lt hi)
  have hnext := fold_take_eq_internal lhs rhs (i + 1) (by omega)
  rw [List.take_succ_eq_append_getElem (by
    simpa [Nat.size_eq_bits_len] using hi), fold_append, hcurrent] at hnext
  simpa [fold] using hnext

/-- Folding all canonical multiplier bits computes multiplication and leaves
the shift advanced by the multiplier width.
@isnad1 id=eq.0h2v.s5.1a62d17ac36f from=translated src=- shape=762b4620 vocab=586e6bb0
-/
theorem fold_natBits_internal (lhs rhs : ℕ) :
    fold rhs.bits 0 lhs = (lhs * rhs, lhs * 2 ^ rhs.size) := by
  rw [fold_eq_internal, Nat.fromBitsLE_bits, Nat.size_eq_bits_len]
  simp

/-- The complete partial accumulator is the product.
@isnad1 id=eq.0h2v.s4.3da6c61d2a65 from=translated src=- shape=3f8c58da vocab=d6aca8b2
-/
theorem partialAcc_full_internal (lhs rhs : ℕ) :
    partialAcc lhs rhs rhs.size = lhs * rhs := by
  unfold partialAcc
  rw [← Nat.size_eq_bits_len, List.take_length, Nat.fromBitsLE_bits]

/-- The complete partial shift has advanced by the multiplier width.
@isnad1 id=eq.0h2v.s5.d643f86a7cec from=translated src=- shape=fa72c243 vocab=5e434540
-/
theorem partialShift_full_internal (lhs rhs : ℕ) :
    partialShift lhs rhs.size = lhs * 2 ^ rhs.size := by
  rfl

/-- The accumulator component of the complete pure fold is the product.
@isnad1 id=eq.0h2v.s4.252f22376bbc from=translated src=- shape=b1ef1adc vocab=fa8e032e
-/
theorem fold_natBits_fst_internal (lhs rhs : ℕ) :
    (fold rhs.bits 0 lhs).1 = lhs * rhs := by
  rw [fold_natBits_internal]

/-- Every partial accumulator is bounded by the complete product.
@isnad1 id=le.0h3v.s4.1f73a14c87b5 from=translated src=- shape=d9737506 vocab=e01122e2
-/
theorem partialAcc_le_mul_internal (lhs rhs i : ℕ) :
    partialAcc lhs rhs i ≤ lhs * rhs := by
  unfold partialAcc
  simpa only [Nat.fromBitsLE_bits] using
    Nat.mul_le_mul_left lhs (fromBitsLE_take_le_internal rhs.bits i)

/-- Binary width is subadditive under multiplication.
@isnad1 id=le.0h2v.s4.370d17ee82fd from=translated src=- shape=a13ca989 vocab=9227dc1d
-/
theorem size_mul_le_add_internal (lhs rhs : ℕ) :
    (lhs * rhs).size ≤ lhs.size + rhs.size := by
  by_cases hrhs : rhs = 0
  · simp [hrhs]
  rw [Nat.size_le]
  calc
    lhs * rhs < 2 ^ lhs.size * rhs :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self lhs) (Nat.pos_of_ne_zero hrhs)
    _ < 2 ^ lhs.size * 2 ^ rhs.size :=
      Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self rhs) (Nat.two_pow_pos _)
    _ = 2 ^ (lhs.size + rhs.size) := by rw [pow_add]

/-- Every partial accumulator fits in the combined input width.
@isnad1 id=le.0h3v.s4.bc99e7d91ceb from=translated src=- shape=052db9f3 vocab=0e7a6a97
-/
theorem partialAcc_size_le_width_internal (lhs rhs i : ℕ) :
    (partialAcc lhs rhs i).size ≤ lhs.size + rhs.size := by
  exact le_trans (Nat.size_le_size (partialAcc_le_mul_internal lhs rhs i))
    (size_mul_le_add_internal lhs rhs)

/-- Shifting left by `i` grows binary width by at most `i`.
@isnad1 id=le.0h2v.s4.4c0aae1103f0 from=translated src=- shape=554866a9 vocab=59237ef2
-/
theorem partialShift_size_le_internal (lhs i : ℕ) :
    (partialShift lhs i).size ≤ lhs.size + i := by
  by_cases hlhs : lhs = 0
  · simp [partialShift, hlhs]
  rw [partialShift, ← Nat.shiftLeft_eq_mul_pow, Nat.size_shiftLeft hlhs]

/-- At any live multiplier iteration, both arithmetic values fit in the
combined input width.
@isnad1 id=and.1h3v.s5.14aa00014b60 from=translated src=- shape=14153c64 vocab=93b1fa81
-/
theorem partial_widths_le_internal (lhs rhs i : ℕ) (hi : i ≤ rhs.size) :
    (partialAcc lhs rhs i).size ≤ lhs.size + rhs.size ∧
      (partialShift lhs i).size ≤ lhs.size + rhs.size := by
  exact ⟨partialAcc_size_le_width_internal lhs rhs i,
    le_trans (partialShift_size_le_internal lhs i)
      (Nat.add_le_add_left hi lhs.size)⟩

end BinaryShiftMul

end Complexity
