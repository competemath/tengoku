/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Encoding.BitPolynomial.Transpose.Defs
public import Tengoku

/-!
# Index arithmetic for binary matrix transposition

The transposed source index stays inside the requested rectangle, and
swapping dimensions reverses the index map. Consequently two transposes
retain precisely the rectangle, adding false entries when the input is short.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

private theorem transpose_index_lt (rows cols k : Nat) (bound : k < rows * cols) :
    (k % rows) * cols + k / rows < rows * cols := by
  have positive : 0 < rows := by
    by_contra! h
    simp only [Nat.le_zero.mp h, Nat.zero_mul, Nat.not_lt_zero] at bound
  have quotient : k / rows < cols :=
    (Nat.div_lt_iff_lt_mul positive).mpr (by simpa only [Nat.mul_comm] using bound)
  have product : (k % rows) * cols + cols ≤ rows * cols := by
    simpa only [Nat.succ_mul] using
      Nat.mul_le_mul_right cols (Nat.succ_le_of_lt (Nat.mod_lt k positive))
  exact (Nat.add_lt_add_left quotient _).trans_le product

private theorem transpose_index_inverse (rows cols k : Nat) (bound : k < rows * cols) :
    (((k % rows) * cols + k / rows) % cols) * rows +
      ((k % rows) * cols + k / rows) / cols = k := by
  have rowsPositive : 0 < rows := by
    by_contra! h
    simp only [Nat.le_zero.mp h, Nat.zero_mul, Nat.not_lt_zero] at bound
  have colsPositive : 0 < cols := by
    by_contra! h
    simp only [Nat.le_zero.mp h, Nat.mul_zero, Nat.not_lt_zero] at bound
  have quotient : k / rows < cols :=
    (Nat.div_lt_iff_lt_mul rowsPositive).mpr
      (by simpa only [Nat.mul_comm] using bound)
  rw [Nat.mul_comm (k % rows) cols, Nat.mul_add_mod, Nat.mod_eq_of_lt quotient,
    Nat.mul_add_div colsPositive, Nat.div_eq_of_lt quotient, Nat.add_zero,
    Nat.mul_comm (k / rows) rows, Nat.div_add_mod]

/--
@isnad1 id=eq.0h3v.s4.b218eb8284a4 from=translated src=- shape=97629784 vocab=144e1258
-/
theorem transposeBits_length (rows cols : Nat) (bits : List Bool) :
    (transposeBits rows cols bits).length = rows * cols := by
  simp only [transposeBits, List.length_map, List.length_range]

/--
@isnad1 id=eq.0h2v.s4.084a0ba1107e from=translated src=- shape=67cea8c4 vocab=10fae0b3
-/
theorem transposeBits_zero_rows (cols : Nat) (bits : List Bool) :
    transposeBits 0 cols bits = [] := by
  simp only [transposeBits, Nat.zero_mul, List.range_zero, List.map_nil]

/--
@isnad1 id=eq.0h2v.s4.5f7bc4a33a79 from=translated src=- shape=b92d2682 vocab=10fae0b3
-/
theorem transposeBits_zero_cols (rows : Nat) (bits : List Bool) :
    transposeBits rows 0 bits = [] := by
  simp only [transposeBits, Nat.mul_zero, List.range_zero, List.map_nil]

/--
@isnad1 id=eq.1h4v.s6.367482f0ca50 from=translated src=- shape=d49be13e vocab=815530fe
-/
theorem transposeBits_getD (rows cols : Nat) (bits : List Bool) (k : Nat)
    (bound : k < rows * cols) :
    (transposeBits rows cols bits)[k]?.getD false =
      bits[(k % rows) * cols + k / rows]?.getD false := by
  simp only [transposeBits, List.getElem?_map, List.getElem?_range bound,
    Option.map_some, Option.getD_some]

/--
@isnad1 id=eq.2h5v.s6.59c2c78ba26f from=translated src=- shape=8bddb582 vocab=e31b33b9
-/
theorem transposeBits_getD_coord (rows cols : Nat) (bits : List Bool)
    (row col : Nat) (rowBound : row < rows) (colBound : col < cols) :
    (transposeBits rows cols bits)[col * rows + row]?.getD false =
      bits[row * cols + col]?.getD false := by
  have positive : 0 < rows := by lia
  have product : col * rows + rows ≤ cols * rows := by
    simpa only [Nat.succ_mul] using
      Nat.mul_le_mul_right rows (Nat.succ_le_of_lt colBound)
  have bound : col * rows + row < rows * cols := by
    rw [Nat.mul_comm rows cols]
    exact (Nat.add_lt_add_left rowBound _).trans_le product
  rw [transposeBits_getD _ _ _ _ bound, Nat.mul_comm col rows, Nat.mul_add_mod,
    Nat.mod_eq_of_lt rowBound, Nat.mul_add_div positive, Nat.div_eq_of_lt rowBound,
    Nat.add_zero]

/--
@isnad1 id=eq.0h3v.s5.00dc8f309509 from=translated src=- shape=b9e3f378 vocab=3a112b25
-/
theorem transposeBits_transposeBits (rows cols : Nat) (bits : List Bool) :
    transposeBits cols rows (transposeBits rows cols bits) =
      (List.range (rows * cols)).map (fun k => bits[k]?.getD false) := by
  apply List.ext_getElem?
  intro k
  by_cases bound : k < rows * cols
  · have swapped : k < cols * rows := by simpa only [Nat.mul_comm] using bound
    have sourceBound : (k % cols) * rows + k / cols < rows * cols := by
      simpa only [Nat.mul_comm] using transpose_index_lt cols rows k swapped
    simp only [transposeBits, List.getElem?_map, List.getElem?_range swapped,
      List.getElem?_range bound, Option.map_some]
    congr 1
    rw [List.getElem?_range sourceBound, Option.map_some, Option.getD_some,
      transpose_index_inverse cols rows k swapped]
  · have leftBound : (transposeBits cols rows (transposeBits rows cols bits)).length ≤ k := by
      rw [transposeBits_length, Nat.mul_comm]
      lia
    have rightBound : ((List.range (rows * cols)).map (fun i => bits[i]?.getD false)).length
        ≤ k := by
      simp only [List.length_map, List.length_range]
      lia
    rw [List.getElem?_eq_none leftBound, List.getElem?_eq_none rightBound]

/--
@isnad1 id=eq.1h3v.s5.750b21647f47 from=translated src=- shape=492cc5c6 vocab=144e1258
-/
theorem transposeBits_transposeBits_of_length (rows cols : Nat) (bits : List Bool)
    (size : bits.length = rows * cols) :
    transposeBits cols rows (transposeBits rows cols bits) = bits := by
  rw [transposeBits_transposeBits]
  apply List.ext_getElem?
  intro k
  by_cases bound : k < rows * cols
  · have inputBound : k < bits.length := by lia
    simp only [List.getElem?_map, List.getElem?_range bound, Option.map_some,
      List.getElem?_eq_getElem inputBound, Option.getD_some]
  · have inputBound : bits.length ≤ k := by lia
    have outputBound : ((List.range (rows * cols)).map (fun i => bits[i]?.getD false)).length
        ≤ k := by
      simp only [List.length_map, List.length_range]
      lia
    rw [List.getElem?_eq_none outputBound, List.getElem?_eq_none inputBound]

/--
@isnad1 id=eq.0h3v.s4.050f06d86bee from=translated src=- shape=741d1b58 vocab=e5828835
-/
theorem transposeEval_pair (bits rowsWord colsWord : List Bool) :
    transposeEval (pair (pair bits rowsWord) colsWord) =
      transposeBits rowsWord.length colsWord.length bits := by
  simp only [transposeEval, pairFst_pair, pairSnd_pair]

/--
@isnad1 id=le.0h1v.s4.30ff7db060a0 from=translated src=- shape=24bbb351 vocab=934b2956
-/
theorem transposeEval_length_le (z : List Bool) :
    (transposeEval z).length ≤ z.length * z.length := by
  rw [transposeEval, transposeBits_length]
  exact Nat.mul_le_mul
    ((pairSnd_length_le (pairFst z)).trans (pairFst_length_le z)) (pairSnd_length_le z)

end BitPolynomial.Internal
end Complexity
