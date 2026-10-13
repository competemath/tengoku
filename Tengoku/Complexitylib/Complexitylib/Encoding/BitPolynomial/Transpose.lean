/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Encoding.BitPolynomial.Transpose.Defs
import Tengoku.Complexitylib.Complexitylib.Encoding.BitPolynomial.Transpose.Internal

/-!
# Correct transposition of binary coefficient matrices

The output has the exact rectangular width. Position `col*rows+row` reads
input position `row*cols+col`, with false for missing entries. Two transposes
recover the requested rectangle, truncating excess bits and adding high
false padding if needed. Exact-sized inputs therefore roundtrip unchanged.

All statements include zero dimensions and arbitrary input padding. The
uniform machine certificate is in `Complexitylib.Classes.P.BitPolynomial.Transpose`.
-/

public section

namespace Complexity
namespace BitPolynomial

/-- Transposition always writes the exact requested rectangular width.
@isnad1 id=eq.0h3v.s4.b218eb8284a4 from=translated src=- shape=97629784 vocab=144e1258
-/
theorem transposeBits_length (rows cols : Nat) (bits : List Bool) :
    (transposeBits rows cols bits).length = rows * cols :=
  Internal.transposeBits_length rows cols bits

/-- A matrix with no rows has empty output.
@isnad1 id=eq.0h2v.s4.084a0ba1107e from=translated src=- shape=67cea8c4 vocab=10fae0b3
-/
theorem transposeBits_zero_rows (cols : Nat) (bits : List Bool) :
    transposeBits 0 cols bits = [] :=
  Internal.transposeBits_zero_rows cols bits

/-- A matrix with no columns has empty output.
@isnad1 id=eq.0h2v.s4.5f7bc4a33a79 from=translated src=- shape=b92d2682 vocab=10fae0b3
-/
theorem transposeBits_zero_cols (rows : Nat) (bits : List Bool) :
    transposeBits rows 0 bits = [] :=
  Internal.transposeBits_zero_cols rows bits

/-- Each in-range output bit reads its transposed source index.
@isnad1 id=eq.1h4v.s6.367482f0ca50 from=translated src=- shape=d49be13e vocab=815530fe
-/
theorem transposeBits_getD (rows cols : Nat) (bits : List Bool) (k : Nat)
    (bound : k < rows * cols) :
    (transposeBits rows cols bits)[k]?.getD false =
      bits[(k % rows) * cols + k / rows]?.getD false :=
  Internal.transposeBits_getD rows cols bits k bound

/-- Matrix coordinates transpose directly, including missing input entries.
@isnad1 id=eq.2h5v.s6.59c2c78ba26f from=translated src=- shape=8bddb582 vocab=e31b33b9
-/
theorem transposeBits_getD_coord (rows cols : Nat) (bits : List Bool)
    (row col : Nat) (rowBound : row < rows) (colBound : col < cols) :
    (transposeBits rows cols bits)[col * rows + row]?.getD false =
      bits[row * cols + col]?.getD false :=
  Internal.transposeBits_getD_coord rows cols bits row col rowBound colBound

/-- Two transposes recover the requested rectangle with truncation and false padding.
@isnad1 id=eq.0h3v.s5.00dc8f309509 from=translated src=- shape=b9e3f378 vocab=3a112b25
-/
theorem transposeBits_transposeBits (rows cols : Nat) (bits : List Bool) :
    transposeBits cols rows (transposeBits rows cols bits) =
      (List.range (rows * cols)).map (fun k => bits[k]?.getD false) :=
  Internal.transposeBits_transposeBits rows cols bits

/-- Transposition is inverted by swapping dimensions when the input has exact width.
@isnad1 id=eq.1h3v.s5.750b21647f47 from=translated src=- shape=492cc5c6 vocab=144e1258
-/
theorem transposeBits_transposeBits_of_length (rows cols : Nat) (bits : List Bool)
    (size : bits.length = rows * cols) :
    transposeBits cols rows (transposeBits rows cols bits) = bits :=
  Internal.transposeBits_transposeBits_of_length rows cols bits size

/-- The paired evaluator reads its matrix and both runtime unary dimensions.
@isnad1 id=eq.0h3v.s4.050f06d86bee from=translated src=- shape=741d1b58 vocab=e5828835
-/
theorem transposeEval_pair (bits rowsWord colsWord : List Bool) :
    transposeEval (pair (pair bits rowsWord) colsWord) =
      transposeBits rowsWord.length colsWord.length bits :=
  Internal.transposeEval_pair bits rowsWord colsWord

/-- The output width is bounded by the square of the encoded input length.
@isnad1 id=le.0h1v.s4.30ff7db060a0 from=translated src=- shape=24bbb351 vocab=934b2956
-/
theorem transposeEval_length_le (z : List Bool) :
    (transposeEval z).length ≤ z.length * z.length :=
  Internal.transposeEval_length_le z

end BitPolynomial
end Complexity
