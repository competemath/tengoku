/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

module

public import Tengoku.Seed.Computability.Partrec
public import Tengoku.Seed.Computability.PartrecCode
public import Tengoku.Seed.Data.List.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vendored from AlexeyMilovanov/kolmogorov-complexity-lean

Pinned revision `005ac4c81eefe09642ef561057199d489cd79485` (Apache-2.0).
Adapted only for Lean 4.32 `module` / `public import` visibility; mathematical
content is upstream's. Atlas-facing names live in `AISafetyAtlas.Logic`.
-/

/-!
# Binary Encoding of Natural Numbers

This module provides the foundational mapping between natural numbers
and bit strings (`List Bool`). It proves that the standard `Nat.bits`
representation is injective and defines its left inverse (`decodeBits`).
It also establishes the computability of these transformations and
bounds on the length of the binary representation.
-/

namespace Kolmogorov

/-! ### Decoding and Injectivity -/

/-- Decoder from a list of bits (little-endian) back to a natural number.-/
@[expose]
public def decodeBits : List Bool → ℕ
  | [] => 0
  | false :: bs => 2 * decodeBits bs
  | true :: bs => 2 * decodeBits bs + 1

/-- Proving that `decodeBits` is a left inverse to `Nat.bits`.-/
@[simp]
public theorem decodeBits_natBits (n : ℕ) : decodeBits (Nat.bits n) = n := by
  induction n using Nat.binaryRec
  case zero =>
    simp [decodeBits]
  case bit b n' ih =>
    by_cases h_zero : n' = 0
    · subst h_zero
      cases b
      · simp [decodeBits, Nat.bit, Nat.bits]
      · have h_app : Nat.bits (Nat.bit true 0) = true :: Nat.bits 0 := by
          apply Nat.bits_append_bit
          intro _; rfl
        rw [h_app]
        simp [decodeBits, Nat.bit]
    · have h_app : Nat.bits (Nat.bit b n') = b :: Nat.bits n' := by
        apply Nat.bits_append_bit
        intro h; contradiction
      rw [h_app]
      cases b <;> simp [decodeBits, ih, Nat.bit]

/-! ### Length Bounds -/

/-! ### Computability -/

/-- A single step of decoding a bit, multiplying the accumulator and adding the bit.-/
@[expose]
public def decodeStep (b : Bool) (n : ℕ) : ℕ :=
  Nat.bit b n

/-! ### Nat.bits Computability -/

/-- Helper function for the strong recursion of `Nat.bits`.-/
@[expose]
public def bitsG (_ : Unit) (l : List (List Bool)) : Option (List Bool) :=
  let n := l.length
  bif n == 0 then some []
  else some ((n % 2 == 1) :: l.getD (n / 2) [])

end Kolmogorov
