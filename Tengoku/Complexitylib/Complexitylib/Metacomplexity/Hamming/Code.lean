/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Hamming.Code.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Hamming.Code.Internal
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Hamming.Code.Repetition

/-!
# Finite Boolean codes

This module turns the finite Hamming geometry into an abstract coding layer.
An injective code has exactly `2^messageLength` codewords, minimum distance
implies the exact sphere-packing bound, and exhaustive decoding is uniquely
correct below half that distance. No runtime claim is bundled into these
semantic results. The repetition submodule supplies the first concrete linear
code with exact distance amplification.
-/

public section

namespace Complexity

namespace BooleanCode

/-- Codewords are exactly encoded messages.
@isnad1 id=iff.0h4v.s5.923c0ad250cc from=translated src=- shape=2c07b237 vocab=cf9b4a29
-/
theorem mem_codewords_iff {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (word : BooleanHamming.Word blockLength) :
    word ∈ code.codewords ↔ ∃ message, code.encode message = word :=
  mem_codewords_iff_internal code word

/-- An injective Boolean code has exactly `2^messageLength` codewords.
@isnad1 id=eq.0h3v.s5.29318486539d from=translated src=- shape=eb4de368 vocab=07c34245
-/
@[simp] theorem card_codewords {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength) :
    code.codewords.card = 2 ^ messageLength :=
  card_codewords_internal code

/-- A message-level minimum-distance contract separates the finite codeword
set by the same amount.
@isnad1 id=issepara.1h4v.s4.4da3b4b789cd from=translated src=- shape=d7e5d263 vocab=9e688a0f
-/
theorem isSeparated_codewords {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength} {minimumDistance : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance) :
    BooleanHamming.IsSeparated code.codewords minimumDistance :=
  isSeparated_codewords_internal hdistance

/-- Coding-theoretic Hamming packing bound with exact finite parameters.
@isnad1 id=le.2h5v.s6.12536e1dccf4 from=translated src=- shape=5cd4ed3a vocab=8744729a
-/
theorem packing_bound {messageLength blockLength minimumDistance radius : ℕ}
    {code : BooleanCode messageLength blockLength}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance) :
    2 ^ messageLength * BooleanHamming.volume blockLength radius ≤
      2 ^ blockLength :=
  packing_bound_internal hdistance hradius

/-- Candidate-list membership is exactly proximity of the encoded message.
@isnad1 id=iff.0h6v.s5.08795486d879 from=translated src=- shape=4fb8a0e8 vocab=6df0f031
-/
@[simp] theorem mem_decodeCandidates_iff {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (received : BooleanHamming.Word blockLength) (radius : ℕ)
    (message : BooleanHamming.Word messageLength) :
    message ∈ code.decodeCandidates received radius ↔
      BooleanHamming.distance (code.encode message) received ≤ radius :=
  mem_decodeCandidates_iff_internal code received radius message

/-- Every sufficiently close message occurs in exhaustive decoding.
@isnad1 id=mem.1h6v.s5.b7c280b865e5 from=translated src=- shape=2a529010 vocab=6df0f031
-/
theorem mem_decodeCandidates_of_close {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (received : BooleanHamming.Word blockLength) (radius : ℕ)
    (message : BooleanHamming.Word messageLength)
    (hclose : BooleanHamming.distance (code.encode message) received ≤ radius) :
    message ∈ code.decodeCandidates received radius :=
  mem_decodeCandidates_of_close_internal code received radius message hclose

/-- Below half the minimum distance, any two decoding candidates coincide. -/
theorem eq_of_mem_decodeCandidates {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength)
    {left right : BooleanHamming.Word messageLength}
    (hleft : left ∈ code.decodeCandidates received radius)
    (hright : right ∈ code.decodeCandidates received radius) :
    left = right :=
  eq_of_mem_decodeCandidates_internal
    hdistance hradius received hleft hright

/-- Exhaustive decoding contains at most one message below half the minimum
distance.
@isnad1 id=le.2h6v.s5.20a2fad0701b from=translated src=- shape=f94a6900 vocab=d44fc7b7
-/
theorem card_decodeCandidates_le_one {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength) :
    (code.decodeCandidates received radius).card ≤ 1 :=
  card_decodeCandidates_le_one_internal hdistance hradius received

/-- A nearby message is the entire exhaustive candidate set below half the
minimum distance.
@isnad1 id=eq.3h7v.s6.903c8ab1fb11 from=translated src=- shape=e60b2896 vocab=620c73b3
-/
theorem decodeCandidates_eq_singleton_of_close
    {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength)
    (message : BooleanHamming.Word messageLength)
    (hclose : BooleanHamming.distance (code.encode message) received ≤ radius) :
    code.decodeCandidates received radius = {message} :=
  decodeCandidates_eq_singleton_of_close_internal
    hdistance hradius received message hclose

/-- The exhaustive decoder recovers every message from fewer than half the
minimum-distance errors.
@isnad1 id=eq.3h7v.s6.af9c0dd2e544 from=translated src=- shape=278fec9d vocab=1fab3dbb
-/
theorem decodeUnique?_eq_some_of_close
    {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength)
    (message : BooleanHamming.Word messageLength)
    (hclose : BooleanHamming.distance (code.encode message) received ≤ radius) :
    code.decodeUnique? received radius = some message :=
  decodeUnique?_eq_some_of_close_internal
    hdistance hradius received message hclose

end BooleanCode

end Complexity
