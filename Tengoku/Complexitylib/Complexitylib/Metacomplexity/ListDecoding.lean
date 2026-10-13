/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.ListDecoding.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.ListDecoding.Internal
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.ListDecoding.Family

/-!
# Finite Boolean list decoding

Exact truth-table agreement above `1/2 + ε` places the original message in
the candidate set of any code list-decodable up to radius `1/2 - ε`. The
candidate set contains at most the advertised indexed list size. A canonical
fixed-width codec stores the selecting index in exactly `clog₂(listSize)` bits
and turns the existential decoder occurrence into an actual bit string. The
family layer separates semantic inverse-accuracy decoding, concrete polynomial
parameter bounds, and single-machine encoder/full-decoder uniformity.
-/

public section

universe u

namespace Complexity

namespace BooleanListCode

/-- Encoding a decoder index uses exactly the ceiling-logarithmic number of
bits needed for the advertised list size.
@isnad1 id=eq.0h2v.s3.fb622da58dec from=translated src=- shape=97f23171 vocab=1d63b9f9
-/
@[simp] theorem length_encodeDecoderIndex
    {listSize : ℕ} (index : Fin listSize) :
    (encodeDecoderIndex index).length = decoderIndexBitWidth listSize :=
  length_encodeDecoderIndex_internal index

/-- Fixed-width decoder-index encoding round-trips exactly.
@isnad1 id=eq.0h2v.s4.f1d35f43c714 from=translated src=- shape=e515e695 vocab=e2817dab
-/
theorem decodeDecoderIndex?_encodeDecoderIndex
    {listSize : ℕ} (index : Fin listSize) :
    decodeDecoderIndex? listSize (encodeDecoderIndex index) = some index :=
  decodeDecoderIndex?_encodeDecoderIndex_internal index

/-- Selecting a list decoder output through its encoded index agrees with
selecting it directly.
@isnad1 id=eq.0h6v.s5.c86235c5220e from=translated src=- shape=f5950c9a vocab=85293def
-/
theorem decodeAtIndexBits?_encodeDecoderIndex
    {messageLength listSize : ℕ} {coordinate : Type u}
    (code : BooleanListCode messageLength listSize coordinate)
    (received : coordinate → Bool) (index : Fin listSize) :
    code.decodeAtIndexBits? received (encodeDecoderIndex index) =
      some (code.decode received index) :=
  decodeAtIndexBits?_encodeDecoderIndex_internal code received index

/-- Relative Boolean Hamming distance is one minus exact agreement
probability.
@isnad1 id=eq.0h3v.s5.fa6e2c2731b8 from=translated src=- shape=e1412eb0 vocab=890c7541
-/
theorem relativeDistance_eq_one_sub_agreementProbability
    {coordinate : Type u} [Fintype coordinate] [DecidableEq coordinate]
    [Nonempty coordinate] (left right : coordinate → Bool) :
    relativeDistance left right = 1 - agreementProbability left right :=
  relativeDistance_eq_one_sub_agreementProbability_internal left right

/-- Exact agreement and relative Hamming distance partition the coordinate
space.
@isnad1 id=eq.0h3v.s5.c0e1f0889ea3 from=translated src=- shape=1f967c7d vocab=157582dd
-/
theorem agreementProbability_add_relativeDistance
    {coordinate : Type u} [Fintype coordinate] [DecidableEq coordinate]
    [Nonempty coordinate] (left right : coordinate → Bool) :
    agreementProbability left right + relativeDistance left right = 1 :=
  agreementProbability_add_relativeDistance_internal left right

/-- Agreement at least `1 - radius` implies relative distance at most
`radius`.
@isnad1 id=le.1h4v.s5.f2a32a633464 from=translated src=- shape=cf743c47 vocab=fb056d84
-/
theorem relativeDistance_le_of_agreementProbability_ge
    {coordinate : Type u} [Fintype coordinate] [DecidableEq coordinate]
    [Nonempty coordinate] {left right : coordinate → Bool} {radius : ℚ}
    (hagreement : 1 - radius ≤ agreementProbability left right) :
    relativeDistance left right ≤ radius :=
  relativeDistance_le_of_agreementProbability_ge_internal hagreement

/-- A list-decoding guarantee and sufficient agreement produce an indexed
decoder occurrence of the original message.
@isnad1 id=ex.2h7v.s6.76e43b898611 from=translated src=- shape=b78d4f78 vocab=2dca3422
-/
theorem exists_decoder_index_of_agreementProbability_ge
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {radius : ℚ}
    (hcode : code.IsListDecodableAt radius)
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 - radius ≤
      agreementProbability (code.encode message) received) :
    ∃ index, code.decode received index = message :=
  exists_decoder_index_of_agreementProbability_ge_internal
    hcode message received hagreement

/-- A list-decoding guarantee and sufficient agreement produce an actual
fixed-width bit string selecting the original message.
@isnad1 id=ex.2h7v.s6.f138a164d1a1 from=translated src=- shape=4049eaf1 vocab=5e740219
-/
theorem exists_indexBits_of_agreementProbability_ge
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {radius : ℚ}
    (hcode : code.IsListDecodableAt radius)
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 - radius ≤
      agreementProbability (code.encode message) received) :
    ∃ bits : List Bool,
      bits.length = decoderIndexBitWidth listSize ∧
        code.decodeAtIndexBits? received bits = some message :=
  exists_indexBits_of_agreementProbability_ge_internal
    hcode message received hagreement

/-- Sufficient agreement places the original message in the decoder candidate
set.
@isnad1 id=mem.2h7v.s6.5ec2b2a72e11 from=translated src=- shape=58ccbfbc vocab=05c5e177
-/
theorem mem_candidates_of_agreementProbability_ge
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {radius : ℚ}
    (hcode : code.IsListDecodableAt radius)
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 - radius ≤
      agreementProbability (code.encode message) received) :
    message ∈ code.candidates received :=
  mem_candidates_of_agreementProbability_ge_internal
    hcode message received hagreement

/-- Deduplicating the indexed decoder output leaves at most `listSize`
messages.
@isnad1 id=le.0h5v.s4.8de8abf843e7 from=translated src=- shape=ac4adcaf vocab=b4f6b322
-/
theorem card_candidates_le
    {messageLength listSize : ℕ} {coordinate : Type u}
    (code : BooleanListCode messageLength listSize coordinate)
    (received : coordinate → Bool) :
    (code.candidates received).card ≤ listSize :=
  card_candidates_le_internal code received

/-- For a code list-decodable to radius `1/2 - ε`, agreement
`1/2 + ε` puts the message in the decoder candidate set.
@isnad1 id=mem.2h7v.s7.7f2da9724b00 from=translated src=- shape=6fcbfd65 vocab=8362c18a
-/
theorem mem_candidates_of_half_add_margin
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {margin : ℚ}
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 / 2 + margin ≤
      agreementProbability (code.encode message) received) :
    message ∈ code.candidates received :=
  mem_candidates_of_half_add_margin_internal
    hcode message received hagreement

/-- At agreement `1/2 + ε`, the original message is selected by an actual
ceiling-logarithmic decoder-index string.
@isnad1 id=ex.2h7v.s7.65a8bb647f35 from=translated src=- shape=9455cecf vocab=8013d86c
-/
theorem exists_indexBits_of_half_add_margin
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {margin : ℚ}
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 / 2 + margin ≤
      agreementProbability (code.encode message) received) :
    ∃ bits : List Bool,
      bits.length = decoderIndexBitWidth listSize ∧
        code.decodeAtIndexBits? received bits = some message :=
  exists_indexBits_of_half_add_margin_internal
    hcode message received hagreement

/-- Hirahara's abstract list-decoding bridge: a `1/2 + ε` approximator
identifies a candidate set containing the original message and having at most
the advertised list size.
@isnad1 id=and.2h7v.s7.21de885de7cb from=translated src=- shape=1dfebcab vocab=bc47439b
-/
theorem mem_candidates_and_card_le_of_half_add_margin
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {margin : ℚ}
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 / 2 + margin ≤
      agreementProbability (code.encode message) received) :
    message ∈ code.candidates received ∧
      (code.candidates received).card ≤ listSize :=
  mem_candidates_and_card_le_of_half_add_margin_internal
    hcode message received hagreement

end BooleanListCode

end Complexity
