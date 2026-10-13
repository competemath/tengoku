/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.ListDecoding.Defs
import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.FiniteEnsemble.Internal

/-!
# Finite Boolean list decoding -- proof internals
-/

public section

universe u

namespace Complexity

namespace BooleanListCode

/--
@isnad1 id=eq.0h2v.s3.fb622da58dec from=translated src=- shape=97f23171 vocab=1d63b9f9
-/
theorem length_encodeDecoderIndex_internal
    {listSize : ℕ} (index : Fin listSize) :
    (encodeDecoderIndex index).length = decoderIndexBitWidth listSize := by
  simp [encodeDecoderIndex, decoderIndexBitWidth]

/--
@isnad1 id=eq.0h2v.s4.f1d35f43c714 from=translated src=- shape=e515e695 vocab=e2817dab
-/
theorem decodeDecoderIndex?_encodeDecoderIndex_internal
    {listSize : ℕ} (index : Fin listSize) :
    decodeDecoderIndex? listSize (encodeDecoderIndex index) = some index := by
  simp [decodeDecoderIndex?, encodeDecoderIndex]

/--
@isnad1 id=eq.0h6v.s5.c86235c5220e from=translated src=- shape=f5950c9a vocab=85293def
-/
theorem decodeAtIndexBits?_encodeDecoderIndex_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    (code : BooleanListCode messageLength listSize coordinate)
    (received : coordinate → Bool) (index : Fin listSize) :
    code.decodeAtIndexBits? received (encodeDecoderIndex index) =
      some (code.decode received index) := by
  simp [decodeAtIndexBits?, decodeDecoderIndex?_encodeDecoderIndex_internal]

/--
@isnad1 id=eq.0h3v.s5.fa6e2c2731b8 from=translated src=- shape=e1412eb0 vocab=890c7541
-/
theorem relativeDistance_eq_one_sub_agreementProbability_internal
    {coordinate : Type u} [Fintype coordinate] [DecidableEq coordinate]
    [Nonempty coordinate] (left right : coordinate → Bool) :
    relativeDistance left right = 1 - agreementProbability left right := by
  have hevent :
      (Finset.univ.filter fun input => left input ≠ right input) =
        (Finset.univ.filter fun input => left input = right input)ᶜ := by
    ext input
    simp
  rw [relativeDistance, agreementProbability, hevent,
    uniformProbability_compl_internal]

/--
@isnad1 id=eq.0h3v.s5.c0e1f0889ea3 from=translated src=- shape=1f967c7d vocab=157582dd
-/
theorem agreementProbability_add_relativeDistance_internal
    {coordinate : Type u} [Fintype coordinate] [DecidableEq coordinate]
    [Nonempty coordinate] (left right : coordinate → Bool) :
    agreementProbability left right + relativeDistance left right = 1 := by
  rw [relativeDistance_eq_one_sub_agreementProbability_internal]
  ring

/--
@isnad1 id=le.1h4v.s5.f2a32a633464 from=translated src=- shape=cf743c47 vocab=fb056d84
-/
theorem relativeDistance_le_of_agreementProbability_ge_internal
    {coordinate : Type u} [Fintype coordinate] [DecidableEq coordinate]
    [Nonempty coordinate] {left right : coordinate → Bool} {radius : ℚ}
    (hagreement : 1 - radius ≤ agreementProbability left right) :
    relativeDistance left right ≤ radius := by
  rw [relativeDistance_eq_one_sub_agreementProbability_internal]
  linarith

/--
@isnad1 id=ex.2h7v.s6.76e43b898611 from=translated src=- shape=b78d4f78 vocab=2dca3422
-/
theorem exists_decoder_index_of_agreementProbability_ge_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {radius : ℚ}
    (hcode : code.IsListDecodableAt radius)
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 - radius ≤
      agreementProbability (code.encode message) received) :
    ∃ index, code.decode received index = message := by
  exact hcode message received
    (relativeDistance_le_of_agreementProbability_ge_internal hagreement)

/--
@isnad1 id=ex.2h7v.s6.f138a164d1a1 from=translated src=- shape=4049eaf1 vocab=5e740219
-/
theorem exists_indexBits_of_agreementProbability_ge_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {radius : ℚ}
    (hcode : code.IsListDecodableAt radius)
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 - radius ≤
      agreementProbability (code.encode message) received) :
    ∃ bits : List Bool,
      bits.length = decoderIndexBitWidth listSize ∧
        code.decodeAtIndexBits? received bits = some message := by
  obtain ⟨index, hdecode⟩ :=
    exists_decoder_index_of_agreementProbability_ge_internal
      hcode message received hagreement
  refine ⟨encodeDecoderIndex index,
    length_encodeDecoderIndex_internal index, ?_⟩
  rw [decodeAtIndexBits?_encodeDecoderIndex_internal, hdecode]

/--
@isnad1 id=mem.2h7v.s6.5ec2b2a72e11 from=translated src=- shape=58ccbfbc vocab=05c5e177
-/
theorem mem_candidates_of_agreementProbability_ge_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {radius : ℚ}
    (hcode : code.IsListDecodableAt radius)
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 - radius ≤
      agreementProbability (code.encode message) received) :
    message ∈ code.candidates received := by
  obtain ⟨index, hdecode⟩ :=
    exists_decoder_index_of_agreementProbability_ge_internal
      hcode message received hagreement
  exact Finset.mem_image.mpr ⟨index, Finset.mem_univ index, hdecode⟩

/--
@isnad1 id=le.0h5v.s4.8de8abf843e7 from=translated src=- shape=ac4adcaf vocab=b4f6b322
-/
theorem card_candidates_le_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    (code : BooleanListCode messageLength listSize coordinate)
    (received : coordinate → Bool) :
    (code.candidates received).card ≤ listSize := by
  unfold candidates
  calc
    (Finset.univ.image (code.decode received)).card ≤
        (Finset.univ : Finset (Fin listSize)).card :=
      Finset.card_image_le
    _ = listSize := by simp

/--
@isnad1 id=mem.2h7v.s7.7f2da9724b00 from=translated src=- shape=6fcbfd65 vocab=8362c18a
-/
theorem mem_candidates_of_half_add_margin_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {margin : ℚ}
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 / 2 + margin ≤
      agreementProbability (code.encode message) received) :
    message ∈ code.candidates received := by
  apply mem_candidates_of_agreementProbability_ge_internal
    hcode message received
  convert hagreement using 1
  all_goals ring

/--
@isnad1 id=ex.2h7v.s7.65a8bb647f35 from=translated src=- shape=9455cecf vocab=8013d86c
-/
theorem exists_indexBits_of_half_add_margin_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {margin : ℚ}
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 / 2 + margin ≤
      agreementProbability (code.encode message) received) :
    ∃ bits : List Bool,
      bits.length = decoderIndexBitWidth listSize ∧
        code.decodeAtIndexBits? received bits = some message := by
  apply exists_indexBits_of_agreementProbability_ge_internal
    hcode message received
  convert hagreement using 1
  all_goals ring

/--
@isnad1 id=and.2h7v.s7.21de885de7cb from=translated src=- shape=1dfebcab vocab=bc47439b
-/
theorem mem_candidates_and_card_le_of_half_add_margin_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {margin : ℚ}
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 / 2 + margin ≤
      agreementProbability (code.encode message) received) :
    message ∈ code.candidates received ∧
      (code.candidates received).card ≤ listSize := by
  exact ⟨mem_candidates_of_half_add_margin_internal
    hcode message received hagreement,
    card_candidates_le_internal code received⟩

end BooleanListCode

end Complexity
