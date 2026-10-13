/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Hamming.Code.Defs
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Hamming.Internal

/-!
# Finite Boolean codes -- proof internals
-/

public section

namespace Complexity

namespace BooleanCode

/--
@isnad1 id=iff.0h4v.s5.923c0ad250cc from=translated src=- shape=2c07b237 vocab=cf9b4a29
-/
theorem mem_codewords_iff_internal {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (word : BooleanHamming.Word blockLength) :
    word ∈ code.codewords ↔ ∃ message, code.encode message = word := by
  simp [codewords]

/--
@isnad1 id=eq.0h3v.s5.29318486539d from=translated src=- shape=eb4de368 vocab=07c34245
-/
theorem card_codewords_internal {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength) :
    code.codewords.card = 2 ^ messageLength := by
  rw [codewords,
    Finset.card_image_of_injective Finset.univ code.encode_injective,
    Finset.card_univ, card_finArrowBool]

/--
@isnad1 id=issepara.1h4v.s4.4da3b4b789cd from=translated src=- shape=d7e5d263 vocab=9e688a0f
-/
theorem isSeparated_codewords_internal {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength} {minimumDistance : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance) :
    BooleanHamming.IsSeparated code.codewords minimumDistance := by
  intro left hleft right hright hne
  obtain ⟨leftMessage, hleftCode⟩ :=
    (mem_codewords_iff_internal code left).mp hleft
  obtain ⟨rightMessage, hrightCode⟩ :=
    (mem_codewords_iff_internal code right).mp hright
  have hmessages : leftMessage ≠ rightMessage := by
    intro heq
    apply hne
    rw [← hleftCode, ← hrightCode, heq]
  simpa [hleftCode, hrightCode] using
    hdistance leftMessage rightMessage hmessages

/--
@isnad1 id=le.2h5v.s6.12536e1dccf4 from=translated src=- shape=5cd4ed3a vocab=8744729a
-/
theorem packing_bound_internal {messageLength blockLength minimumDistance radius : ℕ}
    {code : BooleanCode messageLength blockLength}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance) :
    2 ^ messageLength * BooleanHamming.volume blockLength radius ≤
      2 ^ blockLength := by
  have hpacking := BooleanHamming.packing_bound_internal
    (code := code.codewords)
    (isSeparated_codewords_internal hdistance) hradius
  rw [card_codewords_internal] at hpacking
  exact hpacking

/--
@isnad1 id=iff.0h6v.s5.08795486d879 from=translated src=- shape=4fb8a0e8 vocab=6df0f031
-/
theorem mem_decodeCandidates_iff_internal {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (received : BooleanHamming.Word blockLength) (radius : ℕ)
    (message : BooleanHamming.Word messageLength) :
    message ∈ code.decodeCandidates received radius ↔
      BooleanHamming.distance (code.encode message) received ≤ radius := by
  simp [decodeCandidates]

/--
@isnad1 id=mem.1h6v.s5.b7c280b865e5 from=translated src=- shape=2a529010 vocab=6df0f031
-/
theorem mem_decodeCandidates_of_close_internal {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (received : BooleanHamming.Word blockLength) (radius : ℕ)
    (message : BooleanHamming.Word messageLength)
    (hclose : BooleanHamming.distance (code.encode message) received ≤ radius) :
    message ∈ code.decodeCandidates received radius := by
  exact (mem_decodeCandidates_iff_internal code received radius message).mpr hclose

theorem eq_of_mem_decodeCandidates_internal {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength)
    {left right : BooleanHamming.Word messageLength}
    (hleft : left ∈ code.decodeCandidates received radius)
    (hright : right ∈ code.decodeCandidates received radius) :
    left = right := by
  by_contra hne
  have hminimum := hdistance left right hne
  have hleftClose :=
    (mem_decodeCandidates_iff_internal code received radius left).mp hleft
  have hrightClose :=
    (mem_decodeCandidates_iff_internal code received radius right).mp hright
  have hreceivedRight :
      BooleanHamming.distance received (code.encode right) ≤ radius := by
    rw [BooleanHamming.distance_comm_internal]
    exact hrightClose
  have htriangle := BooleanHamming.distance_triangle_internal
    (code.encode left) received (code.encode right)
  omega

/--
@isnad1 id=le.2h6v.s5.20a2fad0701b from=translated src=- shape=f94a6900 vocab=d44fc7b7
-/
theorem card_decodeCandidates_le_one_internal {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength) :
    (code.decodeCandidates received radius).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro left right hleft hright
  exact eq_of_mem_decodeCandidates_internal
    hdistance hradius received hleft hright

/--
@isnad1 id=eq.3h7v.s6.903c8ab1fb11 from=translated src=- shape=e60b2896 vocab=620c73b3
-/
theorem decodeCandidates_eq_singleton_of_close_internal
    {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength)
    (message : BooleanHamming.Word messageLength)
    (hclose : BooleanHamming.distance (code.encode message) received ≤ radius) :
    code.decodeCandidates received radius = {message} := by
  have hmessage :=
    mem_decodeCandidates_of_close_internal code received radius message hclose
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hmessage, ?_⟩
  intro candidate hcandidate
  exact eq_of_mem_decodeCandidates_internal
    hdistance hradius received hcandidate hmessage

/--
@isnad1 id=eq.3h7v.s6.af9c0dd2e544 from=translated src=- shape=278fec9d vocab=1fab3dbb
-/
theorem decodeUnique?_eq_some_of_close_internal
    {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength)
    (message : BooleanHamming.Word messageLength)
    (hclose : BooleanHamming.distance (code.encode message) received ≤ radius) :
    code.decodeUnique? received radius = some message := by
  rw [decodeUnique?,
    decodeCandidates_eq_singleton_of_close_internal
      hdistance hradius received message hclose]
  simp

end BooleanCode

end Complexity
