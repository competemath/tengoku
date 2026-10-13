/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.Encoding.Positions.Defs
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.Encoding.Positions.Internal

/-!
# Reading the structure encoding by table site

The computable positions recover every relation and constant-table bit. The
full encoded length is strictly increasing with universe size, so at a fixed
input length there can be at most one structure size.
-/

public section

namespace Complexity.DescriptiveComplexity

/-- Every relation and constant-table site occurs in the encoder's ordering.
@isnad1 id=mem.0h3v.s4.3b33e12fca17 from=translated src=- shape=8b56728a vocab=624ef3c7
-/
theorem mem_encodingTableSites (V : Vocabulary) (card : Nat) (site : InputSite V card) :
    site ∈ encodingTableSites V card := mem_encodingTableSites_internal V card site

/-- The existing structure encoder has the named encoded length.
@isnad1 id=eq.0h2v.s4.c1379e04c2e7 from=translated src=- shape=7f817f27 vocab=eb50f217
-/
theorem encodeStruct_length_eq {V : Vocabulary} (A : DecFinStruct V) :
    (encodeStruct A).length = encodingLength V A.card := encodeStruct_length A

/-- The unary prefix alone is longer than the represented universe size.
@isnad1 id=lt.0h2v.s3.e2e9555c1410 from=translated src=- shape=58a504ac vocab=2abc34d6
-/
theorem card_lt_encodingLength (V : Vocabulary) (card : Nat) :
    card < encodingLength V card := by
  unfold encodingLength
  omega

/-- Encoded lengths are positive even when all relation and constant tables are empty.
@isnad1 id=lt.0h2v.s3.8e5d6b432400 from=translated src=- shape=787c1379 vocab=2abc34d6
-/
theorem encodingLength_pos (V : Vocabulary) (card : Nat) : 0 < encodingLength V card :=
  Nat.lt_of_le_of_lt (Nat.zero_le card) (card_lt_encodingLength V card)

/-- The unary prefix makes encoded length strictly increasing in universe size.
@isnad1 id=strictmo.0h1v.s3.1bef1c36ce4c from=translated src=- shape=8735051e vocab=2b9f39a1
-/
theorem encodingLength_strictMono (V : Vocabulary) : StrictMono (encodingLength V) :=
  encodingLength_strictMono_internal V

/-- Every table site occurs exactly once in the encoder's ordering.
@isnad1 id=nodup.0h2v.s3.d53ed8164241 from=translated src=- shape=a3b7a634 vocab=1440c4a7
-/
theorem encodingTableSites_nodup (V : Vocabulary) (card : Nat) :
    (encodingTableSites V card).Nodup := encodingTableSites_nodup_internal V card

/-- The header contains `card` true bits followed by the false terminator.
@isnad1 id=eq.0h3v.s6.2ef630fa0fcc from=translated src=- shape=dede6886 vocab=5b472729
-/
theorem getElem?_encodeStruct_header {V : Vocabulary} (A : DecFinStruct V)
    (i : Fin (A.card + 1)) :
    (encodeStruct A)[i.val]? = some (decide (i.val < A.card)) :=
  getElem?_encodeStruct_header_internal A i

end Complexity.DescriptiveComplexity
