/-
  EvmAsm.EL.RLP.FullDecode

  Top-level wrapper for consumers that require an RLP decode to consume the
  whole input.
-/

module

public import Tengoku.EvmAsm.EvmAsm.EL.RLP.Decode

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace EvmAsm.EL.RLP

/-- Decode one complete RLP item, rejecting successful prefix decodes that
leave trailing input.-/
def decodeFully (bs : List Byte) : Option RLPItem :=
  match decode bs with
  | some (item, []) => some item
  | _ => none

/-- Distinctive token: FullDecode.decodeFully_eq_some_iff #120.
@isnad1 id=iff.0h2v.s5.b4135d7c5c75 from=translated src=- shape=9220dcbc vocab=4c386337
-/
theorem decodeFully_eq_some_iff (bs : List Byte) (item : RLPItem) :
    decodeFully bs = some item ↔ decode bs = some (item, []) := by
  unfold decodeFully
  cases h_decode : decode bs with
  | none =>
      simp
  | some decoded =>
      cases decoded with
      | mk item' leftover =>
          cases leftover with
          | nil => simp
          | cons b rest => simp

/--
Complete-decode success as an existential raw-decoder fact.

Distinctive token: FullDecode.decodeFully_ne_none_iff_exists_decode_empty #120.
@isnad1 id=iff.0h1v.s5.b2ce2831aa68 from=translated src=- shape=2ac2a98b vocab=96ef2929
-/
theorem decodeFully_ne_none_iff_exists_decode_empty (bs : List Byte) :
    decodeFully bs ≠ none ↔ ∃ item, decode bs = some (item, []) := by
  constructor
  · unfold decodeFully
    cases h_decode : decode bs with
    | none =>
        simp
    | some decoded =>
        cases decoded with
        | mk item leftover =>
            cases leftover with
            | nil =>
                intro _
                exact ⟨item, by simp [h_decode.symm]⟩
            | cons b rest =>
                simp
  · rintro ⟨item, h_decode⟩ h_none
    have h_some : decodeFully bs = some item :=
      (decodeFully_eq_some_iff bs item).2 h_decode
    rw [h_some] at h_none
    contradiction

/--
@isnad1 id=eq.1h1v.s4.16aecc98a5f7 from=translated src=- shape=f14ddf9f vocab=c8cd12fc
-/
theorem decodeFully_eq_none_of_decode_none
    {bs : List Byte} (h_decode : decode bs = none) :
    decodeFully bs = none := by
  simp [decodeFully, h_decode]

/--
@isnad1 id=eq.2h3v.s5.2b5c85af3f68 from=translated src=- shape=4275c888 vocab=96ef2929
-/
theorem decodeFully_eq_none_of_decode_leftover
    {bs leftover : List Byte} {item : RLPItem}
    (h_decode : decode bs = some (item, leftover))
    (h_leftover : leftover ≠ []) :
    decodeFully bs = none := by
  unfold decodeFully
  cases leftover with
  | nil => contradiction
  | cons b rest => simp [h_decode]

/--
Complete-decode failure is exactly either decoder failure or successful
prefix decode with trailing bytes left over.

Distinctive token: FullDecode.decodeFully_eq_none_iff #120.
@isnad1 id=iff.0h1v.s5.c31cc5ee9e89 from=translated src=- shape=ca92cf2b vocab=96ef2929
-/
theorem decodeFully_eq_none_iff (bs : List Byte) :
    decodeFully bs = none ↔
      decode bs = none ∨
        ∃ item leftover, decode bs = some (item, leftover) ∧ leftover ≠ [] := by
  unfold decodeFully
  cases h_decode : decode bs with
  | none => simp
  | some decoded =>
      cases decoded with
      | mk item leftover =>
          cases leftover with
          | nil => simp
          | cons b rest =>
              constructor
              · intro _
                exact Or.inr ⟨item, b :: rest, rfl, by simp⟩
              · intro _
                rfl

/--
@isnad1 id=eq.1h2v.s5.698d4ea97a27 from=translated src=- shape=0f4e6325 vocab=4c386337
-/
theorem decodeFully_eq_some_of_decode
    {bs : List Byte} {item : RLPItem}
    (h_decode : decode bs = some (item, [])) :
    decodeFully bs = some item := by
  exact (decodeFully_eq_some_iff bs item).2 h_decode

/--
@isnad1 id=eq.1h1v.s5.1c7249f118e6 from=translated src=- shape=693ea2d3 vocab=b19a8261
-/
theorem decodeFully_encode_of_decode_encode
    {item : RLPItem}
    (h_roundtrip : decode (encode item) = some (item, [])) :
    decodeFully (encode item) = some item := by
  exact decodeFully_eq_some_of_decode h_roundtrip

end EvmAsm.EL.RLP
