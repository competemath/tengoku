/-
  EvmAsm.EL.RLP.ReadLengthBridge

  Reusable result bridge for RLP long-form length-field decoding (GH #120).
-/

module

public import Tengoku.EvmAsm.EvmAsm.EL.RLP.ReadLength

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace EvmAsm.EL.RLP

namespace ReadLengthBridge

/-- Decoded long-form RLP length field plus the input remainder after the
    length bytes.-/
structure LengthFieldResult where
  length : Nat
  rest : List Byte
  deriving Repr

/--
Decode exactly `n` bytes as a canonical big-endian RLP length field.

This is a small executable-spec bridge over `readLength`: later RISC-V
decoder phases can target this result object without duplicating the
leading-zero rejection and remainder plumbing.

Distinctive token: RLP.ReadLengthBridge.decodeLengthField? #120.-/
def decodeLengthField? (bs : List Byte) (n : Nat) :
    Option LengthFieldResult := do
  let (lenVal, rest) ← readLength bs n
  some { length := lenVal, rest := rest }

theorem decodeLengthField?_eq_some_iff
    {bs : List Byte} {n lenVal : Nat} {rest : List Byte} :
    decodeLengthField? bs n = some { length := lenVal, rest := rest } ↔
      readLength bs n = some (lenVal, rest) := by
  constructor
  · unfold decodeLengthField?
    cases readLength bs n with
    | none => simp
    | some decoded =>
        cases decoded with
        | mk lenVal' rest' =>
            intro h
            injection h with h_result
            cases h_result
            rfl
  · intro h
    simp [decodeLengthField?, h]

end ReadLengthBridge

end EvmAsm.EL.RLP
