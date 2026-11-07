/-
  EvmAsm.EL.RLP.PrefixDecode

  Bridges from the pure RLP prefix classifier to the canonical decoder.
-/

module

public import Tengoku.EvmAsm.EvmAsm.EL.RLP.Decode
public import Tengoku.EvmAsm.EvmAsm.EL.RLP.Prefix

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace EvmAsm.EL.RLP

/-- Minimal semantic target for an executable prefix decoder.

It reports the RLP prefix class and the number of header bytes before the
payload. Empty input has no prefix to classify.-/
def decodePrefixInfo (input : List Byte) : Option (PrefixClass × Nat) :=
  match input with
  | [] => none
  | pfx :: _ => some (classifyPrefix pfx, rlpPrefixHeaderBytes pfx)

/--
@isnad1 id=eq.0h0v.s3.650e390b3fcf from=translated src=- shape=f28a9683 vocab=dc25f97e
-/
theorem decodePrefixInfo_nil :
    decodePrefixInfo ([] : List Byte) = none := rfl

/--
@isnad1 id=eq.0h2v.s4.b3c365299c17 from=translated src=- shape=17909f7f vocab=090e392a
-/
theorem decodePrefixInfo_cons (pfx : Byte) (rest : List Byte) :
    decodePrefixInfo (pfx :: rest) =
      some (classifyPrefix pfx, rlpPrefixHeaderBytes pfx) := rfl

/-- A classified single-byte prefix selects the single-byte `decodeAux` branch.
@isnad1 id=eq.1h3v.s5.c1b5938eee3e from=translated src=- shape=974f19e2 vocab=db91ab30
-/
theorem decodeAux_cons_singleByte_of_classifyPrefix
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .singleByte) :
    decodeAux (nDepth + 1) (pfx :: rest) = some (.bytes [pfx], rest) := by
  have h_lt := (classifyPrefix_singleByte_iff pfx).mp h
  simp [decodeAux, h_lt]

/-- A classified short-byte-string prefix selects the short-string branch.
@isnad1 id=eq.1h3v.s7.83a0b996689c from=translated src=- shape=a6a186ec vocab=2a5c8cd6
-/
theorem decodeAux_cons_shortBytes_of_classifyPrefix
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .shortBytes) :
    decodeAux (nDepth + 1) (pfx :: rest) =
      (do
        let (data, rest') ← takeBytes rest (rlpPrefixShortBytesPayloadLen pfx)
        match data with
        | [b] => if b.toNat < 0x80 then none else some (.bytes data, rest')
        | _ => some (.bytes data, rest')) := by
  have h_range := (classifyPrefix_shortBytes_iff pfx).mp h
  have h_not_lt : ¬ pfx.toNat < 0x80 := by omega
  unfold decodeAux rlpPrefixShortBytesPayloadLen
  simp [h_not_lt, h_range.2]
  rfl

/-- A classified long-byte-string prefix selects the long-string branch.
@isnad1 id=eq.1h3v.s7.e2c28f0ecfe2 from=translated src=- shape=189086d5 vocab=39e8f6f7
-/
theorem decodeAux_cons_longBytes_of_classifyPrefix
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .longBytes) :
    decodeAux (nDepth + 1) (pfx :: rest) =
      (do
        let (lenVal, rest') ← readLength rest (rlpPrefixLongBytesLenOfLen pfx)
        if lenVal ≤ 55 then none
        else do
          let (data, rest'') ← takeBytes rest' lenVal
          some (.bytes data, rest'')) := by
  have h_range := (classifyPrefix_longBytes_iff pfx).mp h
  have h_not_lt : ¬ pfx.toNat < 0x80 := by omega
  have h_not_short : ¬ pfx.toNat ≤ 0xB7 := by omega
  unfold decodeAux rlpPrefixLongBytesLenOfLen
  simp [h_not_lt, h_not_short, h_range.2]

/-- A classified short-list prefix selects the short-list branch.
@isnad1 id=eq.1h3v.s7.6021ea60ff19 from=translated src=- shape=a948cd18 vocab=59412070
-/
theorem decodeAux_cons_shortList_of_classifyPrefix
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .shortList) :
    decodeAux (nDepth + 1) (pfx :: rest) =
      (do
        let (payload, rest') ← takeBytes rest (rlpPrefixShortListPayloadLen pfx)
        let (items, leftover) ← decodeItems nDepth payload
        if List.isEmpty leftover then some (.list items, rest') else none) := by
  have h_range := (classifyPrefix_shortList_iff pfx).mp h
  have h_not_lt : ¬ pfx.toNat < 0x80 := by omega
  have h_not_shortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have h_not_longBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  unfold decodeAux rlpPrefixShortListPayloadLen
  simp [h_not_lt, h_not_shortBytes, h_not_longBytes, h_range.2]

/-- A classified long-list prefix selects the long-list branch.
@isnad1 id=eq.1h3v.s7.7c32fdf01768 from=translated src=- shape=dc8996a7 vocab=6ec0a35b
-/
theorem decodeAux_cons_longList_of_classifyPrefix
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .longList) :
    decodeAux (nDepth + 1) (pfx :: rest) =
      (do
        let (lenVal, rest') ← readLength rest (rlpPrefixLongListLenOfLen pfx)
        if lenVal ≤ 55 then none
        else do
          let (payload, rest'') ← takeBytes rest' lenVal
          let (items, leftover) ← decodeItems nDepth payload
          if List.isEmpty leftover then some (.list items, rest'') else none) := by
  have h_range := (classifyPrefix_longList_iff pfx).mp h
  have h_not_lt : ¬ pfx.toNat < 0x80 := by omega
  have h_not_shortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have h_not_longBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have h_not_shortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  unfold decodeAux rlpPrefixLongListLenOfLen
  simp [h_not_lt, h_not_shortBytes, h_not_longBytes, h_not_shortList]

/--
  Classifier-dispatch form of the `decodeAux` prefix branch equations. This
  packages the five class-specific bridge lemmas into one semantic target for
  executable prefix classifiers.
@isnad1 id=eq.0h3v.s9.cff108d1e12d from=translated src=- shape=560d24c2 vocab=4afc53a3
-/
theorem decodeAux_cons_eq_classifyPrefix_match
    (nDepth : Nat) (pfx : Byte) (rest : List Byte) :
    decodeAux (nDepth + 1) (pfx :: rest) =
      match classifyPrefix pfx with
      | .singleByte => some (.bytes [pfx], rest)
      | .shortBytes =>
          (do
            let (data, rest') ← takeBytes rest (rlpPrefixShortBytesPayloadLen pfx)
            match data with
            | [b] => if b.toNat < 0x80 then none else some (.bytes data, rest')
            | _ => some (.bytes data, rest'))
      | .longBytes =>
          (do
            let (lenVal, rest') ← readLength rest (rlpPrefixLongBytesLenOfLen pfx)
            if lenVal ≤ 55 then none
            else do
              let (data, rest'') ← takeBytes rest' lenVal
              some (.bytes data, rest''))
      | .shortList =>
          (do
            let (payload, rest') ← takeBytes rest (rlpPrefixShortListPayloadLen pfx)
            let (items, leftover) ← decodeItems nDepth payload
            if List.isEmpty leftover then some (.list items, rest') else none)
      | .longList =>
          (do
            let (lenVal, rest') ← readLength rest (rlpPrefixLongListLenOfLen pfx)
            if lenVal ≤ 55 then none
            else do
              let (payload, rest'') ← takeBytes rest' lenVal
              let (items, leftover) ← decodeItems nDepth payload
              if List.isEmpty leftover then some (.list items, rest'') else none) := by
  cases h : classifyPrefix pfx
  · rw [decodeAux_cons_singleByte_of_classifyPrefix nDepth pfx rest h]
  · rw [decodeAux_cons_shortBytes_of_classifyPrefix nDepth pfx rest h]
  · rw [decodeAux_cons_longBytes_of_classifyPrefix nDepth pfx rest h]
  · rw [decodeAux_cons_shortList_of_classifyPrefix nDepth pfx rest h]
  · rw [decodeAux_cons_longList_of_classifyPrefix nDepth pfx rest h]

/--
  Top-level `decode` wrapper version of `decodeAux_cons_eq_classifyPrefix_match`.
  This exposes the pure prefix classifier as the first dispatch point for every
  nonempty RLP input stream.
@isnad1 id=eq.0h2v.s9.132a225a0b9d from=translated src=- shape=251f163b vocab=3351234e
-/
theorem decode_cons_eq_classifyPrefix_match (pfx : Byte) (rest : List Byte) :
    decode (pfx :: rest) =
      match classifyPrefix pfx with
      | .singleByte => some (.bytes [pfx], rest)
      | .shortBytes =>
          (do
            let (data, rest') ← takeBytes rest (rlpPrefixShortBytesPayloadLen pfx)
            match data with
            | [b] => if b.toNat < 0x80 then none else some (.bytes data, rest')
            | _ => some (.bytes data, rest'))
      | .longBytes =>
          (do
            let (lenVal, rest') ← readLength rest (rlpPrefixLongBytesLenOfLen pfx)
            if lenVal ≤ 55 then none
            else do
              let (data, rest'') ← takeBytes rest' lenVal
              some (.bytes data, rest''))
      | .shortList =>
          (do
            let (payload, rest') ← takeBytes rest (rlpPrefixShortListPayloadLen pfx)
            let (items, leftover) ← decodeItems (2 * rest.length + 1) payload
            if List.isEmpty leftover then some (.list items, rest') else none)
      | .longList =>
          (do
            let (lenVal, rest') ← readLength rest (rlpPrefixLongListLenOfLen pfx)
            if lenVal ≤ 55 then none
            else do
              let (payload, rest'') ← takeBytes rest' lenVal
              let (items, leftover) ← decodeItems (2 * rest.length + 1) payload
              if List.isEmpty leftover then some (.list items, rest'') else none) := by
  unfold decode
  rw [show 2 * (pfx :: rest).length = (2 * rest.length + 1) + 1 by simp; omega]
  exact decodeAux_cons_eq_classifyPrefix_match (2 * rest.length + 1) pfx rest

end EvmAsm.EL.RLP
