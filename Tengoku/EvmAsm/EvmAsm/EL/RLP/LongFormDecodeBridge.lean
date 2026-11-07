/-
  EvmAsm.EL.RLP.LongFormDecodeBridge

  Long-form decode bridges using the packaged read-length result (GH #120).
-/

module

public import Tengoku.EvmAsm.EvmAsm.EL.RLP.PrefixDecode
public import Tengoku.EvmAsm.EvmAsm.EL.RLP.ListDecodeBridge
public import Tengoku.EvmAsm.EvmAsm.EL.RLP.ReadLengthBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

public section

namespace EvmAsm.EL.RLP

namespace LongFormDecodeBridge

abbrev LengthFieldResult := ReadLengthBridge.LengthFieldResult

/--
Long byte-string branch expressed through the packaged length-field result.

Distinctive token: RLP.LongFormDecodeBridge.decodeAux_long_bytes_lengthField #120.
@isnad1 id=eq.2h4v.s6.e213ce54b805 from=translated src=- shape=93292445 vocab=49681a41
-/
theorem decodeAux_long_bytes_lengthField
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (lengthField : LengthFieldResult)
    (h_class : classifyPrefix pfx = .longBytes)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongBytesLenOfLen pfx) = some lengthField) :
    decodeAux (fuel + 1) (pfx :: rest) =
      if lengthField.length ≤ 55 then none
      else
        match takeBytes lengthField.rest lengthField.length with
        | none => none
        | some (data, rest'') => some (.bytes data, rest'') := by
  cases lengthField with
  | mk lenVal rest' =>
      have h_read := (ReadLengthBridge.decodeLengthField?_eq_some_iff).1 h_len
      rw [decodeAux_cons_longBytes_of_classifyPrefix fuel pfx rest h_class]
      by_cases h_short : lenVal ≤ 55
      · simp [h_read, h_short]
      · simp [h_read, h_short]
        cases takeBytes rest' lenVal <;> rfl

/--
@isnad1 id=eq.2h3v.s5.5ef42f6ef6ff from=translated src=- shape=c9d029db vocab=67c37b39
-/
theorem decodeAux_long_bytes_lengthField_none
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .longBytes)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongBytesLenOfLen pfx) = none) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  rw [decodeAux_cons_longBytes_of_classifyPrefix fuel pfx rest h_class]
  unfold ReadLengthBridge.decodeLengthField? at h_len
  cases h_read : readLength rest (rlpPrefixLongBytesLenOfLen pfx) with
  | none => rfl
  | some decoded => simp [h_read] at h_len

/--
@isnad1 id=eq.3h4v.s6.1584cf528c34 from=translated src=- shape=6db9dcaf vocab=2c9ed259
-/
theorem decodeAux_long_bytes_lengthField_short_rejected
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (lengthField : LengthFieldResult)
    (h_class : classifyPrefix pfx = .longBytes)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongBytesLenOfLen pfx) = some lengthField)
    (h_short : lengthField.length ≤ 55) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  rw [decodeAux_long_bytes_lengthField fuel pfx rest lengthField h_class h_len]
  simp [h_short]

/--
@isnad1 id=eq.4h6v.s6.593a6696b32f from=translated src=- shape=d9480c39 vocab=8fa7ae84
-/
theorem decodeAux_long_bytes_lengthField_payload
    (fuel : Nat) (pfx : Byte) (rest data rest'' : List Byte)
    (lengthField : LengthFieldResult)
    (h_class : classifyPrefix pfx = .longBytes)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongBytesLenOfLen pfx) = some lengthField)
    (h_long : ¬ lengthField.length ≤ 55)
    (h_take : takeBytes lengthField.rest lengthField.length =
      some (data, rest'')) :
    decodeAux (fuel + 1) (pfx :: rest) = some (.bytes data, rest'') := by
  rw [decodeAux_long_bytes_lengthField fuel pfx rest lengthField h_class h_len]
  simp [h_long, h_take]

/-- Long list branch expressed through the packaged length-field result.
@isnad1 id=eq.2h4v.s7.e8965a5d1970 from=translated src=- shape=48593232 vocab=4913d062
-/
theorem decodeAux_long_list_lengthField
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (lengthField : LengthFieldResult)
    (h_class : classifyPrefix pfx = .longList)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongListLenOfLen pfx) = some lengthField) :
    decodeAux (fuel + 1) (pfx :: rest) =
      if lengthField.length ≤ 55 then none
      else
        match takeBytes lengthField.rest lengthField.length with
        | none => none
        | some (payload, rest'') =>
            match decodeItems fuel payload with
            | none => none
            | some (items, leftover) =>
                if List.isEmpty leftover then some (.list items, rest'') else none := by
  cases lengthField with
  | mk lenVal rest' =>
      have h_read := (ReadLengthBridge.decodeLengthField?_eq_some_iff).1 h_len
      rw [decodeAux_cons_longList_of_classifyPrefix fuel pfx rest h_class]
      by_cases h_short : lenVal ≤ 55
      · simp [h_read, h_short]
      · simp [h_read, h_short]
        cases h_take : takeBytes rest' lenVal with
        | none => rfl
        | some decoded =>
            cases decoded with
            | mk payload rest'' =>
                cases h_decode : decodeItems fuel payload with
                | none => simp [h_decode]
                | some decodedItems =>
                    cases decodedItems with
                    | mk items leftover =>
                        simp [h_decode]

/--
Long list branch expressed through both the packaged length-field result and
the list-payload decoder bridge.

Distinctive token:
LongFormDecodeBridge.decodeAux_long_list_lengthField_decodeListPayload #120.
@isnad1 id=eq.2h4v.s7.b24ff25b5f60 from=translated src=- shape=af44a109 vocab=d5968292
-/
theorem decodeAux_long_list_lengthField_decodeListPayload
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (lengthField : LengthFieldResult)
    (h_class : classifyPrefix pfx = .longList)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongListLenOfLen pfx) = some lengthField) :
    decodeAux (fuel + 1) (pfx :: rest) =
      if lengthField.length ≤ 55 then none
      else
        match takeBytes lengthField.rest lengthField.length with
        | none => none
        | some (payload, rest'') => (do
            let items ← ListDecodeBridge.decodeListPayload fuel payload
            some (.list items, rest'')) := by
  rw [decodeAux_long_list_lengthField fuel pfx rest lengthField h_class h_len]
  by_cases h_short : lengthField.length ≤ 55
  · simp [h_short]
  · simp [h_short]
    cases h_take : takeBytes lengthField.rest lengthField.length with
    | none => rfl
    | some decoded =>
        cases decoded with
        | mk payload rest'' =>
            cases h_decode : decodeItems fuel payload with
            | none => simp [ListDecodeBridge.decodeListPayload, h_decode]
            | some decodedItems =>
                cases decodedItems with
                | mk items leftover =>
                    cases leftover <;> simp [ListDecodeBridge.decodeListPayload, h_decode]

/--
@isnad1 id=eq.2h3v.s5.2b8d4ae3aa85 from=translated src=- shape=c9d029db vocab=1b141389
-/
theorem decodeAux_long_list_lengthField_none
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .longList)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongListLenOfLen pfx) = none) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  rw [decodeAux_cons_longList_of_classifyPrefix fuel pfx rest h_class]
  unfold ReadLengthBridge.decodeLengthField? at h_len
  cases h_read : readLength rest (rlpPrefixLongListLenOfLen pfx) with
  | none => rfl
  | some decoded => simp [h_read] at h_len

/--
@isnad1 id=eq.3h4v.s6.69b426c4f453 from=translated src=- shape=6db9dcaf vocab=e8031e68
-/
theorem decodeAux_long_list_lengthField_short_rejected
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (lengthField : LengthFieldResult)
    (h_class : classifyPrefix pfx = .longList)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongListLenOfLen pfx) = some lengthField)
    (h_short : lengthField.length ≤ 55) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  rw [decodeAux_long_list_lengthField fuel pfx rest lengthField h_class h_len]
  simp [h_short]

/--
@isnad1 id=eq.5h7v.s7.05e74bf6a92c from=translated src=- shape=a47a32ec vocab=b25b93b3
-/
theorem decodeAux_long_list_lengthField_success
    (fuel : Nat) (pfx : Byte) (rest payload rest'' : List Byte)
    (items : List RLPItem) (lengthField : LengthFieldResult)
    (h_class : classifyPrefix pfx = .longList)
    (h_len : ReadLengthBridge.decodeLengthField? rest
      (rlpPrefixLongListLenOfLen pfx) = some lengthField)
    (h_long : ¬ lengthField.length ≤ 55)
    (h_take : takeBytes lengthField.rest lengthField.length =
      some (payload, rest''))
    (h_decode : decodeItems fuel payload = some (items, [])) :
    decodeAux (fuel + 1) (pfx :: rest) = some (.list items, rest'') := by
  rw [decodeAux_long_list_lengthField fuel pfx rest lengthField h_class h_len]
  simp [h_long, h_take, h_decode]

end LongFormDecodeBridge

end EvmAsm.EL.RLP
