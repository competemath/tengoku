/-
  EvmAsm.EL.RLP.LongForm

  Branch lemmas for long-form byte-string and list decoding.
-/
module

public import Tengoku.EvmAsm.EvmAsm.EL.RLP.Decode

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

public section

namespace EvmAsm.EL.RLP

/-! ## Long-form byte strings -/

/--
@isnad1 id=eq.3h3v.s6.f94907c6d18f from=translated src=- shape=9110992d vocab=50458016
-/
theorem decodeAux_long_bytes_readLength_none (fuel : Nat) (pfx : Byte)
    (rest : List Byte)
    (hLong : 0xB7 < pfx.toNat) (hBytes : pfx.toNat ≤ 0xBF)
    (hRead : readLength rest (pfx.toNat - 0xB7) = none) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShort : ¬ pfx.toNat ≤ 0xB7 := by omega
  simp [decodeAux, hNotSingle, hNotShort, hBytes, hRead]

/--
@isnad1 id=eq.4h5v.s6.6a76cf246028 from=translated src=- shape=84192323 vocab=83001a46
-/
theorem decodeAux_long_bytes_short_length_rejected (fuel : Nat) (pfx : Byte)
    (rest rest' : List Byte) (lenVal : Nat)
    (hLong : 0xB7 < pfx.toNat) (hBytes : pfx.toNat ≤ 0xBF)
    (hRead : readLength rest (pfx.toNat - 0xB7) = some (lenVal, rest'))
    (hShort : lenVal ≤ 55) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShort : ¬ pfx.toNat ≤ 0xB7 := by omega
  simp [decodeAux, hNotSingle, hNotShort, hBytes, hRead, hShort]

/--
@isnad1 id=eq.5h5v.s7.4a0db4fab59c from=translated src=- shape=3def52af vocab=bc9972b2
-/
theorem decodeAux_long_bytes_payload_none (fuel : Nat) (pfx : Byte)
    (rest rest' : List Byte) (lenVal : Nat)
    (hLong : 0xB7 < pfx.toNat) (hBytes : pfx.toNat ≤ 0xBF)
    (hRead : readLength rest (pfx.toNat - 0xB7) = some (lenVal, rest'))
    (hLen : ¬ lenVal ≤ 55)
    (hTake : takeBytes rest' lenVal = none) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShort : ¬ pfx.toNat ≤ 0xB7 := by omega
  simp [decodeAux, hNotSingle, hNotShort, hBytes, hRead, hLen, hTake]

/--
@isnad1 id=eq.5h7v.s7.c4132cf9742e from=translated src=- shape=91c3478e vocab=faa0ad64
-/
theorem decodeAux_long_bytes_success (fuel : Nat) (pfx : Byte)
    (rest rest' rest'' data : List Byte) (lenVal : Nat)
    (hLong : 0xB7 < pfx.toNat) (hBytes : pfx.toNat ≤ 0xBF)
    (hRead : readLength rest (pfx.toNat - 0xB7) = some (lenVal, rest'))
    (hLen : ¬ lenVal ≤ 55)
    (hTake : takeBytes rest' lenVal = some (data, rest'')) :
    decodeAux (fuel + 1) (pfx :: rest) = some (.bytes data, rest'') := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShort : ¬ pfx.toNat ≤ 0xB7 := by omega
  simp [decodeAux, hNotSingle, hNotShort, hBytes, hRead, hLen, hTake]

/-! ## Long-form lists -/

/--
@isnad1 id=eq.2h3v.s6.c7586c08cb8f from=translated src=- shape=0de22eff vocab=f78b50a9
-/
theorem decodeAux_long_list_readLength_none (fuel : Nat) (pfx : Byte)
    (rest : List Byte)
    (hLong : 0xF7 < pfx.toNat)
    (hRead : readLength rest (pfx.toNat - 0xF7) = none) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have hNotLongBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have hNotShortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  simp [decodeAux, hNotSingle, hNotShortBytes, hNotLongBytes, hNotShortList,
    hRead]

/--
@isnad1 id=eq.3h5v.s6.ec356de00bc1 from=translated src=- shape=5d915e4c vocab=83001a46
-/
theorem decodeAux_long_list_short_length_rejected (fuel : Nat) (pfx : Byte)
    (rest rest' : List Byte) (lenVal : Nat)
    (hLong : 0xF7 < pfx.toNat)
    (hRead : readLength rest (pfx.toNat - 0xF7) = some (lenVal, rest'))
    (hShort : lenVal ≤ 55) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have hNotLongBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have hNotShortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  simp [decodeAux, hNotSingle, hNotShortBytes, hNotLongBytes, hNotShortList,
    hRead, hShort]

/--
@isnad1 id=eq.4h5v.s6.5493ed89f1b4 from=translated src=- shape=a3da6b29 vocab=bc9972b2
-/
theorem decodeAux_long_list_payload_none (fuel : Nat) (pfx : Byte)
    (rest rest' : List Byte) (lenVal : Nat)
    (hLong : 0xF7 < pfx.toNat)
    (hRead : readLength rest (pfx.toNat - 0xF7) = some (lenVal, rest'))
    (hLen : ¬ lenVal ≤ 55)
    (hTake : takeBytes rest' lenVal = none) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have hNotLongBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have hNotShortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  simp [decodeAux, hNotSingle, hNotShortBytes, hNotLongBytes, hNotShortList,
    hRead, hLen, hTake]

/--
@isnad1 id=eq.5h7v.s7.cb711735e563 from=translated src=- shape=fb28ecfd vocab=550ce68d
-/
theorem decodeAux_long_list_decode_none (fuel : Nat) (pfx : Byte)
    (rest rest' rest'' payload : List Byte) (lenVal : Nat)
    (hLong : 0xF7 < pfx.toNat)
    (hRead : readLength rest (pfx.toNat - 0xF7) = some (lenVal, rest'))
    (hLen : ¬ lenVal ≤ 55)
    (hTake : takeBytes rest' lenVal = some (payload, rest''))
    (hDecode : decodeItems fuel payload = none) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have hNotLongBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have hNotShortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  simp [decodeAux, hNotSingle, hNotShortBytes, hNotLongBytes, hNotShortList,
    hRead, hLen, hTake, hDecode]

/--
@isnad1 id=eq.6h9v.s7.9600072d75bc from=translated src=- shape=d8db5372 vocab=6da933e1
-/
theorem decodeAux_long_list_leftover_rejected (fuel : Nat) (pfx : Byte)
    (rest rest' rest'' payload leftover : List Byte) (items : List RLPItem)
    (lenVal : Nat)
    (hLong : 0xF7 < pfx.toNat)
    (hRead : readLength rest (pfx.toNat - 0xF7) = some (lenVal, rest'))
    (hLen : ¬ lenVal ≤ 55)
    (hTake : takeBytes rest' lenVal = some (payload, rest''))
    (hDecode : decodeItems fuel payload = some (items, leftover))
    (hLeftover : leftover ≠ []) :
    decodeAux (fuel + 1) (pfx :: rest) = none := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have hNotLongBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have hNotShortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  cases leftover with
  | nil => exact False.elim (hLeftover rfl)
  | cons b bs =>
      simp [decodeAux, hNotSingle, hNotShortBytes, hNotLongBytes,
        hNotShortList, hRead, hLen, hTake, hDecode]

/--
@isnad1 id=eq.5h8v.s7.53bf43de3415 from=translated src=- shape=4f91abf7 vocab=4c0d41dd
-/
theorem decodeAux_long_list_success (fuel : Nat) (pfx : Byte)
    (rest rest' rest'' payload : List Byte) (items : List RLPItem) (lenVal : Nat)
    (hLong : 0xF7 < pfx.toNat)
    (hRead : readLength rest (pfx.toNat - 0xF7) = some (lenVal, rest'))
    (hLen : ¬ lenVal ≤ 55)
    (hTake : takeBytes rest' lenVal = some (payload, rest''))
    (hDecode : decodeItems fuel payload = some (items, [])) :
    decodeAux (fuel + 1) (pfx :: rest) = some (.list items, rest'') := by
  have hNotSingle : ¬ pfx.toNat < 0x80 := by omega
  have hNotShortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have hNotLongBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have hNotShortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  simp [decodeAux, hNotSingle, hNotShortBytes, hNotLongBytes, hNotShortList,
    hRead, hLen, hTake, hDecode]

end EvmAsm.EL.RLP
