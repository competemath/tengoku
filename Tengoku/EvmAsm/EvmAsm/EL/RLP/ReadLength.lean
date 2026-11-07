/-
  EvmAsm.EL.RLP.ReadLength

  Branch lemmas for the executable RLP length decoder.
-/
module

public import Tengoku.EvmAsm.EvmAsm.EL.RLP.Decode

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

public section

namespace EvmAsm.EL.RLP

/-! ## readLength branch bridges -/

/--
@isnad1 id=eq.1h4v.s8.aa308d76a15c from=translated src=- shape=6d8b2c15 vocab=27f2b2ef
-/
theorem readLength_eq_of_takeBytes {bs lenBytes rest : List Byte} {n : Nat}
    (h : takeBytes bs n = some (lenBytes, rest)) :
    readLength bs n =
      match lenBytes with
      | [] => some (0, rest)
      | b :: _ =>
          if lenBytes.length > 1 && b == (0 : Byte) then none
          else some (Nat.fromBytesBE lenBytes, rest) := by
  cases lenBytes with
  | nil => simp [readLength, h]
  | cons b tail => simp [readLength, h]

/--
@isnad1 id=eq.1h2v.s5.4fcdb263e6b7 from=translated src=- shape=ecfa5f55 vocab=4e3664f0
-/
theorem readLength_none_of_takeBytes_none {bs : List Byte} {n : Nat}
    (h : takeBytes bs n = none) :
    readLength bs n = none := by
  simp [readLength, h]

/--
@isnad1 id=eq.1h3v.s5.430c4ad1a637 from=translated src=- shape=8e47ca54 vocab=1c416f56
-/
theorem readLength_some_of_takeBytes_nil {bs rest : List Byte} {n : Nat}
    (h : takeBytes bs n = some ([], rest)) :
    readLength bs n = some (0, rest) := by
  simp [readLength, h]

/--
@isnad1 id=eq.1h5v.s6.fddda4399eef from=translated src=- shape=5aaefb5b vocab=757c2315
-/
theorem readLength_none_of_takeBytes_leading_zero {bs rest tail : List Byte}
    {b : Byte} {n : Nat}
    (h : takeBytes bs n = some ((0 : Byte) :: b :: tail, rest)) :
    readLength bs n = none := by
  simp [readLength, h]

/--
@isnad1 id=eq.1h4v.s6.e95b7ed813bf from=translated src=- shape=7f62f742 vocab=252db778
-/
theorem readLength_some_of_takeBytes_single {bs rest : List Byte}
    {b : Byte} {n : Nat}
    (h : takeBytes bs n = some ([b], rest)) :
    readLength bs n = some (b.toNat, rest) := by
  simp [readLength, h, Nat.fromBytesBE]

/--
@isnad1 id=eq.2h5v.s6.c456fe9cf098 from=translated src=- shape=2a7edb3f vocab=8ab86c61
-/
theorem readLength_some_of_takeBytes_nonzero {bs rest tail : List Byte}
    {b : Byte} {n : Nat}
    (h : takeBytes bs n = some (b :: tail, rest))
    (hne : b ≠ (0 : Byte)) :
    readLength bs n = some (Nat.fromBytesBE (b :: tail), rest) := by
  cases tail with
  | nil => simp [readLength, h, Nat.fromBytesBE]
  | cons c tail =>
      have hb : ¬ b = (0#8 : Byte) := by
        intro hz
        exact hne hz
      simp [readLength, h, hb]

end EvmAsm.EL.RLP
