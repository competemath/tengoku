/-
  EvmAsm.EL.RLP.Prefix

  Pure RLP prefix-byte classifier. This is the semantic target for the
  RISC-V prefix-classifier phase of the executable decoder.
-/

module

public import Tengoku.EvmAsm.EvmAsm.EL.RLP.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace EvmAsm.EL.RLP

/-- The five Yellow Paper RLP prefix classes.-/
inductive PrefixClass where
  | singleByte
  | shortBytes
  | longBytes
  | shortList
  | longList
  deriving Repr, BEq, DecidableEq

/-- Classify an RLP prefix byte by its numeric range.-/
def classifyPrefix (pfx : Byte) : PrefixClass :=
  let p := pfx.toNat
  if p < 0x80 then .singleByte
  else if p ≤ 0xB7 then .shortBytes
  else if p ≤ 0xBF then .longBytes
  else if p ≤ 0xF7 then .shortList
  else .longList

/-- Payload length encoded directly in a short string prefix (`0x80..0xB7`).-/
def rlpPrefixShortBytesPayloadLen (pfx : Byte) : Nat :=
  pfx.toNat - 0x80

/-- Number of length bytes following a long string prefix (`0xB8..0xBF`).-/
def rlpPrefixLongBytesLenOfLen (pfx : Byte) : Nat :=
  pfx.toNat - 0xB7

/-- Payload length encoded directly in a short list prefix (`0xC0..0xF7`).-/
def rlpPrefixShortListPayloadLen (pfx : Byte) : Nat :=
  pfx.toNat - 0xC0

/-- Number of length bytes following a long list prefix (`0xF8..0xFF`).-/
def rlpPrefixLongListLenOfLen (pfx : Byte) : Nat :=
  pfx.toNat - 0xF7

/-!
Stated unfolding equations for the four payload-length defs. Use THESE in
`simp`/`rw`, not the def names: since v4.31, on-demand realization of a def's
unfolding lemma recurses ~4 stack frames per unit of a literal right subtrahend
(`- 0xF7` ≈ 1000 frames vs the hard 512 default), realizations are not exported
across modules, and no call-site `set_option maxRecDepth` reaches the
realization context — so `simp [rlpPrefixLongListLenOfLen]` in a downstream
module dies with `maximum recursion depth`. An ordinary `rfl` theorem sidesteps
realization entirely.
-/

/--
@isnad1 id=eq.0h1v.s4.2d5a372e14d7 from=translated src=- shape=6b646b13 vocab=f65ab344
-/
theorem rlpPrefixShortBytesPayloadLen_def (pfx : Byte) :
    rlpPrefixShortBytesPayloadLen pfx = pfx.toNat - 0x80 := rfl

/--
@isnad1 id=eq.0h1v.s4.f6422f9065ab from=translated src=- shape=6b646b13 vocab=2bba88a8
-/
theorem rlpPrefixLongBytesLenOfLen_def (pfx : Byte) :
    rlpPrefixLongBytesLenOfLen pfx = pfx.toNat - 0xB7 := rfl

/--
@isnad1 id=eq.0h1v.s4.20f233d42930 from=translated src=- shape=6b646b13 vocab=ede5d065
-/
theorem rlpPrefixShortListPayloadLen_def (pfx : Byte) :
    rlpPrefixShortListPayloadLen pfx = pfx.toNat - 0xC0 := rfl

/--
@isnad1 id=eq.0h1v.s4.a02007af520e from=translated src=- shape=6b646b13 vocab=f635e3e0
-/
theorem rlpPrefixLongListLenOfLen_def (pfx : Byte) :
    rlpPrefixLongListLenOfLen pfx = pfx.toNat - 0xF7 := rfl

/-- Total length-of-length byte count for an RLP prefix. Only long-form
    byte strings and lists carry an encoded payload length; all other
    prefixes have zero length bytes.-/
def rlpPrefixLenOfLen (pfx : Byte) : Nat :=
  match classifyPrefix pfx with
  | .longBytes => rlpPrefixLongBytesLenOfLen pfx
  | .longList => rlpPrefixLongListLenOfLen pfx
  | _ => 0

/-- Total header bytes before payload for a long string prefix. This includes
    the prefix byte plus the encoded length bytes.-/
def rlpPrefixLongBytesHeaderBytes (pfx : Byte) : Nat :=
  1 + rlpPrefixLongBytesLenOfLen pfx

/-- Total header bytes before payload for a long list prefix. This includes
    the prefix byte plus the encoded length bytes.-/
def rlpPrefixLongListHeaderBytes (pfx : Byte) : Nat :=
  1 + rlpPrefixLongListLenOfLen pfx

/-- Total header bytes before payload for any RLP prefix class. Single-byte
    payloads have no header byte before the payload.-/
def rlpPrefixHeaderBytes (pfx : Byte) : Nat :=
  match classifyPrefix pfx with
  | .singleByte => 0
  | .shortBytes => 1
  | .longBytes => rlpPrefixLongBytesHeaderBytes pfx
  | .shortList => 1
  | .longList => rlpPrefixLongListHeaderBytes pfx

/--
@isnad1 id=iff.0h1v.s4.5ce15468af4c from=translated src=- shape=c29482da vocab=5d74bfbe
-/
theorem classifyPrefix_singleByte_iff (pfx : Byte) :
    classifyPrefix pfx = .singleByte ↔ pfx.toNat < 0x80 := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0]
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega

/--
@isnad1 id=iff.0h1v.s5.255adadcc285 from=translated src=- shape=10b72027 vocab=e5026bce
-/
theorem classifyPrefix_shortBytes_iff (pfx : Byte) :
    classifyPrefix pfx = .shortBytes ↔ 0x80 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xB7 := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0] <;> omega
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega

/--
@isnad1 id=iff.0h1v.s5.7a5c03fc7930 from=translated src=- shape=10b72027 vocab=0fb8a9ce
-/
theorem classifyPrefix_longBytes_iff (pfx : Byte) :
    classifyPrefix pfx = .longBytes ↔ 0xB8 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xBF := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0] <;> omega
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega

/--
@isnad1 id=iff.0h1v.s5.09191f1d2055 from=translated src=- shape=10b72027 vocab=317ca415
-/
theorem classifyPrefix_shortList_iff (pfx : Byte) :
    classifyPrefix pfx = .shortList ↔ 0xC0 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xF7 := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0] <;> omega
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega

/--
@isnad1 id=iff.0h1v.s4.009352e365ce from=translated src=- shape=b6b840e4 vocab=9e7a82db
-/
theorem classifyPrefix_longList_iff (pfx : Byte) :
    classifyPrefix pfx = .longList ↔ 0xF8 ≤ pfx.toNat := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0] <;> omega
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega

/--
@isnad1 id=le.1h1v.s4.8d9407c473c7 from=translated src=- shape=b814d1b5 vocab=19d27668
-/
theorem rlpPrefixShortBytesPayloadLen_le_55_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .shortBytes) :
    rlpPrefixShortBytesPayloadLen pfx ≤ 55 := by
  rw [classifyPrefix_shortBytes_iff] at h
  unfold rlpPrefixShortBytesPayloadLen
  omega

/--
@isnad1 id=le.1h1v.s4.e096801c279c from=translated src=- shape=b814d1b5 vocab=38234ad9
-/
theorem rlpPrefixShortListPayloadLen_le_55_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .shortList) :
    rlpPrefixShortListPayloadLen pfx ≤ 55 := by
  rw [classifyPrefix_shortList_iff] at h
  unfold rlpPrefixShortListPayloadLen
  omega

/--
@isnad1 id=lt.1h1v.s4.c35f32fc64f9 from=translated src=- shape=779b4580 vocab=beefcab7
-/
theorem rlpPrefixLongBytesLenOfLen_pos_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longBytes) :
    0 < rlpPrefixLongBytesLenOfLen pfx := by
  rw [classifyPrefix_longBytes_iff] at h
  unfold rlpPrefixLongBytesLenOfLen
  omega

/--
@isnad1 id=le.1h1v.s4.42f6ed01bceb from=translated src=- shape=b814d1b5 vocab=60a5f24d
-/
theorem rlpPrefixLongBytesLenOfLen_le_8_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longBytes) :
    rlpPrefixLongBytesLenOfLen pfx ≤ 8 := by
  rw [classifyPrefix_longBytes_iff] at h
  unfold rlpPrefixLongBytesLenOfLen
  omega

/--
@isnad1 id=lt.1h1v.s4.298c08c2ff4e from=translated src=- shape=779b4580 vocab=49fe5bca
-/
theorem rlpPrefixLongListLenOfLen_pos_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longList) :
    0 < rlpPrefixLongListLenOfLen pfx := by
  rw [classifyPrefix_longList_iff] at h
  unfold rlpPrefixLongListLenOfLen
  omega

/--
@isnad1 id=le.1h1v.s4.4a1807c5d383 from=translated src=- shape=b814d1b5 vocab=a4756aa7
-/
theorem rlpPrefixLongListLenOfLen_le_8_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longList) :
    rlpPrefixLongListLenOfLen pfx ≤ 8 := by
  rw [classifyPrefix_longList_iff] at h
  unfold rlpPrefixLongListLenOfLen
  have h_bound : pfx.toNat < 256 := pfx.isLt
  omega

/--
@isnad1 id=eq.1h1v.s4.8fed74da34c5 from=translated src=- shape=e6b9d3ca vocab=d233240b
-/
theorem rlpPrefixLenOfLen_eq_zero_of_singleByte {pfx : Byte}
    (h : classifyPrefix pfx = .singleByte) :
    rlpPrefixLenOfLen pfx = 0 := by
  unfold rlpPrefixLenOfLen
  rw [h]

/--
@isnad1 id=eq.1h1v.s4.e474defc325c from=translated src=- shape=e6b9d3ca vocab=461ed4cc
-/
theorem rlpPrefixLenOfLen_eq_zero_of_shortBytes {pfx : Byte}
    (h : classifyPrefix pfx = .shortBytes) :
    rlpPrefixLenOfLen pfx = 0 := by
  unfold rlpPrefixLenOfLen
  rw [h]

/--
@isnad1 id=eq.1h1v.s3.1ed98adecc5a from=translated src=- shape=a45c35a6 vocab=5b05ac02
-/
theorem rlpPrefixLenOfLen_eq_longBytesLenOfLen {pfx : Byte}
    (h : classifyPrefix pfx = .longBytes) :
    rlpPrefixLenOfLen pfx = rlpPrefixLongBytesLenOfLen pfx := by
  unfold rlpPrefixLenOfLen
  rw [h]

/--
@isnad1 id=eq.1h1v.s4.fcf1b0d5708e from=translated src=- shape=e6b9d3ca vocab=d239438c
-/
theorem rlpPrefixLenOfLen_eq_zero_of_shortList {pfx : Byte}
    (h : classifyPrefix pfx = .shortList) :
    rlpPrefixLenOfLen pfx = 0 := by
  unfold rlpPrefixLenOfLen
  rw [h]

/--
@isnad1 id=eq.1h1v.s3.a329c557eda6 from=translated src=- shape=a45c35a6 vocab=8d3077a6
-/
theorem rlpPrefixLenOfLen_eq_longListLenOfLen {pfx : Byte}
    (h : classifyPrefix pfx = .longList) :
    rlpPrefixLenOfLen pfx = rlpPrefixLongListLenOfLen pfx := by
  unfold rlpPrefixLenOfLen
  rw [h]

/--
@isnad1 id=le.0h1v.s3.62537e5586a4 from=translated src=- shape=a311c14d vocab=f1e2bf33
-/
theorem rlpPrefixLenOfLen_le_8 (pfx : Byte) :
    rlpPrefixLenOfLen pfx ≤ 8 := by
  unfold rlpPrefixLenOfLen
  cases h : classifyPrefix pfx <;> simp
  · exact rlpPrefixLongBytesLenOfLen_le_8_of_class h
  · exact rlpPrefixLongListLenOfLen_le_8_of_class h

/--
@isnad1 id=iff.0h1v.s4.b881e4afeecb from=translated src=- shape=3d9b48c0 vocab=d8c6aad0
-/
theorem rlpPrefixLenOfLen_pos_iff_longClass (pfx : Byte) :
    0 < rlpPrefixLenOfLen pfx ↔
      classifyPrefix pfx = .longBytes ∨ classifyPrefix pfx = .longList := by
  constructor
  · intro h_pos
    cases h_class : classifyPrefix pfx
    · rw [rlpPrefixLenOfLen_eq_zero_of_singleByte h_class] at h_pos
      omega
    · rw [rlpPrefixLenOfLen_eq_zero_of_shortBytes h_class] at h_pos
      omega
    · exact Or.inl rfl
    · rw [rlpPrefixLenOfLen_eq_zero_of_shortList h_class] at h_pos
      omega
    · exact Or.inr rfl
  · intro h_long
    rcases h_long with h_longBytes | h_longList
    · rw [rlpPrefixLenOfLen_eq_longBytesLenOfLen h_longBytes]
      exact rlpPrefixLongBytesLenOfLen_pos_of_class h_longBytes
    · rw [rlpPrefixLenOfLen_eq_longListLenOfLen h_longList]
      exact rlpPrefixLongListLenOfLen_pos_of_class h_longList

/--
@isnad1 id=iff.0h1v.s5.8e26d770eeee from=translated src=- shape=914ecec5 vocab=f5bc3d33
-/
theorem rlpPrefixLenOfLen_pos_iff_long_ranges (pfx : Byte) :
    0 < rlpPrefixLenOfLen pfx ↔
      (0xB8 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xBF) ∨ 0xF8 ≤ pfx.toNat := by
  rw [rlpPrefixLenOfLen_pos_iff_longClass,
    classifyPrefix_longBytes_iff, classifyPrefix_longList_iff]

/--
@isnad1 id=lt.0h1v.s3.0f7463688167 from=translated src=- shape=b9369acb vocab=a7689b3d
-/
theorem rlpPrefixLongBytesHeaderBytes_pos (pfx : Byte) :
    0 < rlpPrefixLongBytesHeaderBytes pfx := by
  unfold rlpPrefixLongBytesHeaderBytes
  omega

/--
@isnad1 id=le.1h1v.s4.e64039fc9537 from=translated src=- shape=b814d1b5 vocab=0b89bace
-/
theorem rlpPrefixLongBytesHeaderBytes_le_9_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longBytes) :
    rlpPrefixLongBytesHeaderBytes pfx ≤ 9 := by
  unfold rlpPrefixLongBytesHeaderBytes
  have h_len := rlpPrefixLongBytesLenOfLen_le_8_of_class h
  omega

/--
@isnad1 id=eq.0h1v.s4.883f85dfde73 from=translated src=- shape=cd2b45a8 vocab=1aace835
-/
theorem rlpPrefixLongBytesHeaderBytes_eq_lenOfLen_add_one (pfx : Byte) :
    rlpPrefixLongBytesHeaderBytes pfx =
      rlpPrefixLongBytesLenOfLen pfx + 1 := by
  unfold rlpPrefixLongBytesHeaderBytes
  omega

/--
@isnad1 id=lt.0h1v.s3.86847ee4d340 from=translated src=- shape=b9369acb vocab=7dbc5c1b
-/
theorem rlpPrefixLongListHeaderBytes_pos (pfx : Byte) :
    0 < rlpPrefixLongListHeaderBytes pfx := by
  unfold rlpPrefixLongListHeaderBytes
  omega

/--
@isnad1 id=le.1h1v.s4.95751487d432 from=translated src=- shape=b814d1b5 vocab=7c5f380f
-/
theorem rlpPrefixLongListHeaderBytes_le_9_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longList) :
    rlpPrefixLongListHeaderBytes pfx ≤ 9 := by
  unfold rlpPrefixLongListHeaderBytes
  have h_len := rlpPrefixLongListLenOfLen_le_8_of_class h
  omega

/--
@isnad1 id=eq.0h1v.s4.be64135392fe from=translated src=- shape=cd2b45a8 vocab=cc6e93f1
-/
theorem rlpPrefixLongListHeaderBytes_eq_lenOfLen_add_one (pfx : Byte) :
    rlpPrefixLongListHeaderBytes pfx =
      rlpPrefixLongListLenOfLen pfx + 1 := by
  unfold rlpPrefixLongListHeaderBytes
  omega

/--
@isnad1 id=eq.1h1v.s4.84128e64d8a1 from=translated src=- shape=e6b9d3ca vocab=0c0b714c
-/
theorem rlpPrefixHeaderBytes_eq_zero_of_singleByte {pfx : Byte}
    (h : classifyPrefix pfx = .singleByte) :
    rlpPrefixHeaderBytes pfx = 0 := by
  unfold rlpPrefixHeaderBytes
  rw [h]

/--
@isnad1 id=eq.1h1v.s4.c7251b3d184e from=translated src=- shape=e6b9d3ca vocab=66453dca
-/
theorem rlpPrefixHeaderBytes_eq_one_of_shortBytes {pfx : Byte}
    (h : classifyPrefix pfx = .shortBytes) :
    rlpPrefixHeaderBytes pfx = 1 := by
  unfold rlpPrefixHeaderBytes
  rw [h]

/--
@isnad1 id=eq.1h1v.s3.3dca36d3c339 from=translated src=- shape=a45c35a6 vocab=ad1fd3fa
-/
theorem rlpPrefixHeaderBytes_eq_longBytesHeader_of_longBytes {pfx : Byte}
    (h : classifyPrefix pfx = .longBytes) :
    rlpPrefixHeaderBytes pfx = rlpPrefixLongBytesHeaderBytes pfx := by
  unfold rlpPrefixHeaderBytes
  rw [h]

/--
@isnad1 id=eq.1h1v.s4.ef9b635c713c from=translated src=- shape=e6b9d3ca vocab=285c2406
-/
theorem rlpPrefixHeaderBytes_eq_one_of_shortList {pfx : Byte}
    (h : classifyPrefix pfx = .shortList) :
    rlpPrefixHeaderBytes pfx = 1 := by
  unfold rlpPrefixHeaderBytes
  rw [h]

/--
@isnad1 id=eq.1h1v.s3.7d71fa85175c from=translated src=- shape=a45c35a6 vocab=ec7d5913
-/
theorem rlpPrefixHeaderBytes_eq_longListHeader_of_longList {pfx : Byte}
    (h : classifyPrefix pfx = .longList) :
    rlpPrefixHeaderBytes pfx = rlpPrefixLongListHeaderBytes pfx := by
  unfold rlpPrefixHeaderBytes
  rw [h]

/--
@isnad1 id=le.0h1v.s3.4b841afc9f5b from=translated src=- shape=a311c14d vocab=ac01a3ec
-/
theorem rlpPrefixHeaderBytes_le_9 (pfx : Byte) :
    rlpPrefixHeaderBytes pfx ≤ 9 := by
  unfold rlpPrefixHeaderBytes
  cases h : classifyPrefix pfx <;> simp
  · exact rlpPrefixLongBytesHeaderBytes_le_9_of_class h
  · exact rlpPrefixLongListHeaderBytes_le_9_of_class h

/--
@isnad1 id=lt.1h1v.s4.f086aa409e8b from=translated src=- shape=779b4580 vocab=e66093b3
-/
theorem rlpPrefixHeaderBytes_pos_of_shortBytes {pfx : Byte}
    (h : classifyPrefix pfx = .shortBytes) :
    0 < rlpPrefixHeaderBytes pfx := by
  rw [rlpPrefixHeaderBytes_eq_one_of_shortBytes h]
  omega

/--
@isnad1 id=lt.1h1v.s4.f567cdc69aa0 from=translated src=- shape=779b4580 vocab=2b1b3cc9
-/
theorem rlpPrefixHeaderBytes_pos_of_longBytes {pfx : Byte}
    (h : classifyPrefix pfx = .longBytes) :
    0 < rlpPrefixHeaderBytes pfx := by
  rw [rlpPrefixHeaderBytes_eq_longBytesHeader_of_longBytes h]
  exact rlpPrefixLongBytesHeaderBytes_pos pfx

/--
@isnad1 id=lt.1h1v.s4.841c08951904 from=translated src=- shape=779b4580 vocab=8dc5b346
-/
theorem rlpPrefixHeaderBytes_pos_of_shortList {pfx : Byte}
    (h : classifyPrefix pfx = .shortList) :
    0 < rlpPrefixHeaderBytes pfx := by
  rw [rlpPrefixHeaderBytes_eq_one_of_shortList h]
  omega

/--
@isnad1 id=lt.1h1v.s4.6f59b5ea4492 from=translated src=- shape=779b4580 vocab=778b6199
-/
theorem rlpPrefixHeaderBytes_pos_of_longList {pfx : Byte}
    (h : classifyPrefix pfx = .longList) :
    0 < rlpPrefixHeaderBytes pfx := by
  rw [rlpPrefixHeaderBytes_eq_longListHeader_of_longList h]
  exact rlpPrefixLongListHeaderBytes_pos pfx

/--
@isnad1 id=lt.1h1v.s4.defc42faee43 from=translated src=- shape=779b4580 vocab=edad91f5
-/
theorem rlpPrefixHeaderBytes_pos_of_not_singleByte {pfx : Byte}
    (h : classifyPrefix pfx ≠ .singleByte) :
    0 < rlpPrefixHeaderBytes pfx := by
  cases h_class : classifyPrefix pfx
  · contradiction
  · exact rlpPrefixHeaderBytes_pos_of_shortBytes h_class
  · exact rlpPrefixHeaderBytes_pos_of_longBytes h_class
  · exact rlpPrefixHeaderBytes_pos_of_shortList h_class
  · exact rlpPrefixHeaderBytes_pos_of_longList h_class

/--
@isnad1 id=iff.0h1v.s4.807fbb1ab2d8 from=translated src=- shape=49c34f90 vocab=0c0b714c
-/
theorem rlpPrefixHeaderBytes_eq_zero_iff_singleByte (pfx : Byte) :
    rlpPrefixHeaderBytes pfx = 0 ↔ classifyPrefix pfx = .singleByte := by
  constructor
  · intro h_zero
    cases h_class : classifyPrefix pfx
    · rfl
    · have h_pos := rlpPrefixHeaderBytes_pos_of_shortBytes h_class
      omega
    · have h_pos := rlpPrefixHeaderBytes_pos_of_longBytes h_class
      omega
    · have h_pos := rlpPrefixHeaderBytes_pos_of_shortList h_class
      omega
    · have h_pos := rlpPrefixHeaderBytes_pos_of_longList h_class
      omega
  · intro h
    exact rlpPrefixHeaderBytes_eq_zero_of_singleByte h

/--
@isnad1 id=iff.0h1v.s4.d1fde22bf920 from=translated src=- shape=8bf9dda8 vocab=2f710257
-/
theorem rlpPrefixHeaderBytes_eq_zero_iff_lt_0x80 (pfx : Byte) :
    rlpPrefixHeaderBytes pfx = 0 ↔ pfx.toNat < 0x80 := by
  rw [rlpPrefixHeaderBytes_eq_zero_iff_singleByte,
    classifyPrefix_singleByte_iff]

/--
@isnad1 id=iff.0h1v.s4.6ea279a34e67 from=translated src=- shape=34f07733 vocab=edad91f5
-/
theorem rlpPrefixHeaderBytes_pos_iff_not_singleByte (pfx : Byte) :
    0 < rlpPrefixHeaderBytes pfx ↔ classifyPrefix pfx ≠ .singleByte := by
  constructor
  · intro h_pos h_single
    rw [rlpPrefixHeaderBytes_eq_zero_of_singleByte h_single] at h_pos
    omega
  · intro h
    exact rlpPrefixHeaderBytes_pos_of_not_singleByte h

/--
@isnad1 id=iff.0h1v.s4.5e174d906035 from=translated src=- shape=5a1b1106 vocab=8cbcc05c
-/
theorem rlpPrefixHeaderBytes_pos_iff_ge_0x80 (pfx : Byte) :
    0 < rlpPrefixHeaderBytes pfx ↔ 0x80 ≤ pfx.toNat := by
  rw [rlpPrefixHeaderBytes_pos_iff_not_singleByte]
  constructor
  · intro h_not_single
    have h_not_lt : ¬ pfx.toNat < 0x80 := by
      intro h_lt
      exact h_not_single ((classifyPrefix_singleByte_iff pfx).mpr h_lt)
    omega
  · intro h_ge h_single
    have h_lt := (classifyPrefix_singleByte_iff pfx).mp h_single
    omega

/--
@isnad1 id=iff.0h1v.s4.200db2c0241b from=translated src=- shape=7502505b vocab=4a295089
-/
theorem rlpPrefixHeaderBytes_eq_one_iff_shortClass (pfx : Byte) :
    rlpPrefixHeaderBytes pfx = 1 ↔
      classifyPrefix pfx = .shortBytes ∨ classifyPrefix pfx = .shortList := by
  constructor
  · intro h_one
    cases h_class : classifyPrefix pfx
    · rw [rlpPrefixHeaderBytes_eq_zero_of_singleByte h_class] at h_one
      omega
    · exact Or.inl rfl
    · rw [rlpPrefixHeaderBytes_eq_longBytesHeader_of_longBytes h_class] at h_one
      have h_len := rlpPrefixLongBytesLenOfLen_pos_of_class h_class
      unfold rlpPrefixLongBytesHeaderBytes at h_one
      omega
    · exact Or.inr rfl
    · rw [rlpPrefixHeaderBytes_eq_longListHeader_of_longList h_class] at h_one
      have h_len := rlpPrefixLongListLenOfLen_pos_of_class h_class
      unfold rlpPrefixLongListHeaderBytes at h_one
      omega
  · intro h_short
    rcases h_short with h_shortBytes | h_shortList
    · exact rlpPrefixHeaderBytes_eq_one_of_shortBytes h_shortBytes
    · exact rlpPrefixHeaderBytes_eq_one_of_shortList h_shortList

/--
@isnad1 id=iff.0h1v.s6.79a78c48614a from=translated src=- shape=62c9bfea vocab=007d2111
-/
theorem rlpPrefixHeaderBytes_eq_one_iff_short_ranges (pfx : Byte) :
    rlpPrefixHeaderBytes pfx = 1 ↔
      (0x80 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xB7) ∨
      (0xC0 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xF7) := by
  rw [rlpPrefixHeaderBytes_eq_one_iff_shortClass,
    classifyPrefix_shortBytes_iff, classifyPrefix_shortList_iff]

/--
@isnad1 id=iff.0h1v.s6.3caf72eb7d72 from=translated src=- shape=af90d5ac vocab=8cbcc05c
-/
theorem rlpPrefixHeaderBytes_pos_and_le_one_iff_short_ranges (pfx : Byte) :
    0 < rlpPrefixHeaderBytes pfx ∧ rlpPrefixHeaderBytes pfx ≤ 1 ↔
      (0x80 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xB7) ∨
      (0xC0 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xF7) := by
  constructor
  · intro h
    exact (rlpPrefixHeaderBytes_eq_one_iff_short_ranges pfx).mp (by omega)
  · intro h_short
    have h_one := (rlpPrefixHeaderBytes_eq_one_iff_short_ranges pfx).mpr h_short
    omega

/--
@isnad1 id=iff.0h1v.s4.e5149d922f28 from=translated src=- shape=3d9b48c0 vocab=307c1cd9
-/
theorem rlpPrefixHeaderBytes_ge_two_iff_longClass (pfx : Byte) :
    2 ≤ rlpPrefixHeaderBytes pfx ↔
      classifyPrefix pfx = .longBytes ∨ classifyPrefix pfx = .longList := by
  constructor
  · intro h_two
    cases h_class : classifyPrefix pfx
    · rw [rlpPrefixHeaderBytes_eq_zero_of_singleByte h_class] at h_two
      omega
    · rw [rlpPrefixHeaderBytes_eq_one_of_shortBytes h_class] at h_two
      omega
    · exact Or.inl rfl
    · rw [rlpPrefixHeaderBytes_eq_one_of_shortList h_class] at h_two
      omega
    · exact Or.inr rfl
  · intro h_long
    rcases h_long with h_longBytes | h_longList
    · rw [rlpPrefixHeaderBytes_eq_longBytesHeader_of_longBytes h_longBytes]
      have h_len := rlpPrefixLongBytesLenOfLen_pos_of_class h_longBytes
      unfold rlpPrefixLongBytesHeaderBytes
      omega
    · rw [rlpPrefixHeaderBytes_eq_longListHeader_of_longList h_longList]
      have h_len := rlpPrefixLongListLenOfLen_pos_of_class h_longList
      unfold rlpPrefixLongListHeaderBytes
      omega

/--
@isnad1 id=iff.0h1v.s5.33feac8b607c from=translated src=- shape=757a0bd5 vocab=007d2111
-/
theorem rlpPrefixHeaderBytes_ge_two_iff_long_ranges (pfx : Byte) :
    2 ≤ rlpPrefixHeaderBytes pfx ↔
      (0xB8 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xBF) ∨
        0xF8 ≤ pfx.toNat := by
  rw [rlpPrefixHeaderBytes_ge_two_iff_longClass,
    classifyPrefix_longBytes_iff, classifyPrefix_longList_iff]

/--
@isnad1 id=iff.0h1v.s5.c7a151d4226f from=translated src=- shape=9c004c96 vocab=8cbcc05c
-/
theorem rlpPrefixHeaderBytes_lt_two_iff_non_long_ranges (pfx : Byte) :
    rlpPrefixHeaderBytes pfx < 2 ↔
      pfx.toNat < 0xB8 ∨
        (0xC0 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xF7) := by
  have h_bound : pfx.toNat < 256 := pfx.isLt
  constructor
  · intro h_lt
    have h_not_long_ranges :
        ¬ ((0xB8 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xBF) ∨
          0xF8 ≤ pfx.toNat) := by
      intro h_long_ranges
      have h_two :=
        (rlpPrefixHeaderBytes_ge_two_iff_long_ranges pfx).mpr h_long_ranges
      omega
    by_cases h_low : pfx.toNat < 0xB8
    · exact Or.inl h_low
    · right
      have h_not_long_bytes : ¬ (0xB8 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xBF) := by
        intro h_long_bytes
        exact h_not_long_ranges (Or.inl h_long_bytes)
      have h_not_long_list : ¬ 0xF8 ≤ pfx.toNat := by
        intro h_long_list
        exact h_not_long_ranges (Or.inr h_long_list)
      omega
  · intro h_non_long
    by_cases h_lt : rlpPrefixHeaderBytes pfx < 2
    · exact h_lt
    have h_two : 2 ≤ rlpPrefixHeaderBytes pfx := by omega
    have h_long_ranges :=
      (rlpPrefixHeaderBytes_ge_two_iff_long_ranges pfx).mp h_two
    rcases h_non_long with h_low | h_short_list
    · rcases h_long_ranges with h_long_bytes | h_long_list <;> omega
    · rcases h_long_ranges with h_long_bytes | h_long_list <;> omega

/--
@isnad1 id=iff.0h1v.s5.c72f959a0b2b from=translated src=- shape=b30dd8d6 vocab=8cbcc05c
-/
theorem rlpPrefixHeaderBytes_le_one_iff_non_long_ranges (pfx : Byte) :
    rlpPrefixHeaderBytes pfx ≤ 1 ↔
      pfx.toNat < 0xB8 ∨
        (0xC0 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xF7) := by
  constructor
  · intro h_le
    exact (rlpPrefixHeaderBytes_lt_two_iff_non_long_ranges pfx).mp (by omega)
  · intro h_non_long
    have h_lt :=
      (rlpPrefixHeaderBytes_lt_two_iff_non_long_ranges pfx).mpr h_non_long
    omega

/--
@isnad1 id=iff.0h1v.s6.30590e03a00a from=translated src=- shape=a720a275 vocab=8cbcc05c
-/
theorem rlpPrefixHeaderBytes_eq_zero_or_one_iff_non_long_ranges (pfx : Byte) :
    rlpPrefixHeaderBytes pfx = 0 ∨ rlpPrefixHeaderBytes pfx = 1 ↔
      pfx.toNat < 0xB8 ∨
        (0xC0 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xF7) := by
  rw [← rlpPrefixHeaderBytes_le_one_iff_non_long_ranges]
  constructor
  · intro h_zero_or_one
    rcases h_zero_or_one with h_zero | h_one <;> omega
  · intro h_le
    omega

/--
@isnad1 id=or.0h1v.s5.cc40834bf1ee from=translated src=- shape=d4a4c7f7 vocab=ac01a3ec
-/
theorem rlpPrefixHeaderBytes_eq_zero_or_one_or_ge_two (pfx : Byte) :
    rlpPrefixHeaderBytes pfx = 0 ∨
      rlpPrefixHeaderBytes pfx = 1 ∨
      2 ≤ rlpPrefixHeaderBytes pfx := by
  cases h_class : classifyPrefix pfx
  · exact Or.inl (rlpPrefixHeaderBytes_eq_zero_of_singleByte h_class)
  · exact Or.inr (Or.inl (rlpPrefixHeaderBytes_eq_one_of_shortBytes h_class))
  · exact Or.inr (Or.inr
      ((rlpPrefixHeaderBytes_ge_two_iff_longClass pfx).mpr (Or.inl h_class)))
  · exact Or.inr (Or.inl (rlpPrefixHeaderBytes_eq_one_of_shortList h_class))
  · exact Or.inr (Or.inr
      ((rlpPrefixHeaderBytes_ge_two_iff_longClass pfx).mpr (Or.inr h_class)))

end EvmAsm.EL.RLP
