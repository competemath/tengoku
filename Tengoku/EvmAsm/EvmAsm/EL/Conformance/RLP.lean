/-
  EvmAsm.EL.Conformance.RLP

  Compact Lean-side conformance vectors for the executable RLP decoder
  (GH #125 / GH #120).
-/

module

public import Tengoku.EvmAsm.EvmAsm.EL.Conformance
public import Tengoku.EvmAsm.EvmAsm.EL.RLP.Decode

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace EvmAsm.EL
namespace Conformance
namespace RLP

abbrev Byte := EvmAsm.EL.RLP.Byte
abbrev RLPItem := EvmAsm.EL.RLP.RLPItem

/-- Input shape for an RLP decode executable-helper conformance vector.-/
structure DecodeInput where
  bytes : List Byte
  deriving Repr

/-- Decode exactly one RLP item and reject leftover bytes.-/
def runDecodeFully (input : DecodeInput) : Option RLPItem :=
  match EvmAsm.EL.RLP.decode input.bytes with
  | some (item, []) => some item
  | _ => none

/-- Nested list decode vector, covering recursive item decoding.
    Distinctive token: rlpNestedListDecodeVector.-/
def rlpNestedListDecodeVector : TestVector DecodeInput RLPItem :=
  { id := "rlp-nested-list-decode"
    input := { bytes := [(0xc3 : Byte), 0x01, 0x02, 0x03] }
    expected := .value (.list [.bytes [0x01], .bytes [0x02], .bytes [0x03]]) }

/-- Non-canonical singleton byte string must be rejected; `0x01` should be
    encoded directly as the single byte `0x01`, not as `0x81 0x01`.-/
def rlpNoncanonicalSingletonVector : TestVector DecodeInput RLPItem :=
  { id := "rlp-noncanonical-singleton"
    input := { bytes := [(0x81 : Byte), 0x01] }
    expected := .error "noncanonical-singleton" }

/-- Empty-list decoding covers the canonical `0xc0` list prefix.
    Distinctive token: RLP.rlpEmptyListDecodeVector #120 #125.-/
def rlpEmptyListDecodeVector : TestVector DecodeInput RLPItem :=
  { id := "rlp-empty-list-decode"
    input := { bytes := [(0xc0 : Byte)] }
    expected := .value (.list []) }

/-- Long-form byte string at the first canonical long-byte boundary.
    Distinctive token: RLP.rlpLongBytesDecodeVector #120 #125.-/
def rlpLongBytesDecodeVector : TestVector DecodeInput RLPItem :=
  { id := "rlp-long-bytes-decode"
    input := { bytes := (0xb8 : Byte) :: 0x38 :: List.replicate 56 (0x7f : Byte) }
    expected := .value (.bytes (List.replicate 56 (0x7f : Byte))) }

/--
@isnad1 id=eq.0h0v.s6.d99588e13cbd from=translated src=- shape=c02ac64a vocab=bb1e83ae
-/
theorem runDecodeFully_nestedList :
    runDecodeFully { bytes := [(0xc3 : Byte), 0x01, 0x02, 0x03] } =
      some (.list [.bytes [0x01], .bytes [0x02], .bytes [0x03]]) := rfl

/--
@isnad1 id=eq.0h0v.s5.3277e42b5bc6 from=translated src=- shape=049f840a vocab=0d0597c4
-/
theorem runDecodeFully_reject_noncanonical_singleton :
    runDecodeFully { bytes := [(0x81 : Byte), 0x01] } = none := rfl

/--
@isnad1 id=eq.0h0v.s4.533c31875055 from=translated src=- shape=c115bf46 vocab=71bb7882
-/
theorem runDecodeFully_emptyList :
    runDecodeFully { bytes := [(0xc0 : Byte)] } = some (.list []) := rfl

/--
@isnad1 id=eq.0h0v.s6.516404dfc1a4 from=translated src=- shape=cb1cbec2 vocab=ffe8a357
-/
theorem runDecodeFully_longBytes :
    runDecodeFully
      { bytes := (0xb8 : Byte) :: 0x38 :: List.replicate 56 (0x7f : Byte) } =
      some (.bytes (List.replicate 56 (0x7f : Byte))) := by
  rfl

/--
@isnad1 id=eq.0h0v.s3.09daa0787da5 from=translated src=- shape=dac26ef9 vocab=c767e65a
-/
theorem rlpNestedListDecodeVector_passed :
    checkVector? runDecodeFully rlpNestedListDecodeVector = .passed :=
  checkVector?_some_passed runDecodeFully
    "rlp-nested-list-decode"
    { bytes := [(0xc3 : Byte), 0x01, 0x02, 0x03] }
    (.list [.bytes [0x01], .bytes [0x02], .bytes [0x03]])
    runDecodeFully_nestedList

/--
@isnad1 id=eq.0h0v.s3.cb2511b25980 from=translated src=- shape=234b83e5 vocab=9805960e
-/
theorem rlpNoncanonicalSingletonVector_errored :
    checkVector? runDecodeFully rlpNoncanonicalSingletonVector =
      .errored "rlp-noncanonical-singleton" "noncanonical-singleton" :=
  checkVector?_none_error runDecodeFully
    "rlp-noncanonical-singleton"
    "noncanonical-singleton"
    { bytes := [(0x81 : Byte), 0x01] }
    runDecodeFully_reject_noncanonical_singleton

/--
@isnad1 id=eq.0h0v.s3.5ef1e7975a98 from=translated src=- shape=dac26ef9 vocab=b389d2dc
-/
theorem rlpEmptyListDecodeVector_passed :
    checkVector? runDecodeFully rlpEmptyListDecodeVector = .passed :=
  checkVector?_some_passed runDecodeFully
    "rlp-empty-list-decode"
    { bytes := [(0xc0 : Byte)] }
    (.list [])
    runDecodeFully_emptyList

/--
@isnad1 id=eq.0h0v.s3.61aee8d6619e from=translated src=- shape=dac26ef9 vocab=1b1827d0
-/
theorem rlpLongBytesDecodeVector_passed :
    checkVector? runDecodeFully rlpLongBytesDecodeVector = .passed :=
  checkVector?_some_passed runDecodeFully
    "rlp-long-bytes-decode"
    { bytes := (0xb8 : Byte) :: 0x38 :: List.replicate 56 (0x7f : Byte) }
    (.bytes (List.replicate 56 (0x7f : Byte)))
    runDecodeFully_longBytes

/-- Vector IDs for RLP executable-decoding conformance coverage.
    Distinctive token: rlpConformanceVectorIds #125 #120.-/
def rlpConformanceVectorIds : List String :=
  [ rlpNestedListDecodeVector.id
  , rlpNoncanonicalSingletonVector.id
  , rlpEmptyListDecodeVector.id
  , rlpLongBytesDecodeVector.id
  ]

/--
@isnad1 id=eq.0h0v.s4.b2e6b48a955f from=translated src=- shape=9ae00bbb vocab=bd2b21c7
-/
theorem rlpConformanceVectorIds_eq :
    rlpConformanceVectorIds =
      [ "rlp-nested-list-decode"
      , "rlp-noncanonical-singleton"
      , "rlp-empty-list-decode"
      , "rlp-long-bytes-decode"
      ] := rfl

/--
@isnad1 id=eq.0h0v.s3.d383f6df4fa5 from=translated src=- shape=b3c4969c vocab=f56e25e6
-/
theorem rlpConformanceVectorIds_length :
    rlpConformanceVectorIds.length = 4 := rfl

/--
@isnad1 id=nodup.0h0v.s1.72482feebdc5 from=translated src=- shape=25b03439 vocab=b4b5f8a2
-/
theorem rlpConformanceVectorIds_nodup :
    rlpConformanceVectorIds.Nodup := by
  decide

/-- Compact checked-vector batch for RLP executable decoding.
    Distinctive token: RLP.rlpConformanceVectors #125 #120.-/
def rlpConformanceVectors : List CheckResult :=
  [ checkVector? runDecodeFully rlpNestedListDecodeVector
  , checkVector? runDecodeFully rlpNoncanonicalSingletonVector
  , checkVector? runDecodeFully rlpEmptyListDecodeVector
  , checkVector? runDecodeFully rlpLongBytesDecodeVector
  ]

/--
@isnad1 id=eq.0h0v.s4.3530d2b2c8c0 from=translated src=- shape=ba498037 vocab=998914cb
-/
theorem rlpConformanceVectors_passed :
    rlpConformanceVectors =
      [ .passed
      , .errored "rlp-noncanonical-singleton" "noncanonical-singleton"
      , .passed
      , .passed
      ] := by
  simp [rlpConformanceVectors, rlpNestedListDecodeVector_passed,
    rlpNoncanonicalSingletonVector_errored, rlpEmptyListDecodeVector_passed,
    rlpLongBytesDecodeVector_passed]

end RLP
end Conformance
end EvmAsm.EL
