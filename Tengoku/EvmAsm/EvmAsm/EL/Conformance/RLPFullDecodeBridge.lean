/-
  EvmAsm.EL.Conformance.RLPFullDecodeBridge

  Bridge the RLP conformance runner to the reusable top-level RLP full-decode
  wrapper (GH #125 / GH #120).
-/

module

public import Tengoku.EvmAsm.EvmAsm.EL.Conformance.RLP
public import Tengoku.EvmAsm.EvmAsm.EL.RLP.FullDecode

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

public section

namespace EvmAsm.EL
namespace Conformance
namespace RLPConformanceFullDecodeBridge

/--
The RLP conformance runner is exactly the reusable full-input decode wrapper
applied to the input bytes.

Distinctive token: RLPConformanceFullDecodeBridge.runDecodeFully_eq_decodeFully #125 #120.
@isnad1 id=eq.0h1v.s3.6dd612b7bb3d from=translated src=- shape=38bf8af6 vocab=2c02a54f
-/
theorem runDecodeFully_eq_decodeFully (input : RLP.DecodeInput) :
    RLP.runDecodeFully input = EvmAsm.EL.RLP.decodeFully input.bytes := by
  unfold RLP.runDecodeFully EvmAsm.EL.RLP.decodeFully
  rfl

/--
@isnad1 id=iff.0h2v.s5.040604b586c7 from=translated src=- shape=b0c1abbd vocab=019e9329
-/
theorem runDecodeFully_eq_some_iff
    (input : RLP.DecodeInput) (item : RLP.RLPItem) :
    RLP.runDecodeFully input = some item ↔
      EvmAsm.EL.RLP.decode input.bytes = some (item, []) := by
  rw [runDecodeFully_eq_decodeFully]
  exact EvmAsm.EL.RLP.decodeFully_eq_some_iff input.bytes item

/--
@isnad1 id=eq.0h1v.s4.4d18ff54f94f from=translated src=- shape=cef51f9b vocab=ae65ebae
-/
theorem checkVector?_runDecodeFully_eq_decodeFully
    (vector : TestVector RLP.DecodeInput RLP.RLPItem) :
    checkVector? RLP.runDecodeFully vector =
      checkVector? (fun input => EvmAsm.EL.RLP.decodeFully input.bytes) vector := by
  cases vector with
  | mk id input expected =>
      cases expected <;> simp [checkVector?, runDecodeFully_eq_decodeFully]

/--
@isnad1 id=eq.0h0v.s3.dca62d7e9cec from=translated src=- shape=52c57e5d vocab=31153f14
-/
theorem rlpNestedListDecodeVector_passed_via_decodeFully :
    checkVector? (fun input => EvmAsm.EL.RLP.decodeFully input.bytes)
        RLP.rlpNestedListDecodeVector = .passed := by
  rw [← checkVector?_runDecodeFully_eq_decodeFully]
  exact RLP.rlpNestedListDecodeVector_passed

/--
@isnad1 id=eq.0h0v.s3.bdad5b5184d5 from=translated src=- shape=8a8e352c vocab=053a1715
-/
theorem rlpNoncanonicalSingletonVector_errored_via_decodeFully :
    checkVector? (fun input => EvmAsm.EL.RLP.decodeFully input.bytes)
        RLP.rlpNoncanonicalSingletonVector =
      .errored "rlp-noncanonical-singleton" "noncanonical-singleton" := by
  rw [← checkVector?_runDecodeFully_eq_decodeFully]
  exact RLP.rlpNoncanonicalSingletonVector_errored

/--
@isnad1 id=eq.0h0v.s3.7b147e9eb656 from=translated src=- shape=52c57e5d vocab=357dc5cf
-/
theorem rlpLongBytesDecodeVector_passed_via_decodeFully :
    checkVector? (fun input => EvmAsm.EL.RLP.decodeFully input.bytes)
        RLP.rlpLongBytesDecodeVector = .passed := by
  rw [← checkVector?_runDecodeFully_eq_decodeFully]
  exact RLP.rlpLongBytesDecodeVector_passed

/--
Bridge the empty-list RLP decode conformance vector through the reusable
top-level full-decode wrapper, mirroring the nested-list and
noncanonical-singleton bridges above.

Distinctive token: rlpEmptyListDecodeVector_passed_via_decodeFully #120 #125.
@isnad1 id=eq.0h0v.s3.1d0557d1ddae from=translated src=- shape=52c57e5d vocab=42b20f6c
-/
theorem rlpEmptyListDecodeVector_passed_via_decodeFully :
    checkVector? (fun input => EvmAsm.EL.RLP.decodeFully input.bytes)
        RLP.rlpEmptyListDecodeVector = .passed := by
  rw [← checkVector?_runDecodeFully_eq_decodeFully]
  exact RLP.rlpEmptyListDecodeVector_passed

end RLPConformanceFullDecodeBridge
end Conformance
end EvmAsm.EL
