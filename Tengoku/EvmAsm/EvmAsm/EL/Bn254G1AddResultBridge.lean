/-
  EvmAsm.EL.Bn254G1AddResultBridge

  Bridge from the zkVM `zkvm_bn254_g1_add` accelerator output buffer (a single
  64-byte `zkvm_bn254_g1_point` written through the `result` pointer) to the
  byte-list view consumed by EL precompile return-data assembly. Mirrors the
  SHA256/RIPEMD160 result-bridge skeleton; we do NOT compute a stack word
  here because the BN254 G1 point is 64 bytes (does not fit into one EVM
  stack word) — precompile-output framing is left to a downstream slice.
-/

module

public import Tengoku.EvmAsm.EvmAsm.EL.WorldState

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace EvmAsm.EL

namespace Bn254G1AddResultBridge

/-- The 64-byte BN254 G1 point payload (`zkvm_bn254_g1_point`).-/
abbrev PointBytes := Fin 64 → Byte

/-- Accelerator output payload for `zkvm_bn254_g1_add`.-/
structure AcceleratorOutput where
  result : PointBytes

/-- Materialise the output point as a byte list (length 64).-/
def pointBytesList (point : PointBytes) : List Byte :=
  List.ofFn point

/-- Distinctive token: Bn254G1AddResultBridge.outputBytesList.-/
def outputBytesList (output : AcceleratorOutput) : List Byte :=
  pointBytesList output.result

/--
@isnad1 id=eq.0h1v.s3.f344b17ae7c7 from=translated src=- shape=8e1bdd70 vocab=06cc5b5c
-/
theorem pointBytesList_length (point : PointBytes) :
    (pointBytesList point).length = 64 := by
  simp [pointBytesList]

/--
@isnad1 id=eq.0h1v.s3.cbe821b62f12 from=translated src=- shape=8e1bdd70 vocab=9da8827a
-/
theorem outputBytesList_length (output : AcceleratorOutput) :
    (outputBytesList output).length = 64 := by
  simp [outputBytesList, pointBytesList_length]

/--
@isnad1 id=eq.0h1v.s3.66b40133df1b from=translated src=- shape=38bf8af6 vocab=3f11ec4f
-/
theorem outputBytesList_eq (output : AcceleratorOutput) :
    outputBytesList output = pointBytesList output.result := rfl

end Bn254G1AddResultBridge

end EvmAsm.EL
