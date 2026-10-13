/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.ListDecoding.Family.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.ListDecoding.Family.Internal

/-!
# Uniform families of finite Boolean list codes

This layer states the semantic, parameter-size, and uniform machine obligations
of the efficiently list-decodable code used in Hirahara's reconstruction. It
also turns inverse-accuracy agreement into an actual fixed-width decoder index.
-/

public section

namespace Complexity

namespace BooleanListCodeFamily

/-- A Boolean-cube truth table has exactly `2^coordinateLength` bits.
@isnad1 id=eq.0h2v.s5.eedd1d0f842e from=translated src=- shape=6c03b897 vocab=434fc2c2
-/
@[simp] theorem length_truthTableBits {coordinateLength : ℕ}
    (word : (Fin coordinateLength → Bool) → Bool) :
    (truthTableBits word).length = 2 ^ coordinateLength :=
  length_truthTableBits_internal word

/-- A family encoder emits the complete truth table of its codeword.
@isnad1 id=eq.0h4v.s5.ec4482d4c52f from=translated src=- shape=c34d70cb vocab=17713980
-/
@[simp] theorem length_encoderOutput (family : BooleanListCodeFamily)
    (messageLength inverseAccuracy : ℕ)
    (message : Fin messageLength → Bool) :
    (family.encoderOutput messageLength inverseAccuracy message).length =
      2 ^ family.coordinateLength messageLength inverseAccuracy :=
  length_encoderOutput_internal family messageLength inverseAccuracy message

/-- The full decoder output concatenates exactly `listSize` messages of the
original message length.
@isnad1 id=eq.0h4v.s5.2343085cae3f from=translated src=- shape=ee44b25c vocab=f987f2c1
-/
@[simp] theorem length_decoderOutput (family : BooleanListCodeFamily)
    (messageLength inverseAccuracy : ℕ)
    (received :
      (Fin (family.coordinateLength messageLength inverseAccuracy) → Bool) →
        Bool) :
    (family.decoderOutput messageLength inverseAccuracy received).length =
      family.listSize messageLength inverseAccuracy * messageLength :=
  length_decoderOutput_internal family messageLength inverseAccuracy received

/-- Inverse-accuracy list decoding turns `1/2 + 1/q` agreement into a real
fixed-width string selecting the original message.
@isnad1 id=ex.3h5v.s7.8afd4c84f66d from=translated src=- shape=bdebb222 vocab=f4c14de1
-/
theorem exists_indexBits_of_half_add_inverseAccuracy
    (family : BooleanListCodeFamily)
    (hfamily : family.IsListDecodableAtInverseAccuracy)
    {messageLength inverseAccuracy : ℕ} (haccuracy : 2 ≤ inverseAccuracy)
    (message : Fin messageLength → Bool)
    (received :
      (Fin (family.coordinateLength messageLength inverseAccuracy) → Bool) →
        Bool)
    (hagreement : 1 / 2 + 1 / (inverseAccuracy : ℚ) ≤
      BooleanListCode.agreementProbability
        ((family.code messageLength inverseAccuracy).encode message) received) :
    ∃ bits : List Bool,
      bits.length = BooleanListCode.decoderIndexBitWidth
          (family.listSize messageLength inverseAccuracy) ∧
        (family.code messageLength inverseAccuracy).decodeAtIndexBits?
          received bits = some message :=
  exists_indexBits_of_half_add_inverseAccuracy_internal
    family hfamily haccuracy message received hagreement

/-- Polynomial list size gives a concrete ceiling-logarithmic upper bound on
the selecting decoder-index width.
@isnad1 id=le.0h4v.s5.0d4efd502fe7 from=translated src=- shape=10111f5f vocab=9252183f
-/
theorem decoderIndexBitWidth_le_polynomialBound
    {family : BooleanListCodeFamily}
    (bounds : family.PolynomialParameterBounds)
    (messageLength inverseAccuracy : ℕ) :
    BooleanListCode.decoderIndexBitWidth
        (family.listSize messageLength inverseAccuracy) ≤
      Nat.clog 2
        (bounds.listConstant * (inverseAccuracy + 1) ^ bounds.listDegree) :=
  decoderIndexBitWidth_le_polynomialBound_internal
    bounds messageLength inverseAccuracy

/-- Polynomial parameter bounds control the actual encoder output string.
@isnad1 id=le.0h5v.s6.501904e3b2f2 from=translated src=- shape=6eed98c8 vocab=4c1de594
-/
theorem length_encoderOutput_le
    {family : BooleanListCodeFamily}
    (bounds : family.PolynomialParameterBounds)
    (messageLength inverseAccuracy : ℕ)
    (message : Fin messageLength → Bool) :
    (family.encoderOutput messageLength inverseAccuracy message).length ≤
      bounds.codewordConstant *
        (messageLength + inverseAccuracy + 1) ^ bounds.codewordDegree :=
  length_encoderOutput_le_internal
    bounds messageLength inverseAccuracy message

/-- Polynomial list-size bounds control the actual concatenated decoder
output.
@isnad1 id=le.0h5v.s6.b00fdb0c68bb from=translated src=- shape=0bc4ad38 vocab=f4c8237b
-/
theorem length_decoderOutput_le
    {family : BooleanListCodeFamily}
    (bounds : family.PolynomialParameterBounds)
    (messageLength inverseAccuracy : ℕ)
    (received :
      (Fin (family.coordinateLength messageLength inverseAccuracy) → Bool) →
        Bool) :
    (family.decoderOutput messageLength inverseAccuracy received).length ≤
      (bounds.listConstant *
        (inverseAccuracy + 1) ^ bounds.listDegree) * messageLength :=
  length_decoderOutput_le_internal
    bounds messageLength inverseAccuracy received

/-- The uniform encoder machine produces the exact family codeword within its
advertised common polynomial bound.
@isnad1 id=and.0h5v.s6.064f4d155301 from=translated src=- shape=c2eb6afa vocab=8e97f561
-/
theorem UniformPolynomialTimeRealization.encoder_spec
    {family : BooleanListCodeFamily}
    (realization : family.UniformPolynomialTimeRealization)
    (messageLength inverseAccuracy : ℕ)
    (message : Fin messageLength → Bool) :
    realization.encoderMachine.ProducesInTime
        (encoderInput messageLength inverseAccuracy message)
        (family.encoderOutput messageLength inverseAccuracy message)
        (realization.encoderTime messageLength inverseAccuracy) ∧
      realization.encoderTime messageLength inverseAccuracy ≤
        realization.timeConstant *
          (messageLength + inverseAccuracy + 1) ^ realization.timeDegree :=
  realization.encoder_spec_internal messageLength inverseAccuracy message

/-- The single uniform decoder machine emits the exact concatenated candidate
list within the same kind of polynomial bound.
@isnad1 id=and.0h5v.s6.066c2021114c from=translated src=- shape=fc1fb70b vocab=b473c5bc
-/
theorem UniformPolynomialTimeRealization.decoder_spec
    {family : BooleanListCodeFamily}
    (realization : family.UniformPolynomialTimeRealization)
    (messageLength inverseAccuracy : ℕ)
    (received :
      (Fin (family.coordinateLength messageLength inverseAccuracy) → Bool) →
        Bool) :
    realization.decoderMachine.ProducesInTime
        (family.decoderInput messageLength inverseAccuracy received)
        (family.decoderOutput messageLength inverseAccuracy received)
        (realization.decoderTime messageLength inverseAccuracy) ∧
      realization.decoderTime messageLength inverseAccuracy ≤
        realization.timeConstant *
          (messageLength + inverseAccuracy + 1) ^ realization.timeDegree :=
  realization.decoder_spec_internal messageLength inverseAccuracy received

end BooleanListCodeFamily

end Complexity
