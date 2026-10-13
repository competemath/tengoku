/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Encoding.Defs

/-!
# Canonical encodings of Nisan--Wigderson designs -- proof internals
-/

public section

namespace Complexity

namespace NWDesign

/--
@isnad1 id=eq.0h4v.s5.105c8027e465 from=translated src=- shape=7b47dab5 vocab=5598aea9
-/
theorem length_encode_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength) :
    design.encode.length =
      outputLength * inputLength * Fin.bitWidth seedLength := by
  simp [encode]

/--
@isnad1 id=eq.0h6v.s5.6e9301c06105 from=translated src=- shape=4d74bdaf vocab=ed4b6dc7
-/
theorem decodeCoordinate?_encode_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) (input : Fin inputLength) :
    decodeCoordinate? outputLength inputLength seedLength design.encode
        output input =
      some (design.coordinates output input) := by
  simp [decodeCoordinate?, encode, coordinateBitTable]
  rw [← Fin.fromBits?_toBits (design.coordinates output input)]
  congr 1
  apply List.ext_get
  · simp
  · intro bit hfirst hsecond
    simp

/--
@isnad1 id=eq.1h6v.s6.075aa9baf75c from=translated src=- shape=3022ff55 vocab=a106f60f
-/
theorem decodedCoordinates_encode_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hvalid : ∀ output input,
      (decodeCoordinate? outputLength inputLength seedLength design.encode
        output input).isSome)
    (output : Fin outputLength) (input : Fin inputLength) :
    decodedCoordinates outputLength inputLength seedLength design.encode
        hvalid output input =
      design.coordinates output input := by
  simp [decodedCoordinates, decodeCoordinate?_encode_internal]

/--
@isnad1 id=eq.0h4v.s5.27a9233fc4c8 from=translated src=- shape=0b709110 vocab=1769042c
-/
theorem decode?_encode_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength) :
    decode? outputLength inputLength seedLength design.encode = some design := by
  have hvalid : ∀ output input,
      (decodeCoordinate? outputLength inputLength seedLength design.encode
        output input).isSome := by
    intro output input
    simp [decodeCoordinate?_encode_internal]
  have hinjective : ∀ output, Function.Injective
      (decodedCoordinates outputLength inputLength seedLength design.encode
        hvalid output) := by
    intro output first second heq
    have hfirst :=
      decodedCoordinates_encode_internal design hvalid output first
    have hsecond :=
      decodedCoordinates_encode_internal design hvalid output second
    rw [hfirst, hsecond] at heq
    exact (design.coordinates output).injective heq
  unfold decode?
  rw [dite_eq_left (length_encode_internal design), dite_eq_left hvalid,
    dite_eq_left hinjective]
  congr 1
  cases design with
  | mk coordinates =>
      congr 1
      funext output
      apply Function.Embedding.ext
      intro input
      apply decodedCoordinates_encode_internal

/--
@isnad1 id=eq.1h4v.s5.374e0ecac6b6 from=translated src=- shape=1dd04554 vocab=80588980
-/
theorem decode?_eq_none_of_length_ne_internal
    (outputLength inputLength seedLength : ℕ) (bits : List Bool)
    (hlength : bits.length ≠
      outputLength * inputLength * Fin.bitWidth seedLength) :
    decode? outputLength inputLength seedLength bits = none := by
  simp [decode?, hlength]

/--
@isnad1 id=eq.1h5v.s5.76f189ebd12d from=translated src=- shape=f7bf7353 vocab=ab23c28e
-/
theorem encode_eq_of_decode?_eq_some_internal
    {outputLength inputLength seedLength : ℕ} (bits : List Bool)
    (design : NWDesign outputLength inputLength seedLength)
    (hdecode : decode? outputLength inputLength seedLength bits = some design) :
    design.encode = bits := by
  unfold decode? at hdecode
  split at hdecode
  · rename_i hlength
    split at hdecode
    · rename_i hvalid
      dsimp only at hdecode
      split at hdecode
      · rename_i hinjective
        cases hdecode
        apply List.ext_get
        · rw [length_encode_internal, hlength]
        · intro position hencoded hbits
          let flatPosition : Fin
              (outputLength * inputLength * Fin.bitWidth seedLength) :=
            ⟨position, by rw [← hlength]; exact hbits⟩
          let index :=
            (coordinateBitIndexEquiv outputLength inputLength seedLength).symm
              flatPosition
          have hcoordinate :
              decodeCoordinate? outputLength inputLength seedLength bits
                  index.1.1 index.1.2 =
                some ((decodeCoordinate? outputLength inputLength seedLength bits
                  index.1.1 index.1.2).get (hvalid index.1.1 index.1.2)) :=
            (Option.some_get (hvalid index.1.1 index.1.2)).symm
          simp only [decodeCoordinate?, dite_eq_left hlength] at hcoordinate
          have hcoordinateBits :=
            Fin.toBits_eq_of_fromBits?_eq_some hcoordinate
          simp [encode, coordinateBitTable, decodedCoordinates]
          simp only [decodeCoordinate?, dite_eq_left hlength]
          have hbit := congrArg (fun coordinateBits : List Bool =>
            coordinateBits[index.2.val]?) hcoordinateBits
          simp [index, flatPosition] at hbit
          exact hbit
      · simp at hdecode
    · simp at hdecode
  · simp at hdecode

/--
@isnad1 id=iff.0h5v.s5.ccda5ebfdc94 from=translated src=- shape=82fb6e9a vocab=ab23c28e
-/
theorem decode?_eq_some_iff_internal
    {outputLength inputLength seedLength : ℕ} (bits : List Bool)
    (design : NWDesign outputLength inputLength seedLength) :
    decode? outputLength inputLength seedLength bits = some design ↔
      bits = design.encode := by
  constructor
  · intro hdecode
    exact (encode_eq_of_decode?_eq_some_internal bits design hdecode).symm
  · rintro rfl
    exact decode?_encode_internal design

/--
@isnad1 id=injectiv.0h3v.s4.a569e2baf84a from=translated src=- shape=0d8832f4 vocab=8d4cca1d
-/
theorem encode_injective_internal
    {outputLength inputLength seedLength : ℕ} :
    Function.Injective
      (encode : NWDesign outputLength inputLength seedLength → List Bool) := by
  intro first second hencode
  have hdecode := congrArg
    (decode? outputLength inputLength seedLength) hencode
  simpa only [decode?_encode_internal, Option.some.injEq] using hdecode

/--
@isnad1 id=eq.0h1v.s6.e2d10ffe7409 from=translated src=- shape=c3181122 vocab=793b1580
-/
theorem DecoderInstance.length_encode_internal (data : DecoderInstance) :
    data.encode.length =
      2 * (data.messageLength.size + data.inverseAccuracy.size +
        data.outputLength.size + data.inputLength.size + data.seedLength.size) +
        10 +
      data.outputLength * data.inputLength * Fin.bitWidth data.seedLength := by
  simp only [DecoderInstance.encode, pair_length,
    BinaryNatCode.length_encode]
  rw [NWDesign.length_encode_internal]
  omega

/--
@isnad1 id=eq.0h1v.s3.167055278785 from=translated src=- shape=edb93955 vocab=c7c8e3f2
-/
theorem DecoderInstance.decode?_encode_internal (data : DecoderInstance) :
    DecoderInstance.decode? data.encode = some data := by
  cases data
  simp [DecoderInstance.decode?, DecoderInstance.encode]
  rw [NWDesign.decode?_encode_internal]
  rfl

/--
@isnad1 id=iff.0h2v.s4.9e7d8fc57604 from=translated src=- shape=94e3551a vocab=be1a770c
-/
theorem DecoderInstance.decode?_eq_some_iff_internal
    (bits : List Bool) (data : DecoderInstance) :
    DecoderInstance.decode? bits = some data ↔ bits = data.encode := by
  cases data with
  | mk messageLength inverseAccuracy outputLength inputLength seedLength design =>
      simp [DecoderInstance.decode?, DecoderInstance.encode,
        Option.bind_eq_some_iff, unpair?_eq_some_iff,
        BinaryNatCode.decode?_eq_some_iff,
        NWDesign.decode?_eq_some_iff_internal]
      constructor
      · rintro ⟨decodedOutputLength, decodedInputLength, decodedSeedLength,
          decodedDesign, hbits, rfl, rfl, rfl, hdesign⟩
        cases hdesign
        exact hbits
      · intro hbits
        exact ⟨outputLength, inputLength, seedLength, design, hbits, rfl, rfl,
          rfl, HEq.rfl⟩

/--
@isnad1 id=injectiv.0h0v.s2.e0064592dc86 from=translated src=- shape=4b736592 vocab=bff914ce
-/
theorem DecoderInstance.encode_injective_internal :
    Function.Injective DecoderInstance.encode := by
  intro first second hencode
  have hdecode := congrArg DecoderInstance.decode? hencode
  simpa only [DecoderInstance.decode?_encode_internal, Option.some.injEq] using
    hdecode

end NWDesign

end Complexity
