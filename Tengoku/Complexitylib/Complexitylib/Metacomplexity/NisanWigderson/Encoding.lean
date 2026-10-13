/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Encoding.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Encoding.Internal

/-!
# Canonical codec for Nisan--Wigderson designs

The complete ordered coordinate table is encoded injectively using exactly
`outputLength * inputLength * clog_2(seedLength)` bits. The executable decoder
rejects malformed lengths, out-of-range coordinates, and noninjective blocks,
round-trips every valid design, and accepts only that design's canonical
encoding. A nested self-delimiting wrapper also records all numeric parameters
needed by one uniform list-decoder invocation.
-/

public section

namespace Complexity

namespace NWDesign

/-- Canonical NW-design encoding has the exact rectangular coordinate-table
length.
@isnad1 id=eq.0h4v.s5.105c8027e465 from=translated src=- shape=7b47dab5 vocab=5598aea9
-/
@[simp] theorem length_encode
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength) :
    design.encode.length =
      outputLength * inputLength * Fin.bitWidth seedLength :=
  length_encode_internal design

/-- Canonical NW-design encoding is injective.
@isnad1 id=injectiv.0h3v.s4.a569e2baf84a from=translated src=- shape=0d8832f4 vocab=8d4cca1d
-/
theorem encode_injective
    {outputLength inputLength seedLength : ℕ} :
    Function.Injective
      (encode : NWDesign outputLength inputLength seedLength → List Bool) :=
  encode_injective_internal

/-- Decoding one coordinate from an encoded design recovers it exactly.
@isnad1 id=eq.0h6v.s5.6e9301c06105 from=translated src=- shape=4d74bdaf vocab=ed4b6dc7
-/
@[simp] theorem decodeCoordinate?_encode
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) (input : Fin inputLength) :
    decodeCoordinate? outputLength inputLength seedLength design.encode
        output input =
      some (design.coordinates output input) :=
  decodeCoordinate?_encode_internal design output input

/-- The canonical NW-design decoder round-trips every valid design.
@isnad1 id=eq.0h4v.s5.27a9233fc4c8 from=translated src=- shape=0b709110 vocab=1769042c
-/
@[simp] theorem decode?_encode
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength) :
    decode? outputLength inputLength seedLength design.encode = some design :=
  decode?_encode_internal design

/-- The decoder rejects every string whose total length is malformed, including
when the design has no output or input coordinates.
@isnad1 id=eq.1h4v.s5.374e0ecac6b6 from=translated src=- shape=1dd04554 vocab=80588980
-/
theorem decode?_eq_none_of_length_ne
    (outputLength inputLength seedLength : ℕ) (bits : List Bool)
    (hlength : bits.length ≠
      outputLength * inputLength * Fin.bitWidth seedLength) :
    decode? outputLength inputLength seedLength bits = none :=
  decode?_eq_none_of_length_ne_internal outputLength inputLength seedLength bits
    hlength

/-- Decoding yields a given design exactly on its canonical encoding.
@isnad1 id=iff.0h5v.s5.ccda5ebfdc94 from=translated src=- shape=82fb6e9a vocab=ab23c28e
-/
theorem decode?_eq_some_iff
    {outputLength inputLength seedLength : ℕ} (bits : List Bool)
    (design : NWDesign outputLength inputLength seedLength) :
    decode? outputLength inputLength seedLength bits = some design ↔
      bits = design.encode :=
  decode?_eq_some_iff_internal bits design

namespace DecoderInstance

/-- A self-describing decoder instance has the exact cost of five framed
minimal binary parameters followed by the raw coordinate table.
@isnad1 id=eq.0h1v.s6.e2d10ffe7409 from=translated src=- shape=c3181122 vocab=793b1580
-/
@[simp] theorem length_encode (data : DecoderInstance) :
    data.encode.length =
      2 * (data.messageLength.size + data.inverseAccuracy.size +
        data.outputLength.size + data.inputLength.size + data.seedLength.size) +
        10 +
      data.outputLength * data.inputLength * Fin.bitWidth data.seedLength :=
  data.length_encode_internal

/-- The self-describing instance decoder round-trips every valid instance.
@isnad1 id=eq.0h1v.s3.167055278785 from=translated src=- shape=edb93955 vocab=c7c8e3f2
-/
@[simp] theorem decode?_encode (data : DecoderInstance) :
    DecoderInstance.decode? data.encode = some data :=
  data.decode?_encode_internal

/-- Parsing yields a given self-describing instance exactly on its canonical
encoding.
@isnad1 id=iff.0h2v.s4.9e7d8fc57604 from=translated src=- shape=94e3551a vocab=be1a770c
-/
theorem decode?_eq_some_iff (bits : List Bool) (data : DecoderInstance) :
    DecoderInstance.decode? bits = some data ↔ bits = data.encode :=
  decode?_eq_some_iff_internal bits data

/-- Self-describing decoder-instance encoding is injective.
@isnad1 id=injectiv.0h0v.s2.e0064592dc86 from=translated src=- shape=4b736592 vocab=bff914ce
-/
theorem encode_injective : Function.Injective DecoderInstance.encode :=
  encode_injective_internal

end DecoderInstance

end NWDesign

end Complexity
