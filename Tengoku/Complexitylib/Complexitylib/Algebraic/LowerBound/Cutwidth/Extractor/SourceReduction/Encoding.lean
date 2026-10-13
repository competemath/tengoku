/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Encoding.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Encoding.Internal

/-!
# Exact enumeration and advice for the actual source reduction

Little-endian coding is a bijection between the finite enumeration range
and Boolean words. Concatenating the outer and candidate codes assigns
distinct advice of one fixed length to every actual sampler position.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Enumerated Boolean words serialize to the actual fixed-width binary encoder.
@isnad1 id=eq.0h2v.s5.9881ac234547 from=translated src=- shape=75d92f8e vocab=3168008b
-/
theorem sourceReductionIndexWord_ofFn (width : Nat) (index : Fin (2 ^ width)) :
    List.ofFn (sourceReductionIndexWord width index) = Nat.toBitsLE width index.val :=
  Internal.sourceReductionIndexWord_ofFn width index

/-- Decoding an enumerated word recovers its index.
@isnad1 id=eq.0h2v.s5.834fbd8e1f4f from=translated src=- shape=7cdfc94a vocab=866ffdcc
-/
theorem sourceReductionWordIndex_indexWord (width : Nat) (index : Fin (2 ^ width)) :
    sourceReductionWordIndex width (sourceReductionIndexWord width index) = index :=
  Internal.sourceReductionWordIndex_indexWord width index

/-- Re-encoding a decoded word recovers every coordinate.
@isnad1 id=eq.0h2v.s4.bb054619f7b9 from=translated src=- shape=fdec4105 vocab=93d82b23
-/
theorem sourceReductionIndexWord_wordIndex (width : Nat) (word : Fin width → Bool) :
    sourceReductionIndexWord width (sourceReductionWordIndex width word) = word :=
  Internal.sourceReductionIndexWord_wordIndex width word

/-- The concrete little-endian enumeration is an equivalence, including at width zero. -/
@[expose] def sourceReductionIndexEquiv (width : Nat) : Fin (2 ^ width) ≃ (Fin width → Bool) where
  toFun := sourceReductionIndexWord width
  invFun := sourceReductionWordIndex width
  left_inv := sourceReductionWordIndex_indexWord width
  right_inv := sourceReductionIndexWord_wordIndex width

/-- Every actual position receives advice of the same total width.
@isnad1 id=eq.0h3v.s5.a49cab84d4a8 from=translated src=- shape=ea7e4ecb vocab=eefde8ec
-/
theorem sourceReductionAdvice_length (outerBits candidateBits : Nat)
    (position : Fin (2 ^ outerBits) × Fin (2 ^ candidateBits)) :
    (sourceReductionAdvice outerBits candidateBits position).length = outerBits + candidateBits :=
  Internal.sourceReductionAdvice_length outerBits candidateBits position

/-- Distinct outer/candidate positions receive distinct advice words.
@isnad1 id=injectiv.0h2v.s5.d224160e3d05 from=translated src=- shape=4f9557f5 vocab=25e69a3f
-/
theorem sourceReductionAdvice_injective (outerBits candidateBits : Nat) :
    Function.Injective (sourceReductionAdvice outerBits candidateBits) :=
  Internal.sourceReductionAdvice_injective outerBits candidateBits

end Algebraic.Cutwidth.Extractor
