/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Encoding.Defs

/-!
# Exact binary enumeration and distinct positional advice

The natural-number codec round trips every word and every bounded index.
Taking and dropping the known outer width recovers the two components of
the concatenated advice, so all sampler positions receive distinct advice.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

/--
@isnad1 id=eq.0h2v.s5.9881ac234547 from=translated src=- shape=75d92f8e vocab=3168008b
-/
theorem sourceReductionIndexWord_ofFn (width : Nat) (index : Fin (2 ^ width)) :
    List.ofFn (sourceReductionIndexWord width index) = Nat.toBitsLE width index.val := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_ofFn, sourceReductionIndexWord]
    rw [List.getElem?_eq_getElem hj']
    rfl

/--
@isnad1 id=eq.0h2v.s5.834fbd8e1f4f from=translated src=- shape=7cdfc94a vocab=866ffdcc
-/
theorem sourceReductionWordIndex_indexWord (width : Nat) (index : Fin (2 ^ width)) :
    sourceReductionWordIndex width (sourceReductionIndexWord width index) = index := by
  apply Fin.ext
  change Nat.fromBitsLE (List.ofFn (sourceReductionIndexWord width index)) = index.val
  rw [sourceReductionIndexWord_ofFn, Nat.fromBitsLE_toBitsLE index.isLt]

/--
@isnad1 id=eq.0h2v.s4.bb054619f7b9 from=translated src=- shape=fdec4105 vocab=93d82b23
-/
theorem sourceReductionIndexWord_wordIndex (width : Nat) (word : Fin width → Bool) :
    sourceReductionIndexWord width (sourceReductionWordIndex width word) = word := by
  apply List.ofFn_injective
  rw [sourceReductionIndexWord_ofFn]
  change Nat.toBitsLE width (Nat.fromBitsLE (List.ofFn word)) = List.ofFn word
  simpa only [List.length_ofFn] using Nat.toBitsLE_fromBitsLE (List.ofFn word)

/--
@isnad1 id=eq.0h3v.s5.a49cab84d4a8 from=translated src=- shape=ea7e4ecb vocab=eefde8ec
-/
theorem sourceReductionAdvice_length (outerBits candidateBits : Nat)
    (position : Fin (2 ^ outerBits) × Fin (2 ^ candidateBits)) :
    (sourceReductionAdvice outerBits candidateBits position).length = outerBits + candidateBits := by
  simp [sourceReductionAdvice]

/--
@isnad1 id=injectiv.0h2v.s5.d224160e3d05 from=translated src=- shape=4f9557f5 vocab=25e69a3f
-/
theorem sourceReductionAdvice_injective (outerBits candidateBits : Nat) :
    Function.Injective (sourceReductionAdvice outerBits candidateBits) := by
  intro first second equal
  obtain ⟨outer, candidate⟩ := List.append_inj equal
    (show (Nat.toBitsLE outerBits first.1.val).length =
      (Nat.toBitsLE outerBits second.1.val).length by simp)
  apply Prod.ext
  · apply Fin.ext
    simpa only [Nat.fromBitsLE_toBitsLE first.1.isLt, Nat.fromBitsLE_toBitsLE second.1.isLt]
      using congrArg Nat.fromBitsLE outer
  · apply Fin.ext
    simpa only [Nat.fromBitsLE_toBitsLE first.2.isLt, Nat.fromBitsLE_toBitsLE second.2.isLt]
      using congrArg Nat.fromBitsLE candidate

end Algebraic.Cutwidth.Extractor.Internal
