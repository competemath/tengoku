/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.Interpretation.Composition.Internal
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.Interpretation.Pullback

/-!
# Composition and identity for tagged interpretations

Composition preserves the interpreted structure up to isomorphism. Its tag count
is `t₂ * t₁ ^ d₂`, its dimension is `d₂ * d₁`, and invariant queries give the same
answer under composition or successive application. The one-tag, dimension-one
identity is likewise an identity up to isomorphism.

These are the semantic laws needed for first-order reductions, following
Immerman, Chapter 3, and the tagged presentation of Senellart--Gnatenko (2026).
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity.TaggedFOInterpretation

variable {U V W : Vocabulary} {t₁ d₁ t₂ d₂ : Nat}

/-- The identity tagged interpretation has one tag and one coordinate. -/
def idInterp (V : Vocabulary) : TaggedFOInterpretation V V 1 1 :=
  (FOInterpretation.idInterp V).toTagged

/-- The identity interpreted structure is canonically isomorphic to its input. -/
def idIso (A : FinStruct V) : Iso ((idInterp V).apply A) A := by
  simpa only [idInterp, FOInterpretation.apply_idInterp] using
    (FOInterpretation.idInterp V).toTaggedIso A

/-- Invariant queries cannot distinguish composition from successive application.
@isnad1 id=iff.1h11v.s6.e1f752c6951b from=translated src=- shape=aff9d26d vocab=19b7472f
-/
theorem comp_query (I₂ : TaggedFOInterpretation V W t₂ d₂)
    (I₁ : TaggedFOInterpretation U V t₁ d₁) (A : FinStruct U)
    {Q : BooleanQuery W} (hQ : Q.IsOrderIndependent) :
    Q ((I₂.comp I₁).apply A) ↔ Q (I₂.apply (I₁.apply A)) := hQ ⟨I₂.compIso I₁ A⟩

/-- Translating along a composite agrees semantically with successive translations.
@isnad1 id=iff.0h11v.s6.c28ba6f78b1e from=translated src=- shape=8401524a vocab=7b67e2a3
-/
theorem translateSentence_comp_models (I₂ : TaggedFOInterpretation V W t₂ d₂)
    (I₁ : TaggedFOInterpretation U V t₁ d₁) (A : FinStruct U) (φ : Sentence W) :
    Sentence.Models A ((I₂.comp I₁).translateSentence φ) ↔
      Sentence.Models A (I₁.translateSentence (I₂.translateSentence φ)) := by
  simpa only [translateSentence_models] using I₂.comp_query I₁ A (Sentence.orderIndependent φ)

end Complexity.DescriptiveComplexity.TaggedFOInterpretation
