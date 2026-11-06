/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Valuation extensions

Mathlib's uniqueness criterion for valuations is expressed through
`Valuation.IsEquiv`: two valuations on the same field are equivalent exactly
when they have the same valuation subring.  The results here use the ambient
valued-extension property directly; no marker object is introduced.
-/

namespace ValuationTheory

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

section EquivalentBase

variable {Gamma₁ Gamma₂ GammaL : Type*}
variable [LinearOrderedCommGroupWithZero Gamma₁]
variable [LinearOrderedCommGroupWithZero Gamma₂]
variable [LinearOrderedCommGroupWithZero GammaL]

end EquivalentBase

section ComapAlongCompatibleEmbedding

variable {M : Type y} [Field M] [Algebra K M]
variable {GammaK GammaM : Type*}
variable [LinearOrderedCommGroupWithZero GammaK]
variable [LinearOrderedCommGroupWithZero GammaM]

end ComapAlongCompatibleEmbedding

section LocalValuationSubringMap

variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)

end LocalValuationSubringMap

section Pullback

variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

end Pullback

section Comparison

variable (target : CompleteDVF.{w, x} L)

/-- Equality of valuation subrings implies valuation equivalence.
@isnad1 id=isequiv.1h4v.s6.9fcb5e9762f8 from=translated src=- shape=ed0452c6 vocab=9e66b8b5
-/
theorem valuation_isEquiv_of_valuationSubring_eq
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma')
    (hsub : target.valuation.valuationSubring = v'.valuationSubring) :
    target.valuation.IsEquiv v' :=
  (_root_.Valuation.isEquiv_iff_valuationSubring target.valuation v').2 hsub

/-- Equivalent valuations have the same valuation subring.
@isnad1 id=eq.1h4v.s6.fcdeb7012beb from=translated src=- shape=d02c8c40 vocab=9e66b8b5
-/
theorem valuationSubring_eq_of_valuation_isEquiv
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    {v' : _root_.Valuation L Gamma'}
    (h : target.valuation.IsEquiv v') :
    target.valuation.valuationSubring = v'.valuationSubring :=
  (_root_.Valuation.isEquiv_iff_valuationSubring target.valuation v').1 h

end Comparison
end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
