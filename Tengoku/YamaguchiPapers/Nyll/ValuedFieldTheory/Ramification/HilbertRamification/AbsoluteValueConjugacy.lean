/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.FiniteNormExtension
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaAbsoluteValue
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaCoefficients
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaIntegralClosure
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueExtensionCoefficients
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completeness
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.ExponentialValuation
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Extension
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Nonarchimedean
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Ostrowski
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.PrincipalAdicCompleteness
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.SpectralExtension
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.Core
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Completion.AbsoluteValueExtensions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Valuation conjugacy

For a possibly infinite Galois extension `L/K`, the Galois group acts
transitively on the extensions to `L` of a nontrivial absolute value of `K`.
-/

noncomputable section

universe u v

namespace AlgebraicNumberTheory
namespace Valuations

/-- Pull an absolute value back by a field automorphism.  This is the canonical
right action `w ↦ w ∘ σ`.-/
def absoluteValueConjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) : AbsoluteValue L ℝ :=
  w.comp (f := σ.toRingEquiv.toRingHom) σ.injective

/--
@isnad1 id=eq.0h5v.s7.eabfb8f4ec35 from=translated src=- shape=f91e405b vocab=fb519c3b
-/
@[simp] theorem absoluteValueConjugate_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) (x : L) :
    absoluteValueConjugate w σ x = w (σ x) :=
  rfl

/-- Conjugating an extension by a ground-field automorphism gives another
exact extension of the same base absolute value.
@isnad1 id=extends.0h5v.s6.31fb88675f25 from=translated src=- shape=67b1beaa vocab=9d64fa32
-/
theorem absoluteValueConjugate_extends
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) :
    AbsoluteValue.Extends vK (absoluteValueConjugate w.1 σ) := by
  intro x
  rw [absoluteValueConjugate_apply, σ.commutes, w.2 x]

/-- The conjugated extension as an element of the exact-extension type.-/
def absoluteValueExtensionConjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) : AbsoluteValueExtension vK L :=
  ⟨absoluteValueConjugate w.1 σ,
    absoluteValueConjugate_extends vK w σ⟩

end Valuations
end AlgebraicNumberTheory
