/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.Definable
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.SecondOrder.Reduction
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.SecondOrder.Connectives
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.SecondOrder.Certificate

/-!
# Existential second-order definability

`ExistSODefinable` retains a syntactic existential SO witness for a query. It is
closed under intersection, union, and universe-preserving FO reductions, includes
FO definability, and implies isomorphism invariance. Its induced languages have
verified binary certificate checkers and polynomial witness bounds. The downstream
`SecondOrder.PolynomialTime` module proves their membership in the machine class
`Complexity.NP`, the upper direction of Fagin's theorem (Fagin, 1974).

The separation of a definability witness from reduction transport follows the
organization of Senellart and Gnatenko (2026), Sections 3--4,
<https://arxiv.org/abs/2609.18261>, specialized to our existing interpretations.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

variable {V W : Vocabulary}

/-- A query defined by an existential SO prefix followed by an FO matrix. -/
def ExistSODefinable (Q : BooleanQuery V) : Prop :=
  ∃ φ : SOSentence V, φ.IsExistSO ∧ ∀ A : FinStruct V, Q A ↔ SOSentence.Models A φ

/-- An existential SO witness is in particular a second-order witness.
@isnad1 id=sodefina.1h2v.s3.7a5ca25db85b from=translated src=- shape=b28a8773 vocab=cfb16f06
-/
theorem ExistSODefinable.toSODefinable {Q : BooleanQuery V} (hQ : ExistSODefinable Q) :
    SODefinable Q := by
  obtain ⟨φ, _, hφ⟩ := hQ
  exact ⟨φ, hφ⟩

/-- Existential SO definability implies invariance under isomorphism.
@isnad1 id=isorderi.1h2v.s3.ed39fe312c63 from=translated src=- shape=b28a8773 vocab=2e432328
-/
theorem ExistSODefinable.orderIndependent {Q : BooleanQuery V} (hQ : ExistSODefinable Q) :
    Q.IsOrderIndependent := hQ.toSODefinable.orderIndependent

/-- A first-order witness is an existential SO witness with an empty prefix.
@isnad1 id=existsod.1h2v.s3.6077235b6d25 from=translated src=- shape=b28a8773 vocab=fffd3e8a
-/
theorem FODefinable.toExistSODefinable {Q : BooleanQuery V} (hQ : FODefinable Q) :
    ExistSODefinable Q := by
  obtain ⟨φ, hφ⟩ := hQ
  exact ⟨.ofFormula φ [], SOFormula.ofFormula_isExistSO φ [],
    fun A => (hφ A).trans (SOSentence.models_ofFormula A φ).symm⟩

/-- Existential SO queries are closed under intersection by merging their witness prefixes.
@isnad1 id=existsod.2h3v.s4.8a7f127fe8a9 from=translated src=- shape=85b2e57a vocab=48940a81
-/
theorem ExistSODefinable.inter {Q₁ Q₂ : BooleanQuery V}
    (h₁ : ExistSODefinable Q₁) (h₂ : ExistSODefinable Q₂) :
    ExistSODefinable (Q₁.inter Q₂) := by
  obtain ⟨φ, hφ, hQ₁⟩ := h₁
  obtain ⟨ψ, hψ, hQ₂⟩ := h₂
  refine ⟨φ.existConj ψ, hφ.existConj hψ, fun A => ?_⟩
  simpa only [BooleanQuery.inter, hQ₁ A, hQ₂ A, SOSentence.Models] using
    (φ.existConj_sat ψ A (emptyEnv A.card) (emptyREnv A.card)).symm

/-- Existential SO queries are closed under union by merging their witness prefixes.
@isnad1 id=existsod.2h3v.s4.cf5e98bd96c1 from=translated src=- shape=85b2e57a vocab=5db055cd
-/
theorem ExistSODefinable.union {Q₁ Q₂ : BooleanQuery V}
    (h₁ : ExistSODefinable Q₁) (h₂ : ExistSODefinable Q₂) :
    ExistSODefinable (Q₁.union Q₂) := by
  obtain ⟨φ, hφ, hQ₁⟩ := h₁
  obtain ⟨ψ, hψ, hQ₂⟩ := h₂
  refine ⟨φ.existDisj ψ, hφ.existDisj hψ, fun A => ?_⟩
  simpa only [BooleanQuery.union, hQ₁ A, hQ₂ A, SOSentence.Models] using
    (φ.existDisj_sat ψ A (emptyEnv A.card) (emptyREnv A.card)).symm

/-- Existential SO definability travels backward through FO reductions.
@isnad1 id=existsod.2h4v.s4.d2e6061048ea from=translated src=- shape=bd0a1ff2 vocab=fa773a7e
-/
theorem ExistSODefinable.of_reduces {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W}
    (hQ₂ : ExistSODefinable Q₂) (hred : FOReduces Q₁ Q₂) : ExistSODefinable Q₁ := by
  obtain ⟨I, hI⟩ := hred
  obtain ⟨φ, hfragment, hφ⟩ := hQ₂
  exact ⟨I.translateSO φ, (I.isExistSO_translateSO φ).mpr hfragment,
    fun A => (hI A).trans ((hφ (I.apply A)).trans (I.translateSO_sat A φ _ _))⟩

/-- Existential SO definability also travels backward through quantifier-free reductions.
@isnad1 id=existsod.2h4v.s4.8235fb6be508 from=translated src=- shape=bd0a1ff2 vocab=3390ff81
-/
theorem ExistSODefinable.of_projReduces {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W}
    (hQ₂ : ExistSODefinable Q₂) (hred : FOProjReduces Q₁ Q₂) : ExistSODefinable Q₁ :=
  hQ₂.of_reduces hred.toFOReduces

/-- An inexpressibility result rules out every FO reduction to an existential SO query.
@isnad1 id=not.2h4v.s4.4748b0bd564e from=translated src=- shape=cb9b8df3 vocab=fa773a7e
-/
theorem not_foReduces_of_not_existSODefinable {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W}
    (hQ₁ : ¬ ExistSODefinable Q₁) (hQ₂ : ExistSODefinable Q₂) : ¬ FOReduces Q₁ Q₂ :=
  fun h => hQ₁ (hQ₂.of_reduces h)

end Complexity.DescriptiveComplexity
