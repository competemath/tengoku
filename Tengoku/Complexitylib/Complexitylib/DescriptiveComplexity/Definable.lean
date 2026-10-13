/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.Reduction
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.SecondOrder.Isomorphism

/-!
# First-order definable queries

A Boolean query is **first-order definable** when some FO sentence defines it. The
central fact of descriptive complexity — that a logic can only define
"legitimate" (order-independent) queries — is recorded here for first-order logic:
every FO-definable query is order-independent (`FODefinable.orderIndependent`, a
packaging of Immerman Proposition 1.16). Since FO has `¬`, `∧`, `∨`, the
FO-definable queries are closed under complement, intersection, and union.

This is the template for the planned logic/complexity correspondences: a class
of logics defines a class of queries, and expressibility questions become lower
bounds.

## Main definitions and results

- `DescriptiveComplexity.FODefinable` — first-order definability of a query.
- `DescriptiveComplexity.FODefinable.orderIndependent` — FO-definable ⟹
  order-independent.
- `FODefinable.complement`, `.inter`, `.union` — Boolean closure.
- `FODefinable.of_reduces`, `.of_projReduces` — closure under first-order
  reductions and projections.
- `FODefinable.toSODefinable` — `FO ⊆ SO` at the query level.
-/

public section

open scoped Complexity.DescriptiveComplexity

namespace Complexity

namespace DescriptiveComplexity

variable {V : Vocabulary}

/-- A Boolean query is **first-order definable** if some FO sentence defines it. -/
@[expose] def FODefinable (Q : BooleanQuery V) : Prop :=
  ∃ φ : Sentence V, ∀ A : FinStruct V, Q A ↔ (A ⊨ φ)

/-- **FO-definable queries are order-independent** (Immerman Proposition 1.16,
    packaged): a query defined by an FO sentence cannot distinguish isomorphic
    structures.
@isnad1 id=isorderi.1h2v.s3.71062822212e from=translated src=- shape=b28a8773 vocab=235f00e3
-/
theorem FODefinable.orderIndependent {Q : BooleanQuery V} (hQ : FODefinable Q) :
    Q.IsOrderIndependent := by
  obtain ⟨φ, hφ⟩ := hQ
  intro A B hiso
  rw [hφ A, hφ B]
  exact Sentence.orderIndependent φ hiso

/-- FO-definable queries are closed under complement (via `¬`).
@isnad1 id=fodefina.1h2v.s3.5a9bfd1883d6 from=translated src=- shape=525138f7 vocab=0beb30d8
-/
theorem FODefinable.complement {Q : BooleanQuery V} (hQ : FODefinable Q) :
    FODefinable Q.complement := by
  obtain ⟨φ, hφ⟩ := hQ
  exact ⟨φ.neg, fun A => by
    simp only [BooleanQuery.complement, hφ A, Sentence.Models, Formula.Sat]⟩

/-- FO-definable queries are closed under intersection (via `∧`).
@isnad1 id=fodefina.2h3v.s4.eef2ac017475 from=translated src=- shape=85b2e57a vocab=91301dfd
-/
theorem FODefinable.inter {Q₁ Q₂ : BooleanQuery V}
    (h₁ : FODefinable Q₁) (h₂ : FODefinable Q₂) : FODefinable (Q₁.inter Q₂) := by
  obtain ⟨φ, hφ⟩ := h₁
  obtain ⟨ψ, hψ⟩ := h₂
  exact ⟨φ.conj ψ, fun A => by
    simp only [BooleanQuery.inter, hφ A, hψ A, Sentence.Models, Formula.Sat]⟩

/-- FO-definable queries are closed under union (via `∨`).
@isnad1 id=fodefina.2h3v.s4.febaa6366482 from=translated src=- shape=85b2e57a vocab=a6893a57
-/
theorem FODefinable.union {Q₁ Q₂ : BooleanQuery V}
    (h₁ : FODefinable Q₁) (h₂ : FODefinable Q₂) : FODefinable (Q₁.union Q₂) := by
  obtain ⟨φ, hφ⟩ := h₁
  obtain ⟨ψ, hψ⟩ := h₂
  exact ⟨φ.disj ψ, fun A => by
    simp only [BooleanQuery.union, hφ A, hψ A, Sentence.Models, Formula.Sat]⟩

/-- **FO-definability is closed under first-order reductions.** If `Q₁` reduces to
    an FO-definable query `Q₂`, translating a sentence for `Q₂` along the reduction
    interpretation gives a sentence for `Q₁`.
@isnad1 id=fodefina.2h4v.s4.f49f596f2e5e from=translated src=- shape=bd0a1ff2 vocab=6329b88d
-/
theorem FODefinable.of_reduces {W : Vocabulary} {Q₁ : BooleanQuery V}
    {Q₂ : BooleanQuery W} (hQ₂ : FODefinable Q₂) (hred : FOReduces Q₁ Q₂) :
    FODefinable Q₁ := by
  obtain ⟨I, hI⟩ := hred
  obtain ⟨φ, hφ⟩ := hQ₂
  refine ⟨I.translate φ, fun A => ?_⟩
  rw [hI A, hφ (I.apply A)]
  exact I.translate_sat A (emptyEnv A.card) φ

/-- FO-definability is closed under first-order projections.
@isnad1 id=fodefina.2h4v.s4.c7fd15eeaf7e from=translated src=- shape=bd0a1ff2 vocab=b957c061
-/
theorem FODefinable.of_projReduces {W : Vocabulary} {Q₁ : BooleanQuery V}
    {Q₂ : BooleanQuery W} (hQ₂ : FODefinable Q₂) (hred : FOProjReduces Q₁ Q₂) :
    FODefinable Q₁ :=
  hQ₂.of_reduces hred.toFOReduces

/-- **`FO ⊆ SO` at the query level:** every first-order definable query is
    second-order definable, via the truth-preserving FO embedding into SO.
@isnad1 id=sodefina.1h2v.s3.39b28f0d990f from=translated src=- shape=b28a8773 vocab=e03ae64a
-/
theorem FODefinable.toSODefinable {Q : BooleanQuery V} (hQ : FODefinable Q) :
    SODefinable Q := by
  obtain ⟨φ, hφ⟩ := hQ
  exact ⟨SOFormula.ofFormula φ [], fun A => (hφ A).trans (SOSentence.models_ofFormula A φ).symm⟩

end DescriptiveComplexity

end Complexity
