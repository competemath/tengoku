/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.SecondOrder.Connectives.Defs
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.SecondOrder.Connectives.Internal

/-!
# Existential second-order conjunction and disjunction

`existConj` and `existDisj` combine formulas while collecting their leading
existential relation quantifiers into one prefix. Their semantics hold for
arbitrary open formulas; existential SO operands produce existential SO results.
Each result has exactly the sum of the operand sizes plus one, so witness merging
does not duplicate formulas.

This is the existential-prefix manipulation used in the second-order framework
of Immerman's *Descriptive Complexity*, Section 7.1. It supplies logical closure
before the machine characterization of existential SO is proved.
-/

public section

namespace Complexity.DescriptiveComplexity.SOFormula

variable {V : Vocabulary} {rctx : List Nat} {n : Nat}

/-- Merging existential prefixes computes conjunction or disjunction as selected.
@isnad1 id=iff.0h9v.s6.908c43870da8 from=translated src=- shape=60b4a40f vocab=9e964a61
-/
theorem mergeExist_sat (isConjunction : Bool) (φ ψ : SOFormula V rctx n)
    (A : FinStruct V) (σ : Env A.card n) (ρ : REnv A.card rctx) :
    (φ.mergeExist isConjunction ψ).Sat A σ ρ ↔
      if isConjunction then φ.Sat A σ ρ ∧ ψ.Sat A σ ρ else φ.Sat A σ ρ ∨ ψ.Sat A σ ρ :=
  mergeExist_sat_internal isConjunction φ ψ A σ ρ

/-- The merged prefix retains existential SO form.
@isnad1 id=isexists.2h6v.s5.40e5dc83511c from=translated src=- shape=18cfba02 vocab=a81b2a76
-/
theorem isExistSO_mergeExist (isConjunction : Bool) (φ ψ : SOFormula V rctx n)
    (hφ : φ.IsExistSO) (hψ : ψ.IsExistSO) : (φ.mergeExist isConjunction ψ).IsExistSO :=
  isExistSO_mergeExist_internal isConjunction φ ψ hφ hψ

/-- Prefix merging adds one connective and preserves all other syntax nodes.
@isnad1 id=eq.0h6v.s5.4887658d5569 from=translated src=- shape=b64b92a9 vocab=e77f0aab
-/
@[simp] theorem size_mergeExist (isConjunction : Bool) (φ ψ : SOFormula V rctx n) :
    (φ.mergeExist isConjunction ψ).size = φ.size + ψ.size + 1 :=
  size_mergeExist_internal isConjunction φ ψ

/-- Existential-prefix conjunction has the usual conjunction semantics.
@isnad1 id=iff.0h8v.s5.ff5a80884ac5 from=translated src=- shape=b8faf25d vocab=9f560eed
-/
theorem existConj_sat (φ ψ : SOFormula V rctx n) (A : FinStruct V)
    (σ : Env A.card n) (ρ : REnv A.card rctx) :
    (φ.existConj ψ).Sat A σ ρ ↔ φ.Sat A σ ρ ∧ ψ.Sat A σ ρ :=
  mergeExist_sat true φ ψ A σ ρ

/-- Existential-prefix disjunction has the usual disjunction semantics.
@isnad1 id=iff.0h8v.s5.cdfca1558b6f from=translated src=- shape=b8faf25d vocab=51660730
-/
theorem existDisj_sat (φ ψ : SOFormula V rctx n) (A : FinStruct V)
    (σ : Env A.card n) (ρ : REnv A.card rctx) :
    (φ.existDisj ψ).Sat A σ ρ ↔ φ.Sat A σ ρ ∨ ψ.Sat A σ ρ :=
  mergeExist_sat false φ ψ A σ ρ

/-- Existential SO form is closed under prefix-merging conjunction.
@isnad1 id=isexists.2h5v.s5.05b3b3af07da from=translated src=- shape=6e1e13f0 vocab=946cd6d5
-/
theorem IsExistSO.existConj {φ ψ : SOFormula V rctx n}
    (hφ : φ.IsExistSO) (hψ : ψ.IsExistSO) : (φ.existConj ψ).IsExistSO :=
  isExistSO_mergeExist true φ ψ hφ hψ

/-- Existential SO form is closed under prefix-merging disjunction.
@isnad1 id=isexists.2h5v.s5.3525e410339f from=translated src=- shape=6e1e13f0 vocab=7e7b4c97
-/
theorem IsExistSO.existDisj {φ ψ : SOFormula V rctx n}
    (hφ : φ.IsExistSO) (hψ : ψ.IsExistSO) : (φ.existDisj ψ).IsExistSO :=
  isExistSO_mergeExist false φ ψ hφ hψ

/-- Existential-prefix conjunction has additive size, with one new connective.
@isnad1 id=eq.0h5v.s5.ee714f8e5981 from=translated src=- shape=98222226 vocab=5a1622db
-/
@[simp] theorem size_existConj (φ ψ : SOFormula V rctx n) :
    (φ.existConj ψ).size = φ.size + ψ.size + 1 := size_mergeExist true φ ψ

/-- Existential-prefix disjunction has additive size, with one new connective.
@isnad1 id=eq.0h5v.s5.711ec6c1b1ce from=translated src=- shape=98222226 vocab=390c8a1f
-/
@[simp] theorem size_existDisj (φ ψ : SOFormula V rctx n) :
    (φ.existDisj ψ).size = φ.size + ψ.size + 1 := size_mergeExist false φ ψ

end Complexity.DescriptiveComplexity.SOFormula
