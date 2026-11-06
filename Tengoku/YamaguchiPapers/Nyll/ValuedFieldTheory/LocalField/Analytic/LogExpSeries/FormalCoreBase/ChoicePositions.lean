/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ExplicitChoiceCounts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Realizing formal-product choices by position sets

This module constructs a basic-factor choice from its mixed and left position
sets and proves the resulting position-count formulas.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- The left basic exponent vector.-/
noncomputable def formalLogOnePlusProductArgumentBasicFactorLeft :
    Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) 1

/-- The right basic exponent vector.-/
noncomputable def formalLogOnePlusProductArgumentBasicFactorRight :
    Fin 2 →₀ ℕ :=
  Finsupp.single (1 : Fin 2) 1

/-- The mixed basic exponent vector.-/
noncomputable def formalLogOnePlusProductArgumentBasicFactorMixed :
    Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1

/-- The basic-factor sequence with mixed positions `M`, left positions `L`,
and right factors in every remaining position below `q`.-/
noncomputable def formalLogOnePlusProductArgumentChoiceFromMixedLeft
    (q : ℕ) (M L : Finset ℕ) : ℕ →₀ (Fin 2 →₀ ℕ) :=
  Finsupp.onFinset (Finset.range q)
    (fun i =>
      if i ∈ Finset.range q then
        if i ∈ M then formalLogOnePlusProductArgumentBasicFactorMixed
        else if i ∈ L then formalLogOnePlusProductArgumentBasicFactorLeft
        else formalLogOnePlusProductArgumentBasicFactorRight
      else 0)
    (by
      intro i hi
      by_cases hq : i ∈ Finset.range q
      · exact hq
      · simp [hq] at hi)

/--
Establishes the identity `formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i = if i ∈ M
then formalLogOnePlusProductArgumentBasicFactorMixed else if i ∈ L then
formalLogOnePlusProductArgumentBasicFactorLeft else
formalLogOnePlusProductArgumentBasicFactorRight`.
@isnad1 id=eq.1h4v.s7.ff84101210c7 from=translated src=- shape=b5ec0fc7 vocab=108fb128
-/
@[simp] theorem formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem
    {q : ℕ} {M L : Finset ℕ} {i : ℕ} (hi : i ∈ Finset.range q) :
    formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i =
      if i ∈ M then formalLogOnePlusProductArgumentBasicFactorMixed
      else if i ∈ L then formalLogOnePlusProductArgumentBasicFactorLeft
      else formalLogOnePlusProductArgumentBasicFactorRight := by
  have hlt : i < q := Finset.mem_range.mp hi
  simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft, hlt]

/-- Establishes the identity `formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i = 0`.
@isnad1 id=eq.1h4v.s7.13a3031f0634 from=translated src=- shape=2fd77493 vocab=2e6e25e9
-/
@[simp] theorem formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_not_mem
    {q : ℕ} {M L : Finset ℕ} {i : ℕ} (hi : i ∉ Finset.range q) :
    formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i = 0 := by
  have hle : q ≤ i := by simpa [Finset.mem_range] using hi
  simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft, hle]

/-- Positions below `q` at which `l` has the mixed-factor label.-/
noncomputable def formalLogOnePlusProductArgumentMixedPositions
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : Finset ℕ :=
  (Finset.range q).filter fun i =>
    formalLogOnePlusProductArgumentBasicFactorLabel (l i) = (2 : Fin 3)

/-- Positions below `q` at which `l` has the left-factor label.-/
noncomputable def formalLogOnePlusProductArgumentLeftPositions
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : Finset ℕ :=
  (Finset.range q).filter fun i =>
    formalLogOnePlusProductArgumentBasicFactorLabel (l i) = (0 : Fin 3)

/-- Positions below `q` at which `l` has the right-factor label.-/
noncomputable def formalLogOnePlusProductArgumentRightPositions
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : Finset ℕ :=
  (Finset.range q).filter fun i =>
    formalLogOnePlusProductArgumentBasicFactorLabel (l i) = (1 : Fin 3)

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
