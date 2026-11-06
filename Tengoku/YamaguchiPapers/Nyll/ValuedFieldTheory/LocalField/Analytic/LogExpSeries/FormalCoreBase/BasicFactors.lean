/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ProductArgument

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic factors in the formal logarithm product argument

This module packages the three possible nonzero monomial factors and their
finite choice spaces.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- The three exponent vectors with nonzero coefficient in `X + Y + XY`.-/
def formalLogOnePlusProductArgumentBasicFactor
    (m : Fin 2 →₀ ℕ) : Prop :=
  m = Finsupp.single (0 : Fin 2) 1 ∨
    m = Finsupp.single (1 : Fin 2) 1 ∨
      m =
        Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1

/-- The finite set of the left, right, and mixed basic exponent vectors.-/
noncomputable def formalLogOnePlusProductArgumentBasicFactorFinset :
    Finset (Fin 2 →₀ ℕ) := by
  classical
  exact
    {Finsupp.single (0 : Fin 2) 1,
      Finsupp.single (1 : Fin 2) 1,
      Finsupp.single (0 : Fin 2) 1 +
        Finsupp.single (1 : Fin 2) 1}

/-- Establishes the identity `formalLogOnePlusProductArgumentBasicFactorFinset.card = 3`.-/
@[simp] theorem formalLogOnePlusProductArgumentBasicFactorFinset_card :
    formalLogOnePlusProductArgumentBasicFactorFinset.card = 3 := by
  classical
  simp [formalLogOnePlusProductArgumentBasicFactorFinset,
    finsupp_fin_two_single_left_ne_single_right]

/-- Labels the left, right, and mixed basic factors by `0`, `1`, and `2`.
Non-basic inputs receive the mixed label; all uses that recover a factor from
its label therefore carry a basic-factor hypothesis.-/
def formalLogOnePlusProductArgumentBasicFactorLabel
    (m : Fin 2 →₀ ℕ) : Fin 3 :=
  if m = Finsupp.single (0 : Fin 2) 1 then 0
  else if m = Finsupp.single (1 : Fin 2) 1 then 1
  else 2

/--
Establishes the identity `formalLogOnePlusProductArgumentBasicFactorLabel (Finsupp.single (0 : Fin
2) 1) = 0`.-/
@[simp] theorem formalLogOnePlusProductArgumentBasicFactorLabel_left :
    formalLogOnePlusProductArgumentBasicFactorLabel
        (Finsupp.single (0 : Fin 2) 1) = 0 := by
  simp [formalLogOnePlusProductArgumentBasicFactorLabel]

/--
Establishes the identity `formalLogOnePlusProductArgumentBasicFactorLabel (Finsupp.single (1 : Fin
2) 1) = 1`.-/
@[simp] theorem formalLogOnePlusProductArgumentBasicFactorLabel_right :
    formalLogOnePlusProductArgumentBasicFactorLabel
        (Finsupp.single (1 : Fin 2) 1) = 1 := by
  simp [formalLogOnePlusProductArgumentBasicFactorLabel,
    finsupp_fin_two_single_left_ne_single_right.symm]

/--
Establishes the identity `formalLogOnePlusProductArgumentBasicFactorLabel (Finsupp.single (0 : Fin
2) 1 + Finsupp.single (1 : Fin 2) 1) = 2`.-/
@[simp] theorem formalLogOnePlusProductArgumentBasicFactorLabel_mixed :
    formalLogOnePlusProductArgumentBasicFactorLabel
        (Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1) = 2 := by
  simp [formalLogOnePlusProductArgumentBasicFactorLabel,
    finsupp_fin_two_single_left_ne_mixed.symm,
    finsupp_fin_two_single_right_ne_mixed.symm]

/-- Finitely supported sequences of `q` basic factors.-/
noncomputable def formalLogOnePlusProductArgumentBasicFactorProductChoices
    (q : ℕ) : Finset (ℕ →₀ (Fin 2 →₀ ℕ)) := by
  classical
  exact
    (Finset.range q).finsupp
      (fun _ => formalLogOnePlusProductArgumentBasicFactorFinset)

/-- Sequences of `q` basic factors whose exponent-vector sum is `e`.-/
noncomputable def formalLogOnePlusProductArgumentBasicFactorChoices
    (q : ℕ) (e : Fin 2 →₀ ℕ) :
    Finset (ℕ →₀ (Fin 2 →₀ ℕ)) := by
  classical
  exact
    (Finset.finsuppAntidiag (Finset.range q) e).filter
      (fun l : ℕ →₀ (Fin 2 →₀ ℕ) =>
        ∀ i ∈ Finset.range q,
          formalLogOnePlusProductArgumentBasicFactor (l i))

/-- The number of left factors among the first `q` entries of `l`.-/
def formalLogOnePlusProductArgumentLeftChoiceCount
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : ℕ :=
  ∑ i ∈ Finset.range q,
    if l i = Finsupp.single (0 : Fin 2) 1 then 1 else 0

/-- The number of right factors among the first `q` entries of `l`.-/
def formalLogOnePlusProductArgumentRightChoiceCount
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : ℕ :=
  ∑ i ∈ Finset.range q,
    if l i = Finsupp.single (1 : Fin 2) 1 then 1 else 0

/-- The number of mixed factors among the first `q` entries of `l`.-/
def formalLogOnePlusProductArgumentMixedChoiceCount
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : ℕ :=
  ∑ i ∈ Finset.range q,
    if l i =
        Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1
    then 1 else 0

/-- The number of entries among the first `q` positions with label `j`.-/
def formalLogOnePlusProductArgumentBasicFactorLabelCount
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) (j : Fin 3) : ℕ :=
  ∑ i ∈ Finset.range q,
    if formalLogOnePlusProductArgumentBasicFactorLabel (l i) = j
    then 1 else 0

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
