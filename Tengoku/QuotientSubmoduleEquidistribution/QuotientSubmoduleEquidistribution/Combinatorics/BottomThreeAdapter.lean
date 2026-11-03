import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.Combinatorics.BottomLevels

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual third closure levels from the five formal shape families

This file packages the exact interface between a classification of
three-element closed supports and the five-family combinatorics used in the
manuscript.  The representation-theoretic layer only has to construct the two
displayed equivalences.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.BottomLevels.BottomThreeAdapter

open Set

universe u v w z

variable {X : Type u} {V : Type v} {E : Type w} {U : Type z}

/-- The actual closed supports at cardinality three.-/
def ClosedLevelThree (c : QuotientSubmoduleEquidistribution.SetClosure X) :=
  {C : c.Closeds // (C : Set X).ncard = 3}

/-- `levelCount 3` is the cardinality of the actual closed-support type.
@isnad1 id=eq.0h2v.s4.f351b4e5c65a from=translated src=- shape=9c0aa99d vocab=8872b761
-/
theorem levelCount_three_eq_natCard_closedLevelThree
    [Finite X] (c : QuotientSubmoduleEquidistribution.SetClosure X) :
    c.levelCount 3 = Nat.card (ClosedLevelThree c) := by
  unfold QuotientSubmoduleEquidistribution.SetClosure.levelCount
  calc
    {C : c.Closeds | (C : Set X).ncard = 3}.ncard =
        Nat.card {C : c.Closeds // (C : Set X).ncard = 3} :=
      (Nat.card_coe_set_eq _).symm
    _ = Nat.card (ClosedLevelThree c) := rfl

/-- Classification data for the third level of one finite closure system.-/
structure Classification
    (c : QuotientSubmoduleEquidistribution.SetClosure X)
    [Fintype V] [Fintype E] [Fintype U]
    (source target : E → V) where
  shapeEquiv :
    BottomThreeShape.Shape (U := U) source target ≃
      ClosedLevelThree c

namespace Classification

variable [Finite X] [Fintype V] [Fintype E] [Fintype U]
  {c : QuotientSubmoduleEquidistribution.SetClosure X} {source target : E → V}

/-- A supplied shape classification gives the exact third-level formula.
@isnad1 id=eq.0h8v.s5.8750d7d59b39 from=translated src=- shape=2cfd2141 vocab=8fbceb7f
-/
theorem levelCount_three_eq_formula
    (D : Classification c (U := U) source target) :
    c.levelCount 3 =
      BottomThreeShape.formula (U := U) source target := by
  rw [levelCount_three_eq_natCard_closedLevelThree]
  calc
    Nat.card (ClosedLevelThree c) =
        Nat.card (BottomThreeShape.Shape (U := U) source target) :=
      Nat.card_congr D.shapeEquiv.symm
    _ = BottomThreeShape.formula (U := U) source target :=
      BottomThreeShape.card source target

end Classification

/-- Simultaneous quotient/submodule classification data.  The second shape
classification swaps arrow sources and targets and uses the same fourth
family `U`.-/
structure SwappedPairClassification
    (qClosure sClosure : QuotientSubmoduleEquidistribution.SetClosure X)
    [Fintype V] [Fintype E] [Fintype U]
    (source target : E → V) where
  qClassification :
    Classification qClosure (U := U) source target
  sClassification :
    Classification sClosure (U := U) target source

namespace SwappedPairClassification

variable [Finite X] [Fintype V] [Fintype E] [Fintype U]
  {qClosure sClosure : QuotientSubmoduleEquidistribution.SetClosure X}
  {source target : E → V}

/-- The quotient-side third level has the five-family formula.
@isnad1 id=eq.0h9v.s6.2e672c5dba53 from=translated src=- shape=1da34b97 vocab=9b56d9ce
-/
theorem qLevelCount_three_eq_formula
    (D : SwappedPairClassification qClosure sClosure (U := U) source target) :
    qClosure.levelCount 3 =
      BottomThreeShape.formula (U := U) source target :=
  D.qClassification.levelCount_three_eq_formula

/-- The submodule-side third level has the same formula after normalizing the
source/target swap.
@isnad1 id=eq.0h9v.s6.bc93cf5a5331 from=translated src=- shape=cf38fc52 vocab=9b56d9ce
-/
theorem sLevelCount_three_eq_formula
    (D : SwappedPairClassification qClosure sClosure (U := U) source target) :
    sClosure.levelCount 3 =
      BottomThreeShape.formula (U := U) source target := by
  calc
    sClosure.levelCount 3 =
        BottomThreeShape.formula (U := U) target source :=
      D.sClassification.levelCount_three_eq_formula
    _ = BottomThreeShape.formula (U := U) source target :=
      (BottomThreeShape.formula_swap source target).symm

/-- Both third levels are given by one exact numerical expression.
@isnad1 id=and.0h9v.s6.edfe237b521d from=translated src=- shape=07c7389e vocab=9b56d9ce
-/
theorem qAndSLevelCount_three_eq_formula
    (D : SwappedPairClassification qClosure sClosure (U := U) source target) :
    (qClosure.levelCount 3 =
        BottomThreeShape.formula (U := U) source target) ∧
      (sClosure.levelCount 3 =
        BottomThreeShape.formula (U := U) source target) :=
  ⟨D.qLevelCount_three_eq_formula, D.sLevelCount_three_eq_formula⟩

/-- Source/target-swapped shape classifications imply equality at level
three.
@isnad1 id=eq.0h9v.s6.6d515ed7a2fd from=translated src=- shape=3ba13635 vocab=754ede00
-/
theorem levelCount_three_eq
    (D : SwappedPairClassification qClosure sClosure (U := U) source target) :
    qClosure.levelCount 3 = sClosure.levelCount 3 := by
  rw [levelCount_three_eq_natCard_closedLevelThree,
    levelCount_three_eq_natCard_closedLevelThree]
  calc
    Nat.card (ClosedLevelThree qClosure) =
        Nat.card (BottomThreeShape.Shape (U := U) source target) :=
      Nat.card_congr D.qClassification.shapeEquiv.symm
    _ = Nat.card (BottomThreeShape.Shape (U := U) target source) :=
      BottomThreeShape.card_swap source target
    _ = Nat.card (ClosedLevelThree sClosure) :=
      Nat.card_congr D.sClassification.shapeEquiv

end SwappedPairClassification

end QuotientSubmoduleEquidistribution.BottomLevels.BottomThreeAdapter
