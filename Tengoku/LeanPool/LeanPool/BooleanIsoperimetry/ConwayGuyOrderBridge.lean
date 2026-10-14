/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.BooleanIsoperimetry.Cube
public import Tengoku.LeanPool.LeanPool.BooleanIsoperimetry.ConwayGuyCoherentGap
import Tengoku.LeanPool.LeanPool.BooleanIsoperimetry.ConwayGuyRigidity
public import Tengoku

/-!
# From unit relations to consecutive subset-sum gaps

This file supplies the elementary order-theoretic bridge between the
Conway--Guy unit-relation certificates and consecutive gaps in the coherent
Boolean term order induced by the Conway--Guy weights.

Tom Bohman's 1996 theorem that the Conway--Guy rows have distinct subset sums
is still an external input if one wants the induced comparison to be a total
order.  The bridge itself only uses integrality: two subset sums differing by
one have no integer subset sum strictly between them.
-/

@[expose] public section

open scoped BigOperators

namespace BooleanIsoperimetry.CoherentGap

/-- The integer weight of a Boolean-cube vertex. -/
def integerSubsetWeight {n : ℕ} (weights : Relation n) (vertex : Cube n) : ℤ :=
  ∑ coordinate ∈ vertex, weights coordinate

/-- The real weight of a Boolean-cube vertex. -/
def realSubsetWeight {n : ℕ} (weights : Fin n → ℝ) (vertex : Cube n) : ℝ :=
  ∑ coordinate ∈ vertex, weights coordinate

/-- Coordinates with coefficient one in a signed relation. -/
def positiveSupport {n : ℕ} (relation : Relation n) : Cube n :=
  Finset.univ.filter fun coordinate => relation coordinate = 1

/-- Coordinates with coefficient minus one in a signed relation. -/
def negativeSupport {n : ℕ} (relation : Relation n) : Cube n :=
  Finset.univ.filter fun coordinate => relation coordinate = -1

/-- No subset sum lies strictly between the weights of `lower` and `upper`. -/
def IsConsecutiveSubsetGap {n : ℕ} (weights : Relation n)
    (lower upper : Cube n) : Prop :=
  integerSubsetWeight weights lower < integerSubsetWeight weights upper ∧
    ∀ middle,
      ¬(integerSubsetWeight weights lower <
          integerSubsetWeight weights middle ∧
        integerSubsetWeight weights middle <
          integerSubsetWeight weights upper)

/-- Every consecutive gap of a reference integer row has size at least one
when measured by the candidate real row. -/
def SatisfiesNormalizedConsecutiveGaps {n : ℕ} (reference : Relation n)
    (candidate : Fin n → ℝ) : Prop :=
  ∀ lower upper,
    IsConsecutiveSubsetGap reference lower upper →
      1 ≤ realSubsetWeight candidate upper -
        realSubsetWeight candidate lower

/--
@isnad1 id=eq.1h3v.s6.02cf0fda8466 from=translated src=- shape=dd10c45c vocab=d0279872
-/
lemma dot_eq_support_difference {n : ℕ} (weights relation : Relation n)
    (hvalues : ∀ coordinate,
      relation coordinate = -1 ∨
        relation coordinate = 0 ∨ relation coordinate = 1) :
    dot relation weights =
      integerSubsetWeight weights (positiveSupport relation) -
        integerSubsetWeight weights (negativeSupport relation) := by
  classical
  unfold dot integerSubsetWeight positiveSupport negativeSupport
  calc
    (∑ coordinate, relation coordinate * weights coordinate) =
        ∑ coordinate,
          ((if relation coordinate = 1 then weights coordinate else 0) -
            if relation coordinate = -1 then weights coordinate else 0) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rcases hvalues coordinate with hnegative | hzero | hpositive
      · simp [hnegative]
      · simp [hzero]
      · simp [hpositive]
    _ =
        (∑ coordinate,
          if relation coordinate = 1 then weights coordinate else 0) -
          ∑ coordinate,
            if relation coordinate = -1 then weights coordinate else 0 := by
      rw [Finset.sum_sub_distrib]
    _ =
        (∑ coordinate ∈ Finset.univ.filter
          (fun coordinate => relation coordinate = 1), weights coordinate) -
          ∑ coordinate ∈ Finset.univ.filter
            (fun coordinate => relation coordinate = -1), weights coordinate := by
      simp only [Finset.sum_filter]

/--
@isnad1 id=eq.1h3v.s6.939e2d6c5d96 from=translated src=- shape=5bf3ead1 vocab=b9ed1163
-/
lemma realDot_eq_support_difference {n : ℕ} (candidate : Fin n → ℝ)
    (relation : Relation n)
    (hvalues : ∀ coordinate,
      relation coordinate = -1 ∨
        relation coordinate = 0 ∨ relation coordinate = 1) :
    realDot relation candidate =
      realSubsetWeight candidate (positiveSupport relation) -
        realSubsetWeight candidate (negativeSupport relation) := by
  classical
  unfold realDot realSubsetWeight positiveSupport negativeSupport
  calc
    (∑ coordinate, (relation coordinate : ℝ) * candidate coordinate) =
        ∑ coordinate,
          ((if relation coordinate = 1 then candidate coordinate else 0) -
            if relation coordinate = -1 then candidate coordinate else 0) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rcases hvalues coordinate with hnegative | hzero | hpositive
      · simp [hnegative]
      · simp [hzero]
      · simp [hpositive]
    _ =
        (∑ coordinate,
          if relation coordinate = 1 then candidate coordinate else 0) -
          ∑ coordinate,
            if relation coordinate = -1 then candidate coordinate else 0 := by
      rw [Finset.sum_sub_distrib]
    _ =
        (∑ coordinate ∈ Finset.univ.filter
          (fun coordinate => relation coordinate = 1), candidate coordinate) -
          ∑ coordinate ∈ Finset.univ.filter
            (fun coordinate => relation coordinate = -1), candidate coordinate := by
      simp only [Finset.sum_filter]

/-- A unit relation is realized by two subsets whose integer weights differ
by exactly one.
@isnad1 id=eq.1h3v.s5.83c5643eca30 from=translated src=- shape=921e353b vocab=a522e6b3
-/
lemma unitRelation_support_gap {n : ℕ} {weights relation : Relation n}
    (hrelation : IsLiftableUnit weights relation) :
    integerSubsetWeight weights (positiveSupport relation) =
      integerSubsetWeight weights (negativeSupport relation) + 1 := by
  have hdot := hrelation.2.1
  rw [dot_eq_support_difference weights relation hrelation.1] at hdot
  omega

/-- Integrality alone makes every realized gap of size one consecutive.
@isnad1 id=isconsec.1h4v.s5.2c0b35b5ae3a from=translated src=- shape=33b2dc4d vocab=7ece44e5
-/
lemma consecutive_of_integer_gap_one {n : ℕ} {weights : Relation n}
    {lower upper : Cube n}
    (hgap : integerSubsetWeight weights upper =
      integerSubsetWeight weights lower + 1) :
    IsConsecutiveSubsetGap weights lower upper := by
  constructor
  · omega
  · intro middle hbetween
    omega

/-- Every liftable unit relation is a consecutive subset-sum gap.
@isnad1 id=isconsec.1h3v.s4.b75de04fd241 from=translated src=- shape=d18b9ec5 vocab=b075e27b
-/
theorem unitRelation_isConsecutiveSubsetGap {n : ℕ}
    {weights relation : Relation n}
    (hrelation : IsLiftableUnit weights relation) :
    IsConsecutiveSubsetGap weights
      (negativeSupport relation) (positiveSupport relation) :=
  consecutive_of_integer_gap_one (unitRelation_support_gap hrelation)

/-- Normalized consecutive-gap inequalities imply all unit-relation
inequalities used by the rigidity certificate.
@isnad1 id=le.2h4v.s5.23bcfdd6a99a from=translated src=- shape=ca755024 vocab=2cf5fc88
-/
theorem normalizedConsecutiveGaps_imply_unitRelations {n : ℕ}
    {reference : Relation n} {candidate : Fin n → ℝ}
    (hnormalized : SatisfiesNormalizedConsecutiveGaps reference candidate) :
    ∀ relation, IsLiftableUnit reference relation →
      1 ≤ realDot relation candidate := by
  intro relation hrelation
  have hgap := hnormalized (negativeSupport relation) (positiveSupport relation)
    (unitRelation_isConsecutiveSubsetGap hrelation)
  rw [realDot_eq_support_difference candidate relation hrelation.1]
  exact hgap

/-- The Conway--Guy row is a coordinatewise lower bound for every real row
with normalized consecutive gaps relative to its subset sums.
@isnad1 id=le.1h3v.s5.40ae22638caf from=translated src=- shape=8c305a64 vocab=9dd82615
-/
theorem conwayGuyRigidity_of_normalizedConsecutiveGaps {n : ℕ}
    (candidate : Fin n → ℝ)
    (hnormalized : SatisfiesNormalizedConsecutiveGaps
      (conwayGuyArithmetic.tower.weights n) candidate) :
    ∀ coordinate,
      (conwayGuyArithmetic.tower.weights n coordinate : ℝ) ≤
        candidate coordinate :=
  conwayGuyNormalizedChamberRigidity candidate
    (normalizedConsecutiveGaps_imply_unitRelations hnormalized)

end BooleanIsoperimetry.CoherentGap

namespace BooleanIsoperimetry

/-- Public short name for the all-dimensional Conway--Guy gap-rigidity
theorem.
@isnad1 id=le.1h3v.s5.40ae22638caf from=translated src=- shape=8c305a64 vocab=9dd82615
-/
alias conwayGuyGapRigidity :=
  CoherentGap.conwayGuyRigidity_of_normalizedConsecutiveGaps

end BooleanIsoperimetry
