/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import Tengoku.LeanPool.LeanPool.QuantumParallelRepetition.Part04

/-! # Quantum parallel repetition, part 05 -/

@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The total probability mass of exact fixed bob question. -/
def exactFixedBobQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (fixed : Finset (Fin n))
    (xs : Fin n → X) (known : Fin n → Y) : ℝ :=
  ∑ ys : Fin n → Y,
    if ∀ j : Fin n, j ∈ fixed → ys j = known j then
      (G.repeat n).questionWeight xs ys
    else 0

/-- The total probability mass of exact fixed alice question. -/
def exactFixedAliceQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (fixed : Finset (Fin n))
    (known : Fin n → X) (ys : Fin n → Y) : ℝ :=
  ∑ xs : Fin n → X,
    if ∀ j : Fin n, j ∈ fixed → xs j = known j then
      (G.repeat n).questionWeight xs ys
    else 0

end

section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The exact reverse left side construction used in the quantum parallel-repetition argument. -/
def exactReverseLeftSide
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  insert seed.coordinate
    (exactLeft seed.coordinate seed.partition)

/-- The exact reverse right side construction used in the quantum parallel-repetition argument. -/
def exactReverseRightSide
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  insert seed.coordinate
    (exactRight seed.coordinate seed.partition)

@[simp] theorem exactReverseLeftSide_coordinate_mem
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    seed.coordinate ∈ exactReverseLeftSide seed := by
  simp only [exactReverseLeftSide, mem_insert, true_or]

@[simp] theorem exactReverseRightSide_coordinate_mem
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    seed.coordinate ∈ exactReverseRightSide seed := by
  simp only [exactReverseRightSide, mem_insert, true_or]

theorem exactReverseLeftSide_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    (exactReverseLeftSide seed).card =
      (exactLeft seed.coordinate seed.partition).card + 1 := by
  simp only [exactReverseLeftSide, exactLeft_coordinate_not_mem, not_false_eq_true,
    card_insert_of_notMem, Nat.add_comm]

theorem exactReverseRightSide_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    (exactReverseRightSide seed).card =
      (exactRight seed.coordinate seed.partition).card + 1 := by
  simp only [exactReverseRightSide, exactRight_coordinate_not_mem, not_false_eq_true,
    card_insert_of_notMem, Nat.add_comm]

end

section

open scoped BigOperators

open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

private def exactReverseLeftSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : ℝ :=
  (1 / (2 : ℝ)) *
    reverseMarkedPartitionWeight
      (exactReverseLeftSide seed) seed.coordinate *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈ exactReverseLeftSide seed}) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈
          exactRight seed.coordinate seed.partition}) : ℝ)) *
    (1 /
      ((exactRight
        seed.coordinate seed.partition).card + 1 : ℝ))

private def exactReverseRightSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : ℝ :=
  (1 / (2 : ℝ)) *
    reverseMarkedPartitionWeight
      (exactReverseRightSide seed) seed.coordinate *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈ exactReverseRightSide seed}) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈
          exactLeft seed.coordinate seed.partition}) : ℝ)) *
    (1 /
      ((exactLeft
        seed.coordinate seed.partition).card + 1 : ℝ))

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The exact history accepted construction used in the quantum parallel-repetition argument. -/
def exactHistoryAccepted
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : Prop :=
  ∀ j : {j : Fin n // j ∈ D},
    G.predicate
      (r.history.aliceConditioned j)
      (r.history.bobConditioned j)
      (r.aliceAnswer j)
      (r.bobAnswer j) = true

end

section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The type used to represent exact global history local index in the exact sampling construction.
-/
abbrev ExactGlobalHistoryLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :=
  PUnit.{1} ⊕
    (Σ r : ExactHistoryFlag X Y A B D,
      ExactPaddedLocalIndex G n S D r)

/-- The state vector representing exact global history. -/
def exactGlobalHistoryVector
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r)) :
    EuclideanSpace ℂ
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D) :=
  taggedTensorVector r z

theorem exactGlobalHistoryVector_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r)) :
    ‖exactGlobalHistoryVector G n S D r z‖ = ‖z‖ :=
  taggedTensorVector_norm r z

/--
The exact global history fin reindex construction used in the quantum parallel-repetition
argument.
-/
def exactGlobalHistoryFinReindex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    EuclideanSpace ℂ
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (Fin (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D)) ×
         Fin (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D))) := by
  classical
  exact LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr
      (Fintype.equivFin (ExactGlobalHistoryLocalIndex G n S D))
      (Fintype.equivFin (ExactGlobalHistoryLocalIndex G n S D)))

/--
The exact global history fin gamma construction used in the quantum parallel-repetition
argument.
-/
def exactGlobalHistoryFinGamma
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) (x : X) :
    BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  ⟨exactGlobalHistoryFinReindex G n S D
      (exactGlobalHistoryVector G n S D r
        (exactGamma G n S D r x)), by
      rw [LinearIsometryEquiv.norm_map,
        exactGlobalHistoryVector_norm]
      exact normalizeOrDefault_norm _ _
        (exactPaddedDefault_norm G n S D r)⟩

/--
The exact global history fin phi construction used in the quantum parallel-repetition argument.
-/
def exactGlobalHistoryFinPhi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) (y : Y) :
    BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  ⟨exactGlobalHistoryFinReindex G n S D
      (exactGlobalHistoryVector G n S D r
        (exactPhi G n S D r y)), by
      rw [LinearIsometryEquiv.norm_map,
        exactGlobalHistoryVector_norm]
      exact normalizeOrDefault_norm _ _
        (exactPaddedDefault_norm G n S D r)⟩

/--
The exact global history fin psi construction used in the quantum parallel-repetition argument.
-/
def exactGlobalHistoryFinPsi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  ⟨exactGlobalHistoryFinReindex G n S D
      (exactGlobalHistoryVector G n S D r
        (exactPsi G n S D r x y)), by
      rw [LinearIsometryEquiv.norm_map,
        exactGlobalHistoryVector_norm]
      exact normalizeOrDefault_norm _ _
        (exactPaddedDefault_norm G n S D r)⟩

end

section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The type used to represent exact source global state in the exact sampling construction. -/
abbrev ExactSourceGlobalState
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :=
  EuclideanSpace ℂ
    (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) ×
      Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)))

/-- The exact source tuple psi construction used in the quantum parallel-repetition argument. -/
def exactSourceTuplePsi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) :
    ExactSourceGlobalState G n S D :=
  (exactGlobalHistoryFinPsi
    G n S D t.2.2.2 t.2.1 t.2.2.1).val

/-- The exact source tuple gamma construction used in the quantum parallel-repetition argument. -/
def exactSourceTupleGamma
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) :
    ExactSourceGlobalState G n S D :=
  (exactGlobalHistoryFinGamma
    G n S D t.2.2.2 t.2.1).val

/-- The exact source tuple phi construction used in the quantum parallel-repetition argument. -/
def exactSourceTuplePhi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) :
    ExactSourceGlobalState G n S D :=
  (exactGlobalHistoryFinPhi
    G n S D t.2.2.2 t.2.2.1).val

theorem exactSourceTupleGamma_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) :
    ‖exactSourceTupleGamma G n S D t‖ = 1 :=
  (exactGlobalHistoryFinGamma
    G n S D t.2.2.2 t.2.1).property

/-- The numerical bound for exact source state distance. -/
def ExactSourceStateDistanceBound
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (η : ℝ) : Prop :=
  (∑ t : ExactLocallySampleableTuple X Y A B D,
    exactLocallySampleableLaw G n S D t *
      ‖exactSourceTupleGamma G n S D t -
        exactSourceTuplePsi G n S D t‖ ^ 2) ≤ 8 * η ∧
  (∑ t : ExactLocallySampleableTuple X Y A B D,
    exactLocallySampleableLaw G n S D t *
      ‖exactSourceTuplePsi G n S D t -
        exactSourceTuplePhi G n S D t‖ ^ 2) ≤ 8 * η

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- Alice's question-to-mean entropy increment paired with Bob's question filter. -/
def exactFairAliceQuestionEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) (y : Y) : ℝ :=
  bornTracePairing S.state.matrix
    ((∑ x : X, G.conditionalXGivenY y x •
      cfc (fun z : ℝ => z * Real.log z)
        (exactAliceQuestionFilter
          G n S D r.seed r.history r.aliceAnswer x)) -
      cfc (fun z : ℝ => z * Real.log z)
        (exactAliceMeanFilter
          G n S D r.seed r.history r.aliceAnswer y))
    (exactBobQuestionFilter
      G n S D r.seed r.history r.bobAnswer y)

/-- Bob's question-to-mean entropy increment paired with Alice's question filter. -/
def exactFairBobQuestionEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) (x : X) : ℝ :=
  bornTracePairing S.state.matrix
    (exactAliceQuestionFilter
      G n S D r.seed r.history r.aliceAnswer x)
    ((∑ y : Y, G.conditionalYGivenX x y •
      cfc (fun z : ℝ => z * Real.log z)
        (exactBobQuestionFilter
          G n S D r.seed r.history r.bobAnswer y)) -
      cfc (fun z : ℝ => z * Real.log z)
        (exactBobMeanFilter
          G n S D r.seed r.history r.bobAnswer x))

private def exactFairAliceHistoryVariation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ y : Y, ∑ x : X, G.questionWeight x y *
    ‖exactUnnormalizedPsi G n S D r x y -
      exactUnnormalizedPhi G n S D r y‖ ^ 2

private def exactFairBobHistoryVariation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ x : X, ∑ y : Y, G.questionWeight x y *
    ‖exactUnnormalizedPsi G n S D r x y -
      exactUnnormalizedGamma G n S D r x‖ ^ 2

/-- The information increment contributed by exact fair alice history entropy. -/
def exactFairAliceHistoryEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ y : Y, G.marginalY y *
    exactFairAliceQuestionEntropyIncrement G n S D r y

/-- The information increment contributed by exact fair bob history entropy. -/
def exactFairBobHistoryEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ x : X, G.marginalX x *
    exactFairBobQuestionEntropyIncrement G n S D r x

/-- The probability weight for exact fair history prior. -/
def exactFairHistoryPriorWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  exactSeedWeight r.seed *
    exactRevealMass G n D r.seed r.history

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The error rate associated with exact source classical information. -/
def exactSourceClassicalInformationRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  (3 * postselectionLogCost G n S D +
      2 * answerLogCost (A := A) (B := B) D) /
    ((Finset.univ \ D).card : ℝ)

/-- The numerical bound for exact source classical information. -/
def ExactSourceClassicalInformationBound
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : Prop :=
  finiteRelativeEntropy
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableJA G n S D base) ≤
        exactSourceClassicalInformationRate G n S D ∧
    finiteRelativeEntropy
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableJB G n S D base) ≤
        exactSourceClassicalInformationRate G n S D

/-- The finite equivalence encoding exact alice information. -/
def exactAliceInformationEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    ExactLocallySampleableTuple X Y A B D ≃
      (SourceRemainingCoordinate D × X) ×
        (ExactHistoryFlag X Y A B D × Y) where
  toFun t := ((t.1, t.2.1), (t.2.2.2, t.2.2.1))
  invFun t := (t.1.1, t.1.2, t.2.2, t.2.1)
  left_inv t := by
    rcases t with ⟨i, x, y, r⟩
    rfl
  right_inv t := by
    rcases t with ⟨⟨i, x⟩, ⟨r, y⟩⟩
    rfl

/-- The finite equivalence encoding exact bob information. -/
def exactBobInformationEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    ExactLocallySampleableTuple X Y A B D ≃
      (SourceRemainingCoordinate D × Y) ×
        (ExactHistoryFlag X Y A B D × X) where
  toFun t := ((t.1, t.2.2.1), (t.2.2.2, t.2.1))
  invFun t := (t.1.1, t.2.2, t.1.2, t.2.1)
  left_inv t := by
    rcases t with ⟨i, x, y, r⟩
    rfl
  right_inv t := by
    rcases t with ⟨⟨i, y⟩, ⟨r, x⟩⟩
    rfl

/--
The exact alice information posterior construction used in the quantum parallel-repetition
argument.
-/
def exactAliceInformationPosterior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (SourceRemainingCoordinate D × X) ×
      (ExactHistoryFlag X Y A B D × Y) → ℝ :=
  fun t => exactLocallySampleableLaw G n S D
    ((exactAliceInformationEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm t)

/--
The exact alice information reference construction used in the quantum parallel-repetition
argument.
-/
def exactAliceInformationReference
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) :
    (SourceRemainingCoordinate D × X) ×
      (ExactHistoryFlag X Y A B D × Y) → ℝ :=
  fun t => exactLocallySampleableJA G n S D base
    ((exactAliceInformationEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm t)

/--
The exact bob information posterior construction used in the quantum parallel-repetition
argument.
-/
def exactBobInformationPosterior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (SourceRemainingCoordinate D × Y) ×
      (ExactHistoryFlag X Y A B D × X) → ℝ :=
  fun t => exactLocallySampleableLaw G n S D
    ((exactBobInformationEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm t)

/--
The exact bob information reference construction used in the quantum parallel-repetition
argument.
-/
def exactBobInformationReference
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) :
    (SourceRemainingCoordinate D × Y) ×
      (ExactHistoryFlag X Y A B D × X) → ℝ :=
  fun t => exactLocallySampleableJB G n S D base
    ((exactBobInformationEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm t)

/-- The error rate associated with exact source pinsker. -/
def exactSourcePinskerRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  Real.sqrt (exactSourceClassicalInformationRate G n S D / 2)

end

section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The finite equivalence encoding exact source prefix flag. -/
def exactSourcePrefixFlagEquiv
    {Ω V Z : Type*} {h : ℕ} :
    ((Ω × (Fin h → V)) × Z) ≃
      ((Ω × Z) × (Fin h → V)) where
  toFun t := ((t.1.1, t.2), t.1.2)
  invFun t := ((t.1.1, t.2), t.1.2)
  left_inv t := by
    rcases t with ⟨⟨u, values⟩, z⟩
    rfl
  right_inv t := by
    rcases t with ⟨⟨u, z⟩, values⟩
    rfl

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The marginal distribution of exact alice question prior. -/
def exactAliceQuestionPriorMarginal
    (G : Game X Y A B) (x : X) : ℝ :=
  ∑ y : Y, G.questionWeight x y

/-- The marginal distribution of exact bob question prior. -/
def exactBobQuestionPriorMarginal
    (G : Game X Y A B) (y : Y) : ℝ :=
  ∑ x : X, G.questionWeight x y

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactGroupedMass_decidableEq_irrel
    {Ω κ : Type*} [Fintype Ω]
    (first second : DecidableEq κ)
    (projection : Ω → κ) (mass : Ω → ℝ) :
    @groupedMass Ω _ κ first projection mass =
      @groupedMass Ω _ κ second projection mass := by
  have h : first = second := Subsingleton.elim first second
  subst second
  rfl

/-- Grouped masses agree when their projections and source weights agree, independently of
the chosen decidable-equality implementations on the target. -/
theorem exactGroupedMass_congr
    {Ω κ : Type*} [Fintype Ω]
    (first second : DecidableEq κ)
    (projection₁ projection₂ : Ω → κ) (mass₁ mass₂ : Ω → ℝ)
    (projection_eq : projection₁ = projection₂)
    (mass_eq : mass₁ = mass₂) :
    @groupedMass Ω _ κ first projection₁ mass₁ =
      @groupedMass Ω _ κ second projection₂ mass₂ := by
  subst projection₂
  subst mass₂
  exact exactGroupedMass_decidableEq_irrel first second projection₁ mass₁

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The exact alice source marginal information construction used in the quantum parallel-repetition
argument.
-/
def exactAliceSourceMarginalInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : ℝ :=
  finiteRelativeEntropy
    (jointFirstMarginal
      (exactAliceInformationPosterior G n S D))
    (jointFirstMarginal
      (exactAliceInformationReference G n S D base))

/--
The exact bob source marginal information construction used in the quantum parallel-repetition
argument.
-/
def exactBobSourceMarginalInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : ℝ :=
  finiteRelativeEntropy
    (jointFirstMarginal
      (exactBobInformationPosterior G n S D))
    (jointFirstMarginal
      (exactBobInformationReference G n S D base))

/--
The exact alice source conditional information construction used in the quantum parallel-
repetition argument.
-/
def exactAliceSourceConditionalInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ ix : SourceRemainingCoordinate D × X,
    jointFirstMarginal
        (exactAliceInformationPosterior G n S D) ix *
      finiteRelativeEntropy
        (jointConditional
          (exactAliceInformationPosterior G n S D) ix)
        (jointConditional
          (exactAliceInformationReference G n S D base) ix)

/--
The exact bob source conditional information construction used in the quantum parallel-
repetition argument.
-/
def exactBobSourceConditionalInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ iy : SourceRemainingCoordinate D × Y,
    jointFirstMarginal
        (exactBobInformationPosterior G n S D) iy *
      finiteRelativeEntropy
        (jointConditional
          (exactBobInformationPosterior G n S D) iy)
        (jointConditional
          (exactBobInformationReference G n S D base) iy)

end

section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Extend a side ranking by inserting the new coordinate at the chosen cut. -/
def exactInsertedRank
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) :
    {j : M // j ∈ insert i side} ≃ Fin (side.card + 1) :=
  (Finset.subtypeInsertEquivOption not_mem).trans
    ((Equiv.optionCongr rank).trans (finSuccEquiv' cut).symm)

@[simp] private theorem exactInsertedRank_marker
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) :
    exactInsertedRank i side not_mem rank cut
      ⟨i, Finset.mem_insert_self i side⟩ = cut := by
  simp only [exactInsertedRank, subtypeInsertEquivOption, Equiv.trans_apply, Equiv.coe_fn_mk,
    ↓reduceDIte, Equiv.optionCongr_apply, Option.map_none, finSuccEquiv'_symm_none]

private theorem exactInsertedRank_old
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1))
    (j : {j : M // j ∈ side}) :
    exactInsertedRank i side not_mem rank cut
      ⟨j.val, Finset.mem_insert_of_mem j.property⟩ =
      cut.succAbove (rank j) := by
  have hne : j.val ≠ i := by
    intro h
    exact not_mem (h ▸ j.property)
  simp only [exactInsertedRank, subtypeInsertEquivOption, Equiv.trans_apply, Equiv.coe_fn_mk, hne,
    ↓reduceDIte, Subtype.coe_eta, Equiv.optionCongr_apply, Option.map_some,
    finSuccEquiv'_symm_some]

/-- The rank map for exact reverse left. -/
def exactReverseLeftRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    {j : M // j ∈ exactReverseLeftSide seed} ≃
      Fin ((exactLeft seed.coordinate seed.partition).card + 1) :=
  exactInsertedRank seed.coordinate
    (exactLeft seed.coordinate seed.partition)
    (exactLeft_coordinate_not_mem seed.coordinate seed.partition)
    (exactLeftRank seed) seed.leftCut

/-- The rank map for exact reverse right. -/
def exactReverseRightRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    {j : M // j ∈ exactReverseRightSide seed} ≃
      Fin ((exactRight seed.coordinate seed.partition).card + 1) :=
  exactInsertedRank seed.coordinate
    (exactRight seed.coordinate seed.partition)
    (exactRight_coordinate_not_mem seed.coordinate seed.partition)
    (exactRightRank seed) seed.rightCut

@[simp] theorem exactReverseLeftRank_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseLeftRank seed
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩ =
      seed.leftCut := by
  exact exactInsertedRank_marker
    seed.coordinate
    (exactLeft seed.coordinate seed.partition)
    (exactLeft_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactLeftRank seed) seed.leftCut

@[simp] theorem exactReverseRightRank_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseRightRank seed
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩ =
      seed.rightCut := by
  exact exactInsertedRank_marker
    seed.coordinate
    (exactRight seed.coordinate seed.partition)
    (exactRight_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactRightRank seed) seed.rightCut

theorem exactReverseLeftRank_old
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M)
    (j : {j : M //
      j ∈ exactLeft seed.coordinate seed.partition}) :
    exactReverseLeftRank seed
      ⟨j.val, Finset.mem_insert_of_mem j.property⟩ =
      seed.leftCut.succAbove (exactLeftRank seed j) := by
  exact exactInsertedRank_old
    seed.coordinate
    (exactLeft seed.coordinate seed.partition)
    (exactLeft_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactLeftRank seed) seed.leftCut j

theorem exactReverseRightRank_old
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M)
    (j : {j : M //
      j ∈ exactRight seed.coordinate seed.partition}) :
    exactReverseRightRank seed
      ⟨j.val, Finset.mem_insert_of_mem j.property⟩ =
      seed.rightCut.succAbove (exactRightRank seed j) := by
  exact exactInsertedRank_old
    seed.coordinate
    (exactRight seed.coordinate seed.partition)
    (exactRight_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactRightRank seed) seed.rightCut j

private def exactInsertedPrefixBefore
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) : Finset M :=
  (Finset.univ.filter
    (fun j : {j : M // j ∈ insert i side} =>
      (exactInsertedRank i side not_mem rank cut j).val <
        cut.val)).image Subtype.val

private def exactReverseLeftPrefixBeforeMarked
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  exactInsertedPrefixBefore seed.coordinate
    (exactLeft seed.coordinate seed.partition)
    (exactLeft_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactLeftRank seed) seed.leftCut

private def exactReverseRightPrefixBeforeMarked
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  exactInsertedPrefixBefore seed.coordinate
    (exactRight seed.coordinate seed.partition)
    (exactRight_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactRightRank seed) seed.rightCut

end

section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The exact ordered side prefix construction used in the quantum parallel-repetition argument. -/
def exactOrderedSidePrefix
    {M : Type*} [DecidableEq M]
    (side : Finset M)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) : Finset M :=
  (Finset.univ.filter
    (fun j : {j : M // j ∈ side} =>
      (rank j).val < cut.val)).image Subtype.val

/-- The information retained when decoding one side of a reverse seed. -/
structure ExactReverseSideContext
    (M : Type*) [Fintype M] [DecidableEq M]
    (side : Finset M) where
  /-- The coordinates on the opposite side of the partition. -/
  otherSide : Finset M
  /-- The rank equivalence for the decoded side. -/
  sideRank : {j : M // j ∈ side} ≃ Fin side.card
  /-- The rank equivalence for the opposite side. -/
  otherRank : {j : M // j ∈ otherSide} ≃ Fin otherSide.card
  /-- The reveal cut on the opposite side. -/
  otherCut : Fin (otherSide.card + 1)
  /-- The partition bit omitted by the reverse encoding. -/
  ignoredBit : Bool
  otherSide_eq_complement : otherSide = Finset.univ \ side
  deriving Fintype

/--
The exact reverse context other prefix construction used in the quantum parallel-repetition
argument.
-/
def exactReverseContextOtherPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    {side : Finset M}
    (context : ExactReverseSideContext M side) : Finset M :=
  exactOrderedSidePrefix
    context.otherSide context.otherRank context.otherCut

theorem exactReverseLeftSide_complement
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactRight seed.coordinate seed.partition =
      Finset.univ \ exactReverseLeftSide seed := by
  ext j
  by_cases hcoordinate : j = seed.coordinate
  · subst j
    simp only [exactRight, ne_eq, mem_filter, mem_univ, not_true_eq_false, false_and, and_false,
      exactReverseLeftSide, mem_sdiff, mem_insert, true_or]
  · cases hbit : seed.partition j <;>
      simp [exactRight, exactLeft,
        exactReverseLeftSide, hcoordinate, hbit]

theorem exactReverseRightSide_complement
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactLeft seed.coordinate seed.partition =
      Finset.univ \ exactReverseRightSide seed := by
  ext j
  by_cases hcoordinate : j = seed.coordinate
  · subst j
    simp only [exactLeft, ne_eq, mem_filter, mem_univ, not_true_eq_false, false_and, and_false,
      exactReverseRightSide, mem_sdiff, mem_insert, true_or]
  · cases hbit : seed.partition j <;>
      simp [exactRight, exactLeft,
        exactReverseRightSide, hcoordinate, hbit]

/-- The data context recording exact reverse alice. -/
def exactReverseAliceContext
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    ExactReverseSideContext M
      (exactReverseLeftSide seed) where
  otherSide := exactRight seed.coordinate seed.partition
  sideRank := (exactReverseLeftRank seed).trans
    (finCongr (exactReverseLeftSide_card seed).symm)
  otherRank := exactRightRank seed
  otherCut := seed.rightCut
  ignoredBit := seed.partition seed.coordinate
  otherSide_eq_complement := exactReverseLeftSide_complement seed

/-- The data context recording exact reverse bob. -/
def exactReverseBobContext
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    ExactReverseSideContext M
      (exactReverseRightSide seed) where
  otherSide := exactLeft seed.coordinate seed.partition
  sideRank := (exactReverseRightRank seed).trans
    (finCongr (exactReverseRightSide_card seed).symm)
  otherRank := exactLeftRank seed
  otherCut := seed.leftCut
  ignoredBit := seed.partition seed.coordinate
  otherSide_eq_complement := exactReverseRightSide_complement seed

/-- The data context recording exact default reverse side. -/
def exactDefaultReverseSideContext
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) : ExactReverseSideContext M side where
  otherSide := Finset.univ \ side
  sideRank := Finset.equivFin side
  otherRank := Finset.equivFin (Finset.univ \ side)
  otherCut := 0
  ignoredBit := false
  otherSide_eq_complement := rfl

/--
The exact reverse alice context at construction used in the quantum parallel-repetition
argument.
-/
def exactReverseAliceContextAt
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) :
    ExactReverseSideContext M side :=
  if h : exactReverseLeftSide seed = side then
    h ▸ exactReverseAliceContext seed
  else
    exactDefaultReverseSideContext side

/--
The exact reverse bob context at construction used in the quantum parallel-repetition argument.
-/
def exactReverseBobContextAt
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) :
    ExactReverseSideContext M side :=
  if h : exactReverseRightSide seed = side then
    h ▸ exactReverseBobContext seed
  else
    exactDefaultReverseSideContext side

@[simp] theorem exactReverseAliceContextAt_actual
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseAliceContextAt
        (exactReverseLeftSide seed) seed =
      exactReverseAliceContext seed := by
  simp only [exactReverseAliceContextAt, ↓reduceDIte]

@[simp] theorem exactReverseBobContextAt_actual
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseBobContextAt
        (exactReverseRightSide seed) seed =
      exactReverseBobContext seed := by
  simp only [exactReverseBobContextAt, ↓reduceDIte]

@[simp] theorem exactReverseAliceContext_otherPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseContextOtherPrefix
        (exactReverseAliceContext seed) =
      exactRightPrefix seed := by
  rfl

@[simp] theorem exactReverseBobContext_otherPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseContextOtherPrefix
        (exactReverseBobContext seed) =
      exactLeftPrefix seed := by
  rfl

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The type used to represent exact reverse alice fixed information in the exact sampling
construction.
-/
abbrev ExactReverseAliceFixedInformation
    (X Y : Type*)
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :=
  Σ context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side,
    ({j : Fin n // j ∈ D} → X) ×
    ({j : Fin n // j ∈ D} → Y) ×
    ({j : SourceRemainingCoordinate D // j ∈ side} → X) ×
    ({j : SourceRemainingCoordinate D // j ∈ context.otherSide} → Y) ×
    ({j : SourceRemainingCoordinate D //
        j ∈ exactReverseContextOtherPrefix context} → X)

/--
The type used to represent exact reverse bob fixed information in the exact sampling
construction.
-/
abbrev ExactReverseBobFixedInformation
    (X Y : Type*)
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :=
  Σ context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side,
    ({j : Fin n // j ∈ D} → X) ×
    ({j : Fin n // j ∈ D} → Y) ×
    ({j : SourceRemainingCoordinate D // j ∈ side} → Y) ×
    ({j : SourceRemainingCoordinate D // j ∈ context.otherSide} → X) ×
    ({j : SourceRemainingCoordinate D //
        j ∈ exactReverseContextOtherPrefix context} → Y)

/-- The projection associated with exact reverse alice source. -/
def exactReverseAliceSourceProjection
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactJointOutcome X Y A B D →
      ExactReverseAliceFixedInformation X Y D side ×
        (Fin side.card → Y) :=
  fun q =>
    let context := exactReverseAliceContextAt side q.1
    (⟨context,
       (fun j => q.2.1 j.val),
       (fun j => q.2.2.1 j.val),
       (fun j => q.2.1 j.val.val),
       (fun j => q.2.2.1 j.val.val),
       (fun j => q.2.1 j.val.val)⟩,
      fun k => q.2.2.1 (context.sideRank.symm k).val.val)

/-- The projection associated with exact reverse bob source. -/
def exactReverseBobSourceProjection
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactJointOutcome X Y A B D →
      ExactReverseBobFixedInformation X Y D side ×
        (Fin side.card → X) :=
  fun q =>
    let context := exactReverseBobContextAt side q.1
    (⟨context,
       (fun j => q.2.1 j.val),
       (fun j => q.2.2.1 j.val),
       (fun j => q.2.2.1 j.val.val),
       (fun j => q.2.1 j.val.val),
       (fun j => q.2.2.1 j.val.val)⟩,
      fun k => q.2.1 (context.sideRank.symm k).val.val)

@[simp] theorem exactReverseAliceContext_marked_rank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    ((exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩).val =
      seed.leftCut.val := by
  simp only [exactReverseAliceContext, Equiv.trans_apply, exactReverseLeftRank_coordinate,
    finCongr_apply, Fin.val_cast]

@[simp] theorem exactReverseBobContext_marked_rank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    ((exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩).val =
      seed.rightCut.val := by
  simp only [exactReverseBobContext, Equiv.trans_apply, exactReverseRightRank_coordinate,
    finCongr_apply, Fin.val_cast]

/--
The exact reverse context prefix before construction used in the quantum parallel-repetition
argument.
-/
def exactReverseContextPrefixBefore
    {M : Type*} [Fintype M] [DecidableEq M]
    {side : Finset M}
    (context : ExactReverseSideContext M side)
    (position : Fin side.card) : Finset M :=
  exactOrderedSidePrefix
    side context.sideRank position.castSucc

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

/-- The finite encoding of exact prefix next. -/
def exactPrefixNextCode
    {Ω V : Type*} {h : ℕ}
    (default : V) (k : Fin h) :
    (Ω × (Fin h → V)) → ((Ω × (Fin h → V)) × V) :=
  fun t => (finitePrefixMask default k.castSucc t, t.2 k)

private def exactPrefixNextDecode
    {Ω V : Type*} {h : ℕ}
    (k : Fin h) :
    ((Ω × (Fin h → V)) × V) → (Ω × (Fin h → V)) :=
  fun t => (t.1.1, Function.update t.1.2 k t.2)

end

section

open scoped BigOperators

open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

/-- The reverse partition placing the side on Alice's side, with a free marked bit. -/
def exactReverseAliceCanonicalPartition
    {M : Type*} [DecidableEq M]
    (side : Finset M) (coordinate : M) (ignored : Bool) : M → Bool :=
  fun j => if j = coordinate then ignored
    else if j ∈ side then false else true

theorem exactReverseAliceCanonicalPartition_side
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    insert coordinate
        (exactLeft coordinate
          (exactReverseAliceCanonicalPartition
            side coordinate ignored)) = side := by
  ext j
  by_cases hj : j = coordinate
  · subst j
    simp only [mem_insert, true_or, member]
  · by_cases hs : j ∈ side <;>
      simp [exactLeft,
        exactReverseAliceCanonicalPartition,
        hj, hs]

private theorem exactReverseAliceCanonicalPartition_unique
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (partition : M → Bool)
    (fiber : insert coordinate
      (exactLeft coordinate partition) = side) :
    partition = exactReverseAliceCanonicalPartition
      side coordinate (partition coordinate) := by
  funext j
  by_cases hj : j = coordinate
  · subst j
    simp only [exactReverseAliceCanonicalPartition, ↓reduceIte]
  · cases hb : partition j
    · have hs : j ∈ side := by
        rw [← fiber]
        simp only [exactLeft, ne_eq, mem_insert, hj, mem_filter, mem_univ, not_false_eq_true, hb,
          and_self, or_true]
      simp only [exactReverseAliceCanonicalPartition, hj, ↓reduceIte, hs]
    · have hs : j ∉ side := by
        rw [← fiber]
        simp only [exactLeft, ne_eq, mem_insert, hj, mem_filter, mem_univ, not_false_eq_true, hb,
          Bool.true_eq_false, and_false, or_self]
      simp only [exactReverseAliceCanonicalPartition, hj, ↓reduceIte, hs]

private def exactReverseAlicePartitionFiberEquiv
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) :
    {partition : M → Bool //
      insert coordinate (exactLeft coordinate partition) = side} ≃
        Bool where
  toFun partition := partition.val coordinate
  invFun ignored :=
    ⟨exactReverseAliceCanonicalPartition side coordinate ignored,
      exactReverseAliceCanonicalPartition_side
        side coordinate member ignored⟩
  left_inv partition := by
    apply Subtype.ext
    exact (exactReverseAliceCanonicalPartition_unique
      side coordinate partition.val partition.property).symm
  right_inv ignored := by
    simp only [exactReverseAliceCanonicalPartition, ↓reduceIte]

/-- The reverse partition placing the side on Bob's side, with a free marked bit. -/
def exactReverseBobCanonicalPartition
    {M : Type*} [DecidableEq M]
    (side : Finset M) (coordinate : M) (ignored : Bool) : M → Bool :=
  fun j => if j = coordinate then ignored
    else if j ∈ side then true else false

theorem exactReverseBobCanonicalPartition_side
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    insert coordinate
        (exactRight coordinate
          (exactReverseBobCanonicalPartition
            side coordinate ignored)) = side := by
  ext j
  by_cases hj : j = coordinate
  · subst j
    simp only [mem_insert, true_or, member]
  · by_cases hs : j ∈ side <;>
      simp [exactRight,
        exactReverseBobCanonicalPartition,
        hj, hs]

private theorem exactReverseBobCanonicalPartition_unique
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (partition : M → Bool)
    (fiber : insert coordinate
      (exactRight coordinate partition) = side) :
    partition = exactReverseBobCanonicalPartition
      side coordinate (partition coordinate) := by
  funext j
  by_cases hj : j = coordinate
  · subst j
    simp only [exactReverseBobCanonicalPartition, ↓reduceIte]
  · cases hb : partition j
    · have hs : j ∉ side := by
        rw [← fiber]
        simp only [exactRight, ne_eq, mem_insert, hj, mem_filter, mem_univ, not_false_eq_true, hb,
          Bool.false_eq_true, and_false, or_self]
      simp only [exactReverseBobCanonicalPartition, hj, ↓reduceIte, hs]
    · have hs : j ∈ side := by
        rw [← fiber]
        simp only [exactRight, ne_eq, mem_insert, hj, mem_filter, mem_univ, not_false_eq_true, hb,
          and_self, or_true]
      simp only [exactReverseBobCanonicalPartition, hj, ↓reduceIte, hs]

private def exactReverseBobPartitionFiberEquiv
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) :
    {partition : M → Bool //
      insert coordinate (exactRight coordinate partition) = side} ≃
        Bool where
  toFun partition := partition.val coordinate
  invFun ignored :=
    ⟨exactReverseBobCanonicalPartition side coordinate ignored,
      exactReverseBobCanonicalPartition_side
        side coordinate member ignored⟩
  left_inv partition := by
    apply Subtype.ext
    exact (exactReverseBobCanonicalPartition_unique
      side coordinate partition.val partition.property).symm
  right_inv ignored := by
    simp only [exactReverseBobCanonicalPartition, ↓reduceIte]

theorem exactReverseAlicePartitionFiber_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) :
    Fintype.card
      {partition : M → Bool //
        insert coordinate
          (exactLeft coordinate partition) = side} = 2 := by
  simpa only [Fintype.card_bool] using Fintype.card_congr
    (exactReverseAlicePartitionFiberEquiv
      side coordinate member)

theorem exactReverseBobPartitionFiber_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) :
    Fintype.card
      {partition : M → Bool //
        insert coordinate
          (exactRight coordinate partition) = side} = 2 := by
  simpa only [Fintype.card_bool] using Fintype.card_congr
    (exactReverseBobPartitionFiberEquiv
      side coordinate member)

theorem exactFiniteIndicator_sum
    {T : Type*} [Fintype T]
    (predicate : T → Prop) [DecidablePred predicate]
    (weight : ℝ) :
    (∑ t : T, if predicate t then weight else 0) =
      (Fintype.card {t : T // predicate t} : ℝ) * weight := by
  classical
  calc
    (∑ t : T, if predicate t then weight else 0) =
        (∑ t : T, if predicate t then (1 : ℝ) else 0) * weight := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _
          split_ifs <;> simp
    _ = (Fintype.card {t : T // predicate t} : ℝ) * weight := by
      simp only [sum_boole, Fintype.card_subtype]

theorem exactReverseAlicePartitionFiber_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (weight : ℝ) :
    (∑ partition : M → Bool,
      if insert coordinate
          (exactLeft coordinate partition) = side
      then weight else 0) = 2 * weight := by
  rw [exactFiniteIndicator_sum]
  rw [exactReverseAlicePartitionFiber_card
    side coordinate member]
  norm_num

theorem exactReverseBobPartitionFiber_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (weight : ℝ) :
    (∑ partition : M → Bool,
      if insert coordinate
          (exactRight coordinate partition) = side
      then weight else 0) = 2 * weight := by
  rw [exactFiniteIndicator_sum]
  rw [exactReverseBobPartitionFiber_card
    side coordinate member]
  norm_num

theorem exactReversePartition_orderCut_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) :
    (∑ leftOrder : Equiv.Perm
        {j : M // j ∈ exactLeft coordinate partition},
      ∑ rightOrder : Equiv.Perm
        {j : M // j ∈ exactRight coordinate partition},
      ∑ leftCut : Fin
        ((exactLeft coordinate partition).card + 1),
      ∑ rightCut : Fin
        ((exactRight coordinate partition).card + 1),
        exactSeedWeight
          ⟨coordinate, partition,
            leftOrder, rightOrder, leftCut, rightCut⟩) =
      (1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) := by
  simp only [exactSeedWeight,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_perm, Fintype.card_coe,
    Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  have hleft :
      (0 : ℝ) < ((exactLeft coordinate partition).card + 1) := by
    exact_mod_cast Nat.zero_lt_succ _
  have hright :
      (0 : ℝ) < ((exactRight coordinate partition).card + 1) := by
    exact_mod_cast Nat.zero_lt_succ _
  have hleft_factorial :
      (0 : ℝ) <
        ((exactLeft coordinate partition).card.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hright_factorial :
      (0 : ℝ) <
        ((exactRight coordinate partition).card.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  field_simp [hleft.ne', hright.ne',
    hleft_factorial.ne', hright_factorial.ne']

theorem exactReverseAlicePartition_orderCut_fiber_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M) (partition : M → Bool) :
    (∑ leftOrder : Equiv.Perm
        {j : M // j ∈ exactLeft coordinate partition},
      ∑ rightOrder : Equiv.Perm
        {j : M // j ∈ exactRight coordinate partition},
      ∑ leftCut : Fin
        ((exactLeft coordinate partition).card + 1),
      ∑ rightCut : Fin
        ((exactRight coordinate partition).card + 1),
        if exactReverseLeftSide
              (⟨coordinate, partition,
                leftOrder, rightOrder, leftCut, rightCut⟩ :
                  ExactForwardSeed M) = side
        then exactSeedWeight
          ⟨coordinate, partition,
            leftOrder, rightOrder, leftCut, rightCut⟩
        else 0) =
      if insert coordinate
          (exactLeft coordinate partition) = side
      then (1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ))
      else 0 := by
  by_cases hside :
      insert coordinate
        (exactLeft coordinate partition) = side
  · simpa only [exactReverseLeftSide, hside, ↓reduceIte, one_div, Fintype.card_pi,
      Fintype.card_bool, prod_const, card_univ, Nat.cast_pow, Nat.cast_ofNat] using
      exactReversePartition_orderCut_sum coordinate partition
  · simp only [exactReverseLeftSide, hside, ↓reduceIte, sum_const_zero]

theorem exactReverseBobPartition_orderCut_fiber_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M) (partition : M → Bool) :
    (∑ leftOrder : Equiv.Perm
        {j : M // j ∈ exactLeft coordinate partition},
      ∑ rightOrder : Equiv.Perm
        {j : M // j ∈ exactRight coordinate partition},
      ∑ leftCut : Fin
        ((exactLeft coordinate partition).card + 1),
      ∑ rightCut : Fin
        ((exactRight coordinate partition).card + 1),
        if exactReverseRightSide
              (⟨coordinate, partition,
                leftOrder, rightOrder, leftCut, rightCut⟩ :
                  ExactForwardSeed M) = side
        then exactSeedWeight
          ⟨coordinate, partition,
            leftOrder, rightOrder, leftCut, rightCut⟩
        else 0) =
      if insert coordinate
          (exactRight coordinate partition) = side
      then (1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ))
      else 0 := by
  by_cases hside :
      insert coordinate
        (exactRight coordinate partition) = side
  · simpa only [exactReverseRightSide, hside, ↓reduceIte, one_div, Fintype.card_pi,
      Fintype.card_bool, prod_const, card_univ, Nat.cast_pow, Nat.cast_ofNat] using
      exactReversePartition_orderCut_sum coordinate partition
  · simp only [exactReverseRightSide, hside, ↓reduceIte, sum_const_zero]

theorem exactReverseAliceSide_marginal
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) :
    groupedMass exactReverseLeftSide
        exactSeedWeight side =
      reversePartitionWeight side := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter, exactForwardSeed_sum]
  simp_rw [exactReverseAlicePartition_orderCut_fiber_sum]
  have hcoordinate (coordinate : M) :
      (∑ partition : M → Bool,
        if insert coordinate
            (exactLeft coordinate partition) = side
        then (1 / (Fintype.card M : ℝ)) *
          (1 / (Fintype.card (M → Bool) : ℝ))
        else 0) =
      if coordinate ∈ side
      then 2 * ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)))
      else 0 := by
    by_cases hmember : coordinate ∈ side
    · simp only [hmember, ↓reduceIte]
      exact exactReverseAlicePartitionFiber_sum
        side coordinate hmember
        ((1 / (Fintype.card M : ℝ)) *
          (1 / (Fintype.card (M → Bool) : ℝ)))
    · simp only [hmember, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro partition _
      have hnot :
          insert coordinate
            (exactLeft coordinate partition) ≠ side := by
        intro h
        apply hmember
        rw [← h]
        exact Finset.mem_insert_self _ _
      simp only [hnot, ↓reduceIte]
  simp_rw [hcoordinate]
  rw [exactFiniteIndicator_sum]
  simp only [Fintype.card_coe, Fintype.card_fun,
    Fintype.card_bool, reversePartitionWeight,
    fairPartitionWeight, Nat.cast_pow]
  ring

theorem exactReverseBobSide_marginal
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) :
    groupedMass exactReverseRightSide
        exactSeedWeight side =
      reversePartitionWeight side := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter, exactForwardSeed_sum]
  simp_rw [exactReverseBobPartition_orderCut_fiber_sum]
  have hcoordinate (coordinate : M) :
      (∑ partition : M → Bool,
        if insert coordinate
            (exactRight coordinate partition) = side
        then (1 / (Fintype.card M : ℝ)) *
          (1 / (Fintype.card (M → Bool) : ℝ))
        else 0) =
      if coordinate ∈ side
      then 2 * ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)))
      else 0 := by
    by_cases hmember : coordinate ∈ side
    · simp only [hmember, ↓reduceIte]
      exact exactReverseBobPartitionFiber_sum
        side coordinate hmember
        ((1 / (Fintype.card M : ℝ)) *
          (1 / (Fintype.card (M → Bool) : ℝ)))
    · simp only [hmember, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro partition _
      have hnot :
          insert coordinate
            (exactRight coordinate partition) ≠ side := by
        intro h
        apply hmember
        rw [← h]
        exact Finset.mem_insert_self _ _
      simp only [hnot, ↓reduceIte]
  simp_rw [hcoordinate]
  rw [exactFiniteIndicator_sum]
  simp only [Fintype.card_coe, Fintype.card_fun,
    Fintype.card_bool, reversePartitionWeight,
    fairPartitionWeight, Nat.cast_pow]
  ring

/-- The probability weight for exact reverse alice conditional seed. -/
def exactReverseAliceConditionalSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) : ℝ :=
  if exactReverseLeftSide seed = side then
    exactSeedWeight seed / reversePartitionWeight side
  else 0

/-- The probability weight for exact reverse bob conditional seed. -/
def exactReverseBobConditionalSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) : ℝ :=
  if exactReverseRightSide seed = side then
    exactSeedWeight seed / reversePartitionWeight side
  else 0

theorem exactReverseAliceConditionalSeedWeight_nonneg
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) :
    0 ≤ exactReverseAliceConditionalSeedWeight side seed := by
  unfold exactReverseAliceConditionalSeedWeight
  split_ifs
  · exact div_nonneg (exactSeedWeight_nonneg seed)
      (reversePartitionWeight_nonneg side)
  · exact le_rfl

theorem exactReverseBobConditionalSeedWeight_nonneg
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) :
    0 ≤ exactReverseBobConditionalSeedWeight side seed := by
  unfold exactReverseBobConditionalSeedWeight
  split_ifs
  · exact div_nonneg (exactSeedWeight_nonneg seed)
      (reversePartitionWeight_nonneg side)
  · exact le_rfl

theorem exactReverseAliceConditionalSeedWeight_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (nonempty : side.Nonempty) :
    (∑ seed : ExactForwardSeed M,
      exactReverseAliceConditionalSeedWeight side seed) = 1 := by
  have hM : 0 < Fintype.card M :=
    Fintype.card_pos_iff.mpr ⟨nonempty.choose⟩
  have hside : 0 < reversePartitionWeight side :=
    (reversePartitionWeight_pos_iff hM side).mpr nonempty
  calc
    (∑ seed : ExactForwardSeed M,
        exactReverseAliceConditionalSeedWeight side seed) =
      (∑ seed : ExactForwardSeed M,
        if exactReverseLeftSide seed = side
        then exactSeedWeight seed else 0) /
          reversePartitionWeight side := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro seed _
            unfold exactReverseAliceConditionalSeedWeight
            split_ifs <;> simp
    _ = groupedMass exactReverseLeftSide
        exactSeedWeight side /
          reversePartitionWeight side := by
            unfold groupedMass
            rw [Finset.sum_filter]
    _ = 1 := by
      rw [exactReverseAliceSide_marginal]
      exact div_self hside.ne'

theorem exactReverseBobConditionalSeedWeight_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (nonempty : side.Nonempty) :
    (∑ seed : ExactForwardSeed M,
      exactReverseBobConditionalSeedWeight side seed) = 1 := by
  have hM : 0 < Fintype.card M :=
    Fintype.card_pos_iff.mpr ⟨nonempty.choose⟩
  have hside : 0 < reversePartitionWeight side :=
    (reversePartitionWeight_pos_iff hM side).mpr nonempty
  calc
    (∑ seed : ExactForwardSeed M,
        exactReverseBobConditionalSeedWeight side seed) =
      (∑ seed : ExactForwardSeed M,
        if exactReverseRightSide seed = side
        then exactSeedWeight seed else 0) /
          reversePartitionWeight side := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro seed _
            unfold exactReverseBobConditionalSeedWeight
            split_ifs <;> simp
    _ = groupedMass exactReverseRightSide
        exactSeedWeight side /
          reversePartitionWeight side := by
            unfold groupedMass
            rw [Finset.sum_filter]
    _ = 1 := by
      rw [exactReverseBobSide_marginal]
      exact div_self hside.ne'

/-- The normalized finite law of forward seeds. -/
def exactForwardSeedLaw
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M) :
    FiniteEventLaw (ExactForwardSeed M) where
  weight := exactSeedWeight
  weight_nonneg := exactSeedWeight_nonneg
  weight_sum := exactSeedWeight_sum nonempty

/-- The finite probability law for exact reverse alice conditional seed. -/
def exactReverseAliceConditionalSeedLaw
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) :
    FiniteEventLaw (ExactForwardSeed M) :=
  if hside : side.Nonempty then
    { weight := exactReverseAliceConditionalSeedWeight side
      weight_nonneg :=
        exactReverseAliceConditionalSeedWeight_nonneg side
      weight_sum :=
        exactReverseAliceConditionalSeedWeight_sum side hside }
  else exactForwardSeedLaw nonempty

/-- The finite probability law for exact reverse bob conditional seed. -/
def exactReverseBobConditionalSeedLaw
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) :
    FiniteEventLaw (ExactForwardSeed M) :=
  if hside : side.Nonempty then
    { weight := exactReverseBobConditionalSeedWeight side
      weight_nonneg :=
        exactReverseBobConditionalSeedWeight_nonneg side
      weight_sum :=
        exactReverseBobConditionalSeedWeight_sum side hside }
  else exactForwardSeedLaw nonempty

@[simp] theorem exactReverseAliceConditionalSeedLaw_weight
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) (hside : side.Nonempty)
    (seed : ExactForwardSeed M) :
    (exactReverseAliceConditionalSeedLaw
      nonempty side).weight seed =
      exactReverseAliceConditionalSeedWeight side seed := by
  simp only [exactReverseAliceConditionalSeedLaw, hside, ↓reduceDIte]

@[simp] theorem exactReverseBobConditionalSeedLaw_weight
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) (hside : side.Nonempty)
    (seed : ExactForwardSeed M) :
    (exactReverseBobConditionalSeedLaw
      nonempty side).weight seed =
      exactReverseBobConditionalSeedWeight side seed := by
  simp only [exactReverseBobConditionalSeedLaw, hside, ↓reduceDIte]

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The finite probability law for reweighted seed prior event. -/
def reweightedSeedPriorEventLaw
    {K : Type*} [Fintype K]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n)) :
    FiniteEventLaw (K × ExactOutcome X Y A B n) where
  weight q := seedLaw.weight q.1 *
    (strategyEventLaw (G.repeat n) S).weight q.2
  weight_nonneg q := mul_nonneg
    (seedLaw.weight_nonneg q.1)
    ((strategyEventLaw (G.repeat n) S).weight_nonneg q.2)
  weight_sum := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,
      (strategyEventLaw (G.repeat n) S).weight_sum, mul_one]
    exact seedLaw.weight_sum

/-- The reweighted seed win event construction used in the quantum parallel-repetition argument. -/
def reweightedSeedWinEvent
    {K : Type*} [Fintype K]
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n)) :
    Finset (K × ExactOutcome X Y A B n) :=
  Finset.univ.filter
    (fun q : K × ExactOutcome X Y A B n =>
      q.2 ∈ FiniteEventLaw.winEvent
        (repeatedCoordinateWin G n) D)

/-- The reweighted seed posterior construction used in the quantum parallel-repetition argument. -/
def reweightedSeedPosterior
    {K : Type*} [Fintype K]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    K × ExactOutcome X Y A B n → ℝ :=
  conditionedEventDistribution
    (reweightedSeedPriorEventLaw seedLaw G n S)
    (reweightedSeedWinEvent (K := K) G n D)

/-- The finite probability law for reweighted seed flagged projection. -/
def reweightedSeedFlaggedProjectionLaw
    {K U Z : Type*} [Fintype K]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n → U)
    (flag : K × ExactOutcome X Y A B n → Z) :
    U × Z → ℝ :=
  groupedMass (fun q => (projection q, flag q))
    (reweightedSeedPosterior seedLaw G n S D)

/--
The reweighted seed prefix joint construction used in the quantum parallel-repetition argument.
-/
def reweightedSeedPrefixJoint
    {K Ω V : Type*} [Fintype K]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V)) :
    ((Ω × ConditionedAnswerFlag A B D) ×
      (Fin h → V)) → ℝ :=
  fun t => reweightedSeedFlaggedProjectionLaw
    seedLaw G n S D projection
    (fun q => repeatedConditionedAnswerFlag G n S D q.2)
    ((exactSourcePrefixFlagEquiv
      (Ω := Ω) (V := V)
      (Z := ConditionedAnswerFlag A B D)).symm t)

/--
The reweighted seed prefix prior construction used in the quantum parallel-repetition argument.
-/
def reweightedSeedPrefixPrior
    {K Ω V : Type*} [Fintype K]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V)) :
    ((Ω × ConditionedAnswerFlag A B D) ×
      (Fin h → V)) → ℝ :=
  fun t => uniformFlagReference
    (Z := ConditionedAnswerFlag A B D)
    (groupedMass projection
      (reweightedSeedPriorEventLaw seedLaw G n S).weight)
    ((exactSourcePrefixFlagEquiv
      (Ω := Ω) (V := V)
      (Z := ConditionedAnswerFlag A B D)).symm t)

/-- The information increment contributed by reweighted seed prefix entropy. -/
def reweightedSeedPrefixEntropyIncrement
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (k : Fin h) : ℝ :=
  finitePrefixRelativeEntropy
      (reweightedSeedPrefixJoint
        seedLaw G n S D projection)
      (reweightedSeedPrefixPrior
        seedLaw G n S D projection)
      default k.succ -
    finitePrefixRelativeEntropy
      (reweightedSeedPrefixJoint
        seedLaw G n S D projection)
      (reweightedSeedPrefixPrior
        seedLaw G n S D projection)
      default k.castSucc

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

private def exactReverseSideContextWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    {side : Finset M}
    (context : ExactReverseSideContext M side) : ℝ :=
  (1 / (2 : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm {j : M // j ∈ side}) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm {j : M // j ∈ context.otherSide}) : ℝ)) *
    (1 / (context.otherSide.card + 1 : ℝ))

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

/-- The finite encoding of exact reverse alice marker. -/
def exactReverseAliceMarkerCode
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    Σ side : Finset M,
      ExactReverseSideContext M side × Fin side.card :=
  ⟨exactReverseLeftSide seed,
    exactReverseAliceContext seed,
    (exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩⟩

/-- The finite encoding of exact reverse bob marker. -/
def exactReverseBobMarkerCode
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    Σ side : Finset M,
      ExactReverseSideContext M side × Fin side.card :=
  ⟨exactReverseRightSide seed,
    exactReverseBobContext seed,
    (exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩⟩

@[simp] theorem exactReverseAliceMarkerCode_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    (((exactReverseAliceMarkerCode seed).2.1.sideRank).symm
      (exactReverseAliceMarkerCode seed).2.2).val =
      seed.coordinate := by
  change
    ((exactReverseAliceContext seed).sideRank.symm
      ((exactReverseAliceContext seed).sideRank
        ⟨seed.coordinate, exactReverseLeftSide_coordinate_mem seed⟩)).val =
      seed.coordinate
  exact congrArg Subtype.val
    ((exactReverseAliceContext seed).sideRank.symm_apply_apply
      ⟨seed.coordinate, exactReverseLeftSide_coordinate_mem seed⟩)

@[simp] theorem exactReverseBobMarkerCode_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    (((exactReverseBobMarkerCode seed).2.1.sideRank).symm
      (exactReverseBobMarkerCode seed).2.2).val =
      seed.coordinate := by
  change
    ((exactReverseBobContext seed).sideRank.symm
      ((exactReverseBobContext seed).sideRank
        ⟨seed.coordinate, exactReverseRightSide_coordinate_mem seed⟩)).val =
      seed.coordinate
  exact congrArg Subtype.val
    ((exactReverseBobContext seed).sideRank.symm_apply_apply
      ⟨seed.coordinate, exactReverseRightSide_coordinate_mem seed⟩)

theorem exactReverseAliceMarkerCode_coordinate_injective
    {M : Type*} [Fintype M] [DecidableEq M]
    {a b : ExactForwardSeed M}
    (same : exactReverseAliceMarkerCode a =
      exactReverseAliceMarkerCode b) :
    a.coordinate = b.coordinate := by
  have h := congrArg
    (fun t : Σ side : Finset M,
      ExactReverseSideContext M side × Fin side.card =>
      (t.2.1.sideRank.symm t.2.2).val) same
  simpa only [exactReverseAliceMarkerCode_coordinate] using h

theorem exactReverseBobMarkerCode_coordinate_injective
    {M : Type*} [Fintype M] [DecidableEq M]
    {a b : ExactForwardSeed M}
    (same : exactReverseBobMarkerCode a =
      exactReverseBobMarkerCode b) :
    a.coordinate = b.coordinate := by
  have h := congrArg
    (fun t : Σ side : Finset M,
      ExactReverseSideContext M side × Fin side.card =>
      (t.2.1.sideRank.symm t.2.2).val) same
  simpa only [exactReverseBobMarkerCode_coordinate] using h

theorem exactReverseAliceMarkerCode_partition_injective
    {M : Type*} [Fintype M] [DecidableEq M]
    {a b : ExactForwardSeed M}
    (same : exactReverseAliceMarkerCode a =
      exactReverseAliceMarkerCode b) :
    a.partition = b.partition := by
  have hcoordinate :=
    exactReverseAliceMarkerCode_coordinate_injective same
  have hside :
      exactReverseLeftSide a =
        exactReverseLeftSide b :=
    congrArg Sigma.fst same
  have hbit : a.partition a.coordinate = b.partition b.coordinate := by
    have h := congrArg
      (fun t : Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card =>
        t.2.1.ignoredBit) same
    exact h
  funext j
  by_cases hj : j = a.coordinate
  · subst j
    simpa only [hcoordinate] using hbit
  · have hbj : j ≠ b.coordinate := by
      simpa only [ne_eq, hcoordinate] using hj
    have hm :
        (a.partition j = false) ↔ (b.partition j = false) := by
      have := Finset.ext_iff.mp hside j
      simpa only [Bool.coe_false_iff_false, Bool.not_eq_eq_eq_not, Bool.not_not,
        exactReverseLeftSide, exactLeft, ne_eq, mem_insert, hj, mem_filter, mem_univ,
        not_false_eq_true, true_and, false_or, hbj] using this
    cases ha : a.partition j <;>
      cases hb : b.partition j <;>
      simp_all

theorem exactReverseBobMarkerCode_partition_injective
    {M : Type*} [Fintype M] [DecidableEq M]
    {a b : ExactForwardSeed M}
    (same : exactReverseBobMarkerCode a =
      exactReverseBobMarkerCode b) :
    a.partition = b.partition := by
  have hcoordinate :=
    exactReverseBobMarkerCode_coordinate_injective same
  have hside :
      exactReverseRightSide a =
        exactReverseRightSide b :=
    congrArg Sigma.fst same
  have hbit : a.partition a.coordinate = b.partition b.coordinate := by
    have h := congrArg
      (fun t : Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card =>
        t.2.1.ignoredBit) same
    exact h
  funext j
  by_cases hj : j = a.coordinate
  · subst j
    simpa only [hcoordinate] using hbit
  · have hbj : j ≠ b.coordinate := by
      simpa only [ne_eq, hcoordinate] using hj
    have hm :
        (a.partition j = true) ↔ (b.partition j = true) := by
      have := Finset.ext_iff.mp hside j
      simpa only [Bool.coe_iff_coe, exactReverseRightSide, exactRight, ne_eq, mem_insert, hj,
        mem_filter, mem_univ, not_false_eq_true, true_and, false_or, hbj] using this
    cases ha : a.partition j <;>
      cases hb : b.partition j <;>
      simp_all

theorem exactReverseAliceMarkerCode_injective
    {M : Type*} [Fintype M] [DecidableEq M] :
    Function.Injective (exactReverseAliceMarkerCode (M := M)) := by
  intro a b same
  have hcoordinate :=
    exactReverseAliceMarkerCode_coordinate_injective same
  have hpartition :=
    exactReverseAliceMarkerCode_partition_injective same
  rcases a with ⟨i, p, l, r, lc, rc⟩
  rcases b with ⟨j, q, l', r', lc', rc'⟩
  dsimp at hcoordinate hpartition
  subst j
  subst q
  simp only [exactReverseAliceMarkerCode, Sigma.mk.inj_iff] at same
  have hpair := eq_of_heq same.2
  have hctx := congrArg Prod.fst hpair
  have hmarked := congrArg Prod.snd hpair
  have hleftCut : lc = lc' := by
    apply Fin.ext
    have hv := congrArg Fin.val hmarked
    exact
      (exactReverseAliceContext_marked_rank
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)).symm.trans
        (hv.trans
          (exactReverseAliceContext_marked_rank
            ({ coordinate := i, partition := p, leftOrder := l',
               rightOrder := r', leftCut := lc', rightCut := rc' } :
              ExactForwardSeed M)))
  have hrightCut : rc = rc' := by
    apply Fin.ext
    have hv := congrArg
      (fun c : ExactReverseSideContext M
        (exactReverseLeftSide
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M)) => c.otherCut.val) hctx
    exact hv
  subst lc'
  subst rc'
  change
    exactReverseAliceContext
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) =
      exactReverseAliceContext
        ({ coordinate := i, partition := p, leftOrder := l',
           rightOrder := r', leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) at hctx
  have hsideRank := congrArg
    (fun c : ExactReverseSideContext M
      (exactReverseLeftSide
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)) => c.sideRank) hctx
  have hotherRankSigma := congrArg
    (fun c : ExactReverseSideContext M
      (exactReverseLeftSide
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)) =>
      (⟨c.otherSide, c.otherRank⟩ :
        Σ other : Finset M,
          ({j : M // j ∈ other} ≃ Fin other.card))) hctx
  simp only [exactReverseAliceContext,
    Sigma.mk.inj_iff] at hotherRankSigma
  have hotherRank := eq_of_heq hotherRankSigma.2
  have hrightSymm : r.symm = r'.symm := by
    have h := congrArg
      (fun e :
        ({j : M // j ∈ exactRight i p} ≃
          Fin (exactRight i p).card) =>
        e.trans (Finset.equivFin (exactRight i p)).symm)
      hotherRank
    simpa only [exactRightRank, Equiv.trans_assoc, Equiv.self_trans_symm,
      Equiv.trans_refl] using h
  have hright : r = r' := Equiv.symm_bijective.injective hrightSymm
  subst r'
  have hreverseLeftRank :
      exactReverseLeftRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) =
        exactReverseLeftRank
          ({ coordinate := i, partition := p, leftOrder := l',
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) := by
    apply Equiv.ext
    intro j
    apply Fin.ext
    have hsideVal
        (seed : ExactForwardSeed M)
        (k : {k : M // k ∈ exactReverseLeftSide seed}) :
        ((exactReverseAliceContext seed).sideRank k).val =
          (exactReverseLeftRank seed k).val := by
      simp only [exactReverseAliceContext, Equiv.trans_apply,
        finCongr_apply, Fin.val_cast]
    have h := congrArg
      (fun e => (e j).val) hsideRank
    exact
      (hsideVal
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) j).symm.trans
        (h.trans
          (hsideVal
            ({ coordinate := i, partition := p, leftOrder := l',
               rightOrder := r, leftCut := lc, rightCut := rc } :
              ExactForwardSeed M) j))
  have hleftRank :
      exactLeftRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) =
        exactLeftRank
          ({ coordinate := i, partition := p, leftOrder := l',
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) := by
    apply Equiv.ext
    intro j
    let j' :
        {j : M //
          j ∈ exactLeft i p} := ⟨j.val, j.property⟩
    have h := congrArg
      (fun e => e
        ⟨j.val, Finset.mem_insert_of_mem j.property⟩)
      hreverseLeftRank
    apply Fin.succAbove_right_injective
    exact
      (exactReverseLeftRank_old
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) j).symm.trans
        (h.trans
          (exactReverseLeftRank_old
            ({ coordinate := i, partition := p, leftOrder := l',
               rightOrder := r, leftCut := lc, rightCut := rc } :
              ExactForwardSeed M) j'))
  have hleftSymm : l.symm = l'.symm := by
    have h := congrArg
      (fun e :
        ({j : M // j ∈ exactLeft i p} ≃
          Fin (exactLeft i p).card) =>
        e.trans (Finset.equivFin (exactLeft i p)).symm)
      hleftRank
    simpa only [exactLeftRank, Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] using h
  have hleft : l = l' := Equiv.symm_bijective.injective hleftSymm
  subst l'
  rfl

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem exactReverseBobMarkerCode_injective
    {M : Type*} [Fintype M] [DecidableEq M] :
    Function.Injective (exactReverseBobMarkerCode (M := M)) := by
  intro a b same
  have hcoordinate :=
    exactReverseBobMarkerCode_coordinate_injective same
  have hpartition :=
    exactReverseBobMarkerCode_partition_injective same
  rcases a with ⟨i, p, l, r, lc, rc⟩
  rcases b with ⟨j, q, l', r', lc', rc'⟩
  dsimp at hcoordinate hpartition
  subst j
  subst q
  simp only [exactReverseBobMarkerCode, Sigma.mk.inj_iff] at same
  have hpair := eq_of_heq same.2
  have hctx := congrArg Prod.fst hpair
  have hmarked := congrArg Prod.snd hpair
  have hrightCut : rc = rc' := by
    apply Fin.ext
    have hv := congrArg Fin.val hmarked
    exact
      (exactReverseBobContext_marked_rank
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)).symm.trans
        (hv.trans
          (exactReverseBobContext_marked_rank
            ({ coordinate := i, partition := p, leftOrder := l',
               rightOrder := r', leftCut := lc', rightCut := rc' } :
              ExactForwardSeed M)))
  have hleftCut : lc = lc' := by
    apply Fin.ext
    have hv := congrArg
      (fun c : ExactReverseSideContext M
        (exactReverseRightSide
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M)) => c.otherCut.val) hctx
    exact hv
  subst rc'
  subst lc'
  change
    exactReverseBobContext
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) =
      exactReverseBobContext
        ({ coordinate := i, partition := p, leftOrder := l',
           rightOrder := r', leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) at hctx
  have hsideRank := congrArg
    (fun c : ExactReverseSideContext M
      (exactReverseRightSide
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)) => c.sideRank) hctx
  have hotherRankSigma := congrArg
    (fun c : ExactReverseSideContext M
      (exactReverseRightSide
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)) =>
      (⟨c.otherSide, c.otherRank⟩ :
        Σ other : Finset M,
          ({j : M // j ∈ other} ≃ Fin other.card))) hctx
  simp only [exactReverseBobContext,
    Sigma.mk.inj_iff] at hotherRankSigma
  have hotherRank := eq_of_heq hotherRankSigma.2
  have hleftSymm : l.symm = l'.symm := by
    have h := congrArg
      (fun e :
        ({j : M // j ∈ exactLeft i p} ≃
          Fin (exactLeft i p).card) =>
        e.trans (Finset.equivFin (exactLeft i p)).symm)
      hotherRank
    simpa only [exactLeftRank, Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] using h
  have hleft : l = l' := Equiv.symm_bijective.injective hleftSymm
  subst l'
  have hreverseRightRank :
      exactReverseRightRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) =
        exactReverseRightRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r', leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) := by
    apply Equiv.ext
    intro j
    apply Fin.ext
    have hsideVal
        (seed : ExactForwardSeed M)
        (k : {k : M // k ∈ exactReverseRightSide seed}) :
        ((exactReverseBobContext seed).sideRank k).val =
          (exactReverseRightRank seed k).val := by
      simp only [exactReverseBobContext, Equiv.trans_apply,
        finCongr_apply, Fin.val_cast]
    have h := congrArg
      (fun e => (e j).val) hsideRank
    exact
      (hsideVal
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) j).symm.trans
        (h.trans
          (hsideVal
            ({ coordinate := i, partition := p, leftOrder := l,
               rightOrder := r', leftCut := lc, rightCut := rc } :
              ExactForwardSeed M) j))
  have hrightRank :
      exactRightRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) =
        exactRightRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r', leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) := by
    apply Equiv.ext
    intro j
    let j' :
        {j : M //
          j ∈ exactRight i p} := ⟨j.val, j.property⟩
    have h := congrArg
      (fun e => e
        ⟨j.val, Finset.mem_insert_of_mem j.property⟩)
      hreverseRightRank
    apply Fin.succAbove_right_injective
    exact
      (exactReverseRightRank_old
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) j).symm.trans
        (h.trans
          (exactReverseRightRank_old
            ({ coordinate := i, partition := p, leftOrder := l,
               rightOrder := r', leftCut := lc, rightCut := rc } :
              ExactForwardSeed M) j'))
  have hrightSymm : r.symm = r'.symm := by
    have h := congrArg
      (fun e :
        ({j : M // j ∈ exactRight i p} ≃
          Fin (exactRight i p).card) =>
        e.trans (Finset.equivFin (exactRight i p)).symm)
      hrightRank
    simpa only [exactRightRank, Equiv.trans_assoc, Equiv.self_trans_symm,
      Equiv.trans_refl] using h
  have hright : r = r' := Equiv.symm_bijective.injective hrightSymm
  subst r'
  rfl

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

/-- Identify the original side with the inserted side after excluding the new coordinate. -/
def exactInsertedOldSubtypeEquiv
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side) :
    {j : M // j ∈ side} ≃
      {j : {j : M // j ∈ insert i side} // j.val ≠ i} where
  toFun j :=
    ⟨⟨j.val, Finset.mem_insert_of_mem j.property⟩,
      fun same => not_mem (same ▸ j.property)⟩
  invFun j :=
    ⟨j.val.val, (Finset.mem_insert.mp j.val.property).resolve_left
      j.property⟩
  left_inv j := by
    apply Subtype.ext
    rfl
  right_inv j := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Remove the marked coordinate and its cut from an extended side ranking. -/
def exactDeleteMarkedRank
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ insert i side} ≃
      Fin (side.card + 1))
    (cut : Fin (side.card + 1))
    (marked :
      rank ⟨i, Finset.mem_insert_self i side⟩ = cut) :
    {j : M // j ∈ side} ≃ Fin side.card :=
  (exactInsertedOldSubtypeEquiv i side not_mem).trans
    ((rank.subtypeEquiv (p := fun j => j.val ≠ i)
      (q := fun k => k ≠ cut)
      (by
        intro j
        constructor
        · intro distinct same
          apply distinct
          have hrank :
              rank j =
                rank ⟨i, Finset.mem_insert_self i side⟩ := by
            rw [marked]
            exact same
          exact congrArg Subtype.val (rank.injective hrank)
        · intro distinct same
          apply distinct
          have hj : j = ⟨i, Finset.mem_insert_self i side⟩ :=
            Subtype.ext same
          rw [hj, marked])).trans (finSuccAboveEquiv cut).symm)

private theorem exactInsertedRank_deleteMarked
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ insert i side} ≃
      Fin (side.card + 1))
    (cut : Fin (side.card + 1))
    (marked :
      rank ⟨i, Finset.mem_insert_self i side⟩ = cut) :
    exactInsertedRank i side not_mem
        (exactDeleteMarkedRank
          i side not_mem rank cut marked) cut = rank := by
  apply Equiv.ext
  intro j
  by_cases is_marker : j.val = i
  · have hj : j = ⟨i, Finset.mem_insert_self i side⟩ :=
      Subtype.ext is_marker
    rw [hj, exactInsertedRank_marker, marked]
  · have old_member : j.val ∈ side :=
      (Finset.mem_insert.mp j.property).resolve_left is_marker
    let old : {j : M // j ∈ side} := ⟨j.val, old_member⟩
    have hj :
        (⟨old.val, Finset.mem_insert_of_mem old.property⟩ :
          {j : M // j ∈ insert i side}) = j := by
      apply Subtype.ext
      rfl
    rw [← hj, exactInsertedRank_old]
    have distinct :
        rank ⟨old.val, Finset.mem_insert_of_mem old.property⟩ ≠ cut := by
      intro same
      apply is_marker
      have hrank :
          rank ⟨old.val, Finset.mem_insert_of_mem old.property⟩ =
            rank ⟨i, Finset.mem_insert_self i side⟩ := by
        rw [marked]
        exact same
      exact congrArg Subtype.val (rank.injective hrank)
    let deleted : {k : Fin (side.card + 1) // k ≠ cut} :=
      ⟨rank ⟨old.val, Finset.mem_insert_of_mem old.property⟩,
        distinct⟩
    have hdelete :
        exactDeleteMarkedRank
            i side not_mem rank cut marked old =
          (finSuccAboveEquiv cut).symm deleted := by
      rfl
    rw [hdelete]
    have h := (finSuccAboveEquiv cut).apply_symm_apply deleted
    exact congrArg Subtype.val h

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

/-- The side permutation whose inverse followed by the canonical ranking is `rank`. -/
def exactPermutationOfSideRank
    {M : Type*}
    (side : Finset M)
    (rank : {j : M // j ∈ side} ≃ Fin side.card) :
    Equiv.Perm {j : M // j ∈ side} :=
  (rank.trans (Finset.equivFin side).symm).symm

private theorem exactPermutationOfSideRank_rank
    {M : Type*}
    (side : Finset M)
    (rank : {j : M // j ∈ side} ≃ Fin side.card) :
    (exactPermutationOfSideRank side rank).symm.trans
      (Finset.equivFin side) = rank := by
  apply Equiv.ext
  intro j
  simp only [exactPermutationOfSideRank, Equiv.symm_trans, Equiv.symm_symm, Equiv.trans_apply,
    Equiv.apply_symm_apply]

theorem exactReverseAliceCanonicalPartition_otherSide
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    exactRight coordinate
        (exactReverseAliceCanonicalPartition
          side coordinate ignored) =
      Finset.univ \ side := by
  ext j
  by_cases marked : j = coordinate
  · subst j
    simp only [exactRight, ne_eq, mem_filter, mem_univ, not_true_eq_false, false_and, and_false,
      mem_sdiff, member]
  · by_cases belongs : j ∈ side <;>
      simp [exactRight,
        exactReverseAliceCanonicalPartition,
        marked, belongs]

theorem exactReverseBobCanonicalPartition_otherSide
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    exactLeft coordinate
        (exactReverseBobCanonicalPartition
          side coordinate ignored) =
      Finset.univ \ side := by
  ext j
  by_cases marked : j = coordinate
  · subst j
    simp only [exactLeft, ne_eq, mem_filter, mem_univ, not_true_eq_false, false_and, and_false,
      mem_sdiff, member]
  · by_cases belongs : j ∈ side <;>
      simp [exactLeft,
        exactReverseBobCanonicalPartition,
        marked, belongs]

theorem exactReverseAliceCanonicalPartition_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    (exactLeft coordinate
      (exactReverseAliceCanonicalPartition
        side coordinate ignored)).card + 1 = side.card := by
  have h := congrArg Finset.card
    (exactReverseAliceCanonicalPartition_side
      side coordinate member ignored)
  simpa only [exactLeft_coordinate_not_mem, not_false_eq_true, card_insert_of_notMem] using h

theorem exactReverseBobCanonicalPartition_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    (exactRight coordinate
      (exactReverseBobCanonicalPartition
        side coordinate ignored)).card + 1 = side.card := by
  have h := congrArg Finset.card
    (exactReverseBobCanonicalPartition_side
      side coordinate member ignored)
  simpa only [exactRight_coordinate_not_mem, not_false_eq_true, card_insert_of_notMem] using h

/--
The exact reverse alice marker decode construction used in the quantum parallel-repetition
argument.
-/
def exactReverseAliceMarkerDecode
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    ExactForwardSeed M := by
  classical
  let coordinate : M := (context.sideRank.symm marker).val
  have member : coordinate ∈ side :=
    (context.sideRank.symm marker).property
  let partition : M → Bool :=
    exactReverseAliceCanonicalPartition
      side coordinate context.ignoredBit
  have hside :
      insert coordinate (exactLeft coordinate partition) = side :=
    exactReverseAliceCanonicalPartition_side
      side coordinate member context.ignoredBit
  have hcard :
      (exactLeft coordinate partition).card + 1 = side.card :=
    exactReverseAliceCanonicalPartition_card
      side coordinate member context.ignoredBit
  let transportedSide :
      {j : M //
        j ∈ insert coordinate (exactLeft coordinate partition)} ≃
      {j : M // j ∈ side} :=
    Equiv.subtypeEquivRight (fun j => by rw [hside])
  let insertedRank :
      {j : M //
        j ∈ insert coordinate (exactLeft coordinate partition)} ≃
      Fin ((exactLeft coordinate partition).card + 1) :=
    transportedSide.trans
      (context.sideRank.trans (finCongr hcard.symm))
  let leftCut : Fin ((exactLeft coordinate partition).card + 1) :=
    (finCongr hcard.symm) marker
  have marked :
      insertedRank
          ⟨coordinate, Finset.mem_insert_self coordinate
            (exactLeft coordinate partition)⟩ = leftCut := by
    have transported :
        transportedSide
            ⟨coordinate, Finset.mem_insert_self coordinate
              (exactLeft coordinate partition)⟩ =
          context.sideRank.symm marker := by
      apply Subtype.ext
      rfl
    change
      (finCongr hcard.symm)
          (context.sideRank
            (transportedSide
              ⟨coordinate, Finset.mem_insert_self coordinate
                (exactLeft coordinate partition)⟩)) =
        (finCongr hcard.symm) marker
    rw [transported, Equiv.apply_symm_apply]
  let leftRank :
      {j : M // j ∈ exactLeft coordinate partition} ≃
        Fin (exactLeft coordinate partition).card :=
    exactDeleteMarkedRank coordinate
      (exactLeft coordinate partition)
      (exactLeft_coordinate_not_mem coordinate partition)
      insertedRank leftCut marked
  have hother :
      exactRight coordinate partition = context.otherSide := by
    calc
      exactRight coordinate partition =
          Finset.univ \ side :=
        exactReverseAliceCanonicalPartition_otherSide
          side coordinate member context.ignoredBit
      _ = context.otherSide := context.otherSide_eq_complement.symm
  let transportedOther :
      {j : M // j ∈ exactRight coordinate partition} ≃
        {j : M // j ∈ context.otherSide} :=
    Equiv.subtypeEquivRight (fun j => by rw [hother])
  let rightRank :
      {j : M // j ∈ exactRight coordinate partition} ≃
        Fin (exactRight coordinate partition).card :=
    transportedOther.trans
      (context.otherRank.trans
        (finCongr (congrArg Finset.card hother).symm))
  exact
    { coordinate := coordinate
      partition := partition
      leftOrder := exactPermutationOfSideRank
        (exactLeft coordinate partition) leftRank
      rightOrder := exactPermutationOfSideRank
        (exactRight coordinate partition) rightRank
      leftCut := leftCut
      rightCut :=
        (finCongr
          (congrArg (fun s : Finset M => s.card + 1) hother).symm)
          context.otherCut }

/--
The exact reverse bob marker decode construction used in the quantum parallel-repetition
argument.
-/
def exactReverseBobMarkerDecode
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    ExactForwardSeed M := by
  classical
  let coordinate : M := (context.sideRank.symm marker).val
  have member : coordinate ∈ side :=
    (context.sideRank.symm marker).property
  let partition : M → Bool :=
    exactReverseBobCanonicalPartition
      side coordinate context.ignoredBit
  have hside :
      insert coordinate (exactRight coordinate partition) = side :=
    exactReverseBobCanonicalPartition_side
      side coordinate member context.ignoredBit
  have hcard :
      (exactRight coordinate partition).card + 1 = side.card :=
    exactReverseBobCanonicalPartition_card
      side coordinate member context.ignoredBit
  let transportedSide :
      {j : M //
        j ∈ insert coordinate (exactRight coordinate partition)} ≃
      {j : M // j ∈ side} :=
    Equiv.subtypeEquivRight (fun j => by rw [hside])
  let insertedRank :
      {j : M //
        j ∈ insert coordinate (exactRight coordinate partition)} ≃
      Fin ((exactRight coordinate partition).card + 1) :=
    transportedSide.trans
      (context.sideRank.trans (finCongr hcard.symm))
  let rightCut : Fin ((exactRight coordinate partition).card + 1) :=
    (finCongr hcard.symm) marker
  have marked :
      insertedRank
          ⟨coordinate, Finset.mem_insert_self coordinate
            (exactRight coordinate partition)⟩ = rightCut := by
    have transported :
        transportedSide
            ⟨coordinate, Finset.mem_insert_self coordinate
              (exactRight coordinate partition)⟩ =
          context.sideRank.symm marker := by
      apply Subtype.ext
      rfl
    change
      (finCongr hcard.symm)
          (context.sideRank
            (transportedSide
              ⟨coordinate, Finset.mem_insert_self coordinate
                (exactRight coordinate partition)⟩)) =
        (finCongr hcard.symm) marker
    rw [transported, Equiv.apply_symm_apply]
  let rightRank :
      {j : M // j ∈ exactRight coordinate partition} ≃
        Fin (exactRight coordinate partition).card :=
    exactDeleteMarkedRank coordinate
      (exactRight coordinate partition)
      (exactRight_coordinate_not_mem coordinate partition)
      insertedRank rightCut marked
  have hother :
      exactLeft coordinate partition = context.otherSide := by
    calc
      exactLeft coordinate partition =
          Finset.univ \ side :=
        exactReverseBobCanonicalPartition_otherSide
          side coordinate member context.ignoredBit
      _ = context.otherSide := context.otherSide_eq_complement.symm
  let transportedOther :
      {j : M // j ∈ exactLeft coordinate partition} ≃
        {j : M // j ∈ context.otherSide} :=
    Equiv.subtypeEquivRight (fun j => by rw [hother])
  let leftRank :
      {j : M // j ∈ exactLeft coordinate partition} ≃
        Fin (exactLeft coordinate partition).card :=
    transportedOther.trans
      (context.otherRank.trans
        (finCongr (congrArg Finset.card hother).symm))
  exact
    { coordinate := coordinate
      partition := partition
      leftOrder := exactPermutationOfSideRank
        (exactLeft coordinate partition) leftRank
      rightOrder := exactPermutationOfSideRank
        (exactRight coordinate partition) rightRank
      leftCut :=
        (finCongr
          (congrArg (fun s : Finset M => s.card + 1) hother).symm)
          context.otherCut
      rightCut := rightCut }

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

@[simp] theorem exactReverseAliceMarkerDecode_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (exactReverseAliceMarkerDecode
      side context marker).coordinate =
      (context.sideRank.symm marker).val := by
  rfl

@[simp] theorem exactReverseBobMarkerDecode_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (exactReverseBobMarkerDecode
      side context marker).coordinate =
      (context.sideRank.symm marker).val := by
  rfl

@[simp] theorem exactReverseAliceMarkerDecode_side
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    exactReverseLeftSide
        (exactReverseAliceMarkerDecode
          side context marker) = side := by
  change
    insert (context.sideRank.symm marker).val
      (exactLeft (context.sideRank.symm marker).val
        (exactReverseAliceCanonicalPartition
          side (context.sideRank.symm marker).val
          context.ignoredBit)) = side
  exact exactReverseAliceCanonicalPartition_side
    side (context.sideRank.symm marker).val
    (context.sideRank.symm marker).property context.ignoredBit

@[simp] theorem exactReverseBobMarkerDecode_side
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    exactReverseRightSide
        (exactReverseBobMarkerDecode
          side context marker) = side := by
  change
    insert (context.sideRank.symm marker).val
      (exactRight (context.sideRank.symm marker).val
        (exactReverseBobCanonicalPartition
          side (context.sideRank.symm marker).val
          context.ignoredBit)) = side
  exact exactReverseBobCanonicalPartition_side
    side (context.sideRank.symm marker).val
    (context.sideRank.symm marker).property context.ignoredBit

@[simp] theorem exactReverseAliceMarkerDecode_ignoredBit
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (exactReverseAliceMarkerDecode
      side context marker).partition
      (context.sideRank.symm marker).val = context.ignoredBit := by
  simp only [exactReverseAliceMarkerDecode, finCongr_apply, exactReverseAliceCanonicalPartition,
    ↓reduceIte]

@[simp] theorem exactReverseBobMarkerDecode_ignoredBit
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (exactReverseBobMarkerDecode
      side context marker).partition
      (context.sideRank.symm marker).val = context.ignoredBit := by
  simp only [exactReverseBobMarkerDecode, finCongr_apply, exactReverseBobCanonicalPartition,
    ↓reduceIte]

theorem exactSigmaFinCutTransport
    {M : Type*}
    (source target : Finset M) (same : source = target)
    (cut : Fin (target.card + 1)) :
    (⟨source,
        (finCongr
          (congrArg (fun side : Finset M => side.card + 1) same).symm)
          cut⟩ : Σ side : Finset M, Fin (side.card + 1)) =
      ⟨target, cut⟩ := by
  subst target
  simp only [finCongr_refl, Equiv.refl_apply]

theorem exactSigmaSideRankTransport
    {M : Type*}
    (source target : Finset M) (same : source = target)
    (rank : {j : M // j ∈ target} ≃ Fin target.card) :
    (⟨source,
        (Equiv.subtypeEquivRight (fun j => by rw [same])).trans
          (rank.trans (finCongr (congrArg Finset.card same).symm))⟩ :
        Σ side : Finset M, ({j : M // j ∈ side} ≃ Fin side.card)) =
      ⟨target, rank⟩ := by
  subst target
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Equiv.ext
    intro j
    simp only [finCongr_refl, Equiv.trans_refl, Equiv.trans_apply, EmbeddingLike.apply_eq_iff_eq]
    apply Subtype.ext
    rfl

theorem exactReverseAliceMarkerDecode_otherRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactRight
        (exactReverseAliceMarkerDecode
          side context marker).coordinate
        (exactReverseAliceMarkerDecode
          side context marker).partition,
      exactRightRank
        (exactReverseAliceMarkerDecode
          side context marker)⟩ :
        Σ other : Finset M,
          ({j : M // j ∈ other} ≃ Fin other.card)) =
      ⟨context.otherSide, context.otherRank⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseAliceCanonicalPartition
      side coordinate context.ignoredBit
  have other : exactRight coordinate partition =
      context.otherSide := by
    exact (exactReverseAliceCanonicalPartition_otherSide
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit).trans
        context.otherSide_eq_complement.symm
  have transported := exactSigmaSideRankTransport
    (exactRight coordinate partition)
    context.otherSide other context.otherRank
  simpa only [exactReverseAliceMarkerDecode,
    exactRightRank,
    exactPermutationOfSideRank_rank] using transported

theorem exactReverseAliceMarkerDecode_otherCut
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactRight
        (exactReverseAliceMarkerDecode
          side context marker).coordinate
        (exactReverseAliceMarkerDecode
          side context marker).partition,
      (exactReverseAliceMarkerDecode
        side context marker).rightCut⟩ :
        Σ other : Finset M, Fin (other.card + 1)) =
      ⟨context.otherSide, context.otherCut⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseAliceCanonicalPartition
      side coordinate context.ignoredBit
  have other : exactRight coordinate partition =
      context.otherSide := by
    exact (exactReverseAliceCanonicalPartition_otherSide
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit).trans
        context.otherSide_eq_complement.symm
  have transported := exactSigmaFinCutTransport
    (exactRight coordinate partition)
    context.otherSide other context.otherCut
  simpa only [exactReverseAliceMarkerDecode] using transported

theorem exactReverseAliceMarkerDecode_sideRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactReverseLeftSide
        (exactReverseAliceMarkerDecode
          side context marker),
      (exactReverseAliceContext
        (exactReverseAliceMarkerDecode
          side context marker)).sideRank⟩ :
        Σ actualSide : Finset M,
          ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
      ⟨side, context.sideRank⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseAliceCanonicalPartition
      side coordinate context.ignoredBit
  have actual : insert coordinate
      (exactLeft coordinate partition) = side :=
    exactReverseAliceCanonicalPartition_side
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit
  let transportedRank :
      {j : M //
        j ∈ insert coordinate (exactLeft coordinate partition)} ≃
        Fin (insert coordinate (exactLeft coordinate partition)).card :=
    (Equiv.subtypeEquivRight (fun j => by rw [actual])).trans
      (context.sideRank.trans
        (finCongr (congrArg Finset.card actual).symm))
  have transported :
      (⟨insert coordinate (exactLeft coordinate partition),
        transportedRank⟩ :
          Σ actualSide : Finset M,
            ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
        ⟨side, context.sideRank⟩ :=
    exactSigmaSideRankTransport
      (insert coordinate (exactLeft coordinate partition))
      side actual context.sideRank
  calc
    (⟨exactReverseLeftSide
        (exactReverseAliceMarkerDecode side context marker),
      (exactReverseAliceContext
        (exactReverseAliceMarkerDecode
          side context marker)).sideRank⟩ :
        Σ actualSide : Finset M,
          ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
        ⟨insert coordinate (exactLeft coordinate partition),
          transportedRank⟩ := by
            apply Sigma.ext
            · change
                insert (context.sideRank.symm marker).val
                    (exactLeft (context.sideRank.symm marker).val
                      (exactReverseAliceCanonicalPartition
                        side (context.sideRank.symm marker).val
                        context.ignoredBit)) =
                  insert coordinate (exactLeft coordinate partition)
              rfl
            · apply heq_of_eq
              dsimp only [exactReverseAliceMarkerDecode]
              simp only [exactReverseLeftSide,
                exactReverseAliceContext, exactReverseLeftRank, exactLeftRank,
                exactPermutationOfSideRank_rank]
              rw [exactInsertedRank_deleteMarked]
              apply Equiv.ext
              intro j
              apply Fin.ext
              simp only [finCongr_apply, Equiv.trans_apply, Fin.val_cast,
                transportedRank, coordinate, partition]
              rfl
    _ = ⟨side, context.sideRank⟩ := transported

theorem exactReverseAliceMarkerDecode_rightInverse
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    exactReverseAliceMarkerCode
        (exactReverseAliceMarkerDecode
          side context marker) =
      ⟨side, context, marker⟩ := by
  classical
  generalize decoded :
    exactReverseAliceMarkerDecode side context marker = seed
  have sameSide : exactReverseLeftSide seed = side := by
    rw [← decoded]
    exact exactReverseAliceMarkerDecode_side
      side context marker
  subst side
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change
      (exactReverseAliceContext seed,
        (exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩) =
        (context, marker)
    have sameContext : exactReverseAliceContext seed = context := by
      cases context with
      | mk otherSide sideRank otherRank otherCut ignored complement =>
        simp only [exactReverseAliceContext,
          ExactReverseSideContext.mk.injEq]
        let reverseContext : ExactReverseSideContext M
            (exactReverseLeftSide seed) :=
          { otherSide := otherSide
            sideRank := sideRank
            otherRank := otherRank
            otherCut := otherCut
            ignoredBit := ignored
            otherSide_eq_complement := complement }
        have exactSideRank :=
          exactReverseAliceMarkerDecode_sideRank
            (exactReverseLeftSide seed)
            reverseContext marker
        have exactOtherRank :=
          exactReverseAliceMarkerDecode_otherRank
            (exactReverseLeftSide seed)
            reverseContext marker
        have exactOtherCut :=
          exactReverseAliceMarkerDecode_otherCut
            (exactReverseLeftSide seed)
            reverseContext marker
        change
          exactReverseAliceMarkerDecode
              (exactReverseLeftSide seed)
              reverseContext marker = seed at decoded
        rw [decoded] at exactSideRank exactOtherRank exactOtherCut
        refine ⟨(exactReverseLeftSide_complement seed).trans
            complement.symm, ?_, ?_, ?_, ?_⟩
        · exact eq_of_heq (Sigma.mk.inj exactSideRank).2
        · exact (Sigma.mk.inj exactOtherRank).2
        · exact (Sigma.mk.inj exactOtherCut).2
        · have exactIgnored := congrArg
            (fun original : ExactForwardSeed M =>
              original.partition original.coordinate) decoded
          simpa only
            [exactReverseAliceMarkerDecode_coordinate,
              exactReverseAliceMarkerDecode_ignoredBit]
              using exactIgnored.symm
    apply Prod.ext
    · exact sameContext
    · rw [sameContext]
      apply context.sideRank.symm.injective
      change
        context.sideRank.symm
            (context.sideRank ⟨seed.coordinate, _⟩) =
          context.sideRank.symm marker
      rw [Equiv.symm_apply_apply]
      apply Subtype.ext
      have coordinate := congrArg
        (fun original : ExactForwardSeed M => original.coordinate)
        decoded
      simpa only [exactReverseAliceMarkerDecode_coordinate]
        using coordinate.symm

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem exactReverseBobMarkerDecode_otherRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactLeft
        (exactReverseBobMarkerDecode
          side context marker).coordinate
        (exactReverseBobMarkerDecode
          side context marker).partition,
      exactLeftRank
        (exactReverseBobMarkerDecode
          side context marker)⟩ :
        Σ other : Finset M,
          ({j : M // j ∈ other} ≃ Fin other.card)) =
      ⟨context.otherSide, context.otherRank⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseBobCanonicalPartition
      side coordinate context.ignoredBit
  have other : exactLeft coordinate partition =
      context.otherSide := by
    exact (exactReverseBobCanonicalPartition_otherSide
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit).trans
        context.otherSide_eq_complement.symm
  have transported := exactSigmaSideRankTransport
    (exactLeft coordinate partition)
    context.otherSide other context.otherRank
  simpa only [exactReverseBobMarkerDecode,
    exactLeftRank,
    exactPermutationOfSideRank_rank] using transported

theorem exactReverseBobMarkerDecode_otherCut
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactLeft
        (exactReverseBobMarkerDecode
          side context marker).coordinate
        (exactReverseBobMarkerDecode
          side context marker).partition,
      (exactReverseBobMarkerDecode
        side context marker).leftCut⟩ :
        Σ other : Finset M, Fin (other.card + 1)) =
      ⟨context.otherSide, context.otherCut⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseBobCanonicalPartition
      side coordinate context.ignoredBit
  have other : exactLeft coordinate partition =
      context.otherSide := by
    exact (exactReverseBobCanonicalPartition_otherSide
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit).trans
        context.otherSide_eq_complement.symm
  have transported := exactSigmaFinCutTransport
    (exactLeft coordinate partition)
    context.otherSide other context.otherCut
  simpa only [exactReverseBobMarkerDecode] using transported

theorem exactReverseBobMarkerDecode_sideRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactReverseRightSide
        (exactReverseBobMarkerDecode
          side context marker),
      (exactReverseBobContext
        (exactReverseBobMarkerDecode
          side context marker)).sideRank⟩ :
        Σ actualSide : Finset M,
          ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
      ⟨side, context.sideRank⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseBobCanonicalPartition
      side coordinate context.ignoredBit
  have actual : insert coordinate
      (exactRight coordinate partition) = side :=
    exactReverseBobCanonicalPartition_side
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit
  let transportedRank :
      {j : M //
        j ∈ insert coordinate (exactRight coordinate partition)} ≃
        Fin (insert coordinate (exactRight coordinate partition)).card :=
    (Equiv.subtypeEquivRight (fun j => by rw [actual])).trans
      (context.sideRank.trans
        (finCongr (congrArg Finset.card actual).symm))
  have transported :
      (⟨insert coordinate (exactRight coordinate partition),
        transportedRank⟩ :
          Σ actualSide : Finset M,
            ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
        ⟨side, context.sideRank⟩ :=
    exactSigmaSideRankTransport
      (insert coordinate (exactRight coordinate partition))
      side actual context.sideRank
  calc
    (⟨exactReverseRightSide
        (exactReverseBobMarkerDecode side context marker),
      (exactReverseBobContext
        (exactReverseBobMarkerDecode
          side context marker)).sideRank⟩ :
        Σ actualSide : Finset M,
          ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
        ⟨insert coordinate (exactRight coordinate partition),
          transportedRank⟩ := by
            apply Sigma.ext
            · change
                insert (context.sideRank.symm marker).val
                    (exactRight (context.sideRank.symm marker).val
                      (exactReverseBobCanonicalPartition
                        side (context.sideRank.symm marker).val
                        context.ignoredBit)) =
                  insert coordinate (exactRight coordinate partition)
              rfl
            · apply heq_of_eq
              dsimp only [exactReverseBobMarkerDecode]
              simp only [exactReverseRightSide,
                exactReverseBobContext, exactReverseRightRank, exactRightRank,
                exactPermutationOfSideRank_rank]
              rw [exactInsertedRank_deleteMarked]
              apply Equiv.ext
              intro j
              apply Fin.ext
              simp only [finCongr_apply, Equiv.trans_apply, Fin.val_cast,
                transportedRank, coordinate, partition]
              rfl
    _ = ⟨side, context.sideRank⟩ := transported

theorem exactReverseBobMarkerDecode_rightInverse
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    exactReverseBobMarkerCode
        (exactReverseBobMarkerDecode
          side context marker) =
      ⟨side, context, marker⟩ := by
  classical
  generalize decoded :
    exactReverseBobMarkerDecode side context marker = seed
  have sameSide : exactReverseRightSide seed = side := by
    rw [← decoded]
    exact exactReverseBobMarkerDecode_side
      side context marker
  subst side
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change
      (exactReverseBobContext seed,
        (exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩) =
        (context, marker)
    have sameContext : exactReverseBobContext seed = context := by
      cases context with
      | mk otherSide sideRank otherRank otherCut ignored complement =>
        simp only [exactReverseBobContext,
          ExactReverseSideContext.mk.injEq]
        let reverseContext : ExactReverseSideContext M
            (exactReverseRightSide seed) :=
          { otherSide := otherSide
            sideRank := sideRank
            otherRank := otherRank
            otherCut := otherCut
            ignoredBit := ignored
            otherSide_eq_complement := complement }
        have exactSideRank :=
          exactReverseBobMarkerDecode_sideRank
            (exactReverseRightSide seed)
            reverseContext marker
        have exactOtherRank :=
          exactReverseBobMarkerDecode_otherRank
            (exactReverseRightSide seed)
            reverseContext marker
        have exactOtherCut :=
          exactReverseBobMarkerDecode_otherCut
            (exactReverseRightSide seed)
            reverseContext marker
        change
          exactReverseBobMarkerDecode
              (exactReverseRightSide seed)
              reverseContext marker = seed at decoded
        rw [decoded] at exactSideRank exactOtherRank exactOtherCut
        refine ⟨(exactReverseRightSide_complement seed).trans
            complement.symm, ?_, ?_, ?_, ?_⟩
        · exact eq_of_heq (Sigma.mk.inj exactSideRank).2
        · exact (Sigma.mk.inj exactOtherRank).2
        · exact (Sigma.mk.inj exactOtherCut).2
        · have exactIgnored := congrArg
            (fun original : ExactForwardSeed M =>
              original.partition original.coordinate) decoded
          simpa only
            [exactReverseBobMarkerDecode_coordinate,
              exactReverseBobMarkerDecode_ignoredBit]
              using exactIgnored.symm
    apply Prod.ext
    · exact sameContext
    · rw [sameContext]
      apply context.sideRank.symm.injective
      change
        context.sideRank.symm
            (context.sideRank ⟨seed.coordinate, _⟩) =
          context.sideRank.symm marker
      rw [Equiv.symm_apply_apply]
      apply Subtype.ext
      have coordinate := congrArg
        (fun original : ExactForwardSeed M => original.coordinate)
        decoded
      simpa only [exactReverseBobMarkerDecode_coordinate]
        using coordinate.symm

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

/-- The finite equivalence encoding exact reverse alice weighted marker. -/
def exactReverseAliceWeightedMarkerEquiv
    {M : Type*} [Fintype M] [DecidableEq M] :
    ExactForwardSeed M ≃
      (Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card) where
  toFun := exactReverseAliceMarkerCode
  invFun marker :=
    exactReverseAliceMarkerDecode
      marker.1 marker.2.1 marker.2.2
  left_inv seed := by
    apply exactReverseAliceMarkerCode_injective
    exact exactReverseAliceMarkerDecode_rightInverse
      (exactReverseAliceMarkerCode seed).1
      (exactReverseAliceMarkerCode seed).2.1
      (exactReverseAliceMarkerCode seed).2.2
  right_inv marker := by
    rcases marker with ⟨side, context, position⟩
    exact exactReverseAliceMarkerDecode_rightInverse
      side context position

/-- The finite equivalence encoding exact reverse bob weighted marker. -/
def exactReverseBobWeightedMarkerEquiv
    {M : Type*} [Fintype M] [DecidableEq M] :
    ExactForwardSeed M ≃
      (Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card) where
  toFun := exactReverseBobMarkerCode
  invFun marker :=
    exactReverseBobMarkerDecode
      marker.1 marker.2.1 marker.2.2
  left_inv seed := by
    apply exactReverseBobMarkerCode_injective
    exact exactReverseBobMarkerDecode_rightInverse
      (exactReverseBobMarkerCode seed).1
      (exactReverseBobMarkerCode seed).2.1
      (exactReverseBobMarkerCode seed).2.2
  right_inv marker := by
    rcases marker with ⟨side, context, position⟩
    exact exactReverseBobMarkerDecode_rightInverse
      side context position

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The entropy quantity for exact reverse alice filter operator marker. -/
def exactReverseAliceFilterOperatorMarkerEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseBobMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairAliceHistoryEntropyIncrement G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

/-- The entropy quantity for exact reverse bob filter operator marker. -/
def exactReverseBobFilterOperatorMarkerEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseAliceMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairBobHistoryEntropyIncrement G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The potential function controlling exact fair alice history high operator. -/
def exactFairAliceHistoryHighOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ y : Y, G.marginalY y *
    bornTracePairing S.state.matrix
      (∑ x : X, G.conditionalXGivenY y x •
        cfc (fun z : ℝ => z * Real.log z)
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x))
      (exactBobQuestionFilter
        G n S D r.seed r.history r.bobAnswer y)

/-- The potential function controlling exact fair alice history low operator. -/
def exactFairAliceHistoryLowOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ y : Y, G.marginalY y *
    bornTracePairing S.state.matrix
      (cfc (fun z : ℝ => z * Real.log z)
        (exactAliceMeanFilter
          G n S D r.seed r.history r.aliceAnswer y))
      (exactBobQuestionFilter
        G n S D r.seed r.history r.bobAnswer y)

/-- The potential function controlling exact fair bob history high operator. -/
def exactFairBobHistoryHighOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ x : X, G.marginalX x *
    bornTracePairing S.state.matrix
      (exactAliceQuestionFilter
        G n S D r.seed r.history r.aliceAnswer x)
      (∑ y : Y, G.conditionalYGivenX x y •
        cfc (fun z : ℝ => z * Real.log z)
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y))

/-- The potential function controlling exact fair bob history low operator. -/
def exactFairBobHistoryLowOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ x : X, G.marginalX x *
    bornTracePairing S.state.matrix
      (exactAliceQuestionFilter
        G n S D r.seed r.history r.aliceAnswer x)
      (cfc (fun z : ℝ => z * Real.log z)
        (exactBobMeanFilter
          G n S D r.seed r.history r.bobAnswer x))

/-- The potential function controlling exact reverse alice filter high operator. -/
def exactReverseAliceFilterHighOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseBobMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairAliceHistoryHighOperatorPotential G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

/-- The potential function controlling exact reverse alice filter low operator. -/
def exactReverseAliceFilterLowOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseBobMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairAliceHistoryLowOperatorPotential G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

/-- The potential function controlling exact reverse bob filter high operator. -/
def exactReverseBobFilterHighOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseAliceMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairBobHistoryHighOperatorPotential G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

/-- The potential function controlling exact reverse bob filter low operator. -/
def exactReverseBobFilterLowOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseAliceMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairBobHistoryLowOperatorPotential G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactFairQuestionTailWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) : ℝ :=
  ∑ tailX : {j : Fin n // j ≠ seed.coordinate.val} → X,
  ∑ tailY : {j : Fin n // j ≠ seed.coordinate.val} → Y,
    if exactRevealCode D seed
       ((Equiv.funSplitAt seed.coordinate.val X).symm (x, tailX),
        (Equiv.funSplitAt seed.coordinate.val Y).symm (y, tailY)) =
          history
    then ∏ j : {j : Fin n // j ≠ seed.coordinate.val},
      G.questionWeight (tailX j) (tailY j)
    else 0

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The total probability mass of exact fair conditioned answer born. -/
def exactFairConditionedAnswerBornMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
    exactFiberQuestionWeight
      G n D r.seed r.history x y xs ys *
      bornTracePairing S.state.matrix
        (conditionedAliceEffect G n S D r.aliceAnswer xs)
        (conditionedBobEffect G n S D r.bobAnswer ys)

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The total probability mass of exact fair full outcome born. -/
def exactFairFullOutcomeBornMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ o : ExactOutcome X Y A B n,
    if exactLocallySampleableCode D (r.seed, o) =
      (r.seed.coordinate, x, y, r)
    then (strategyEventLaw (G.repeat n) S).weight o
    else 0

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The entropy quantity for exact fair accepted alice. -/
def exactFairAcceptedAliceEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  ∑ r : ExactHistoryFlag X Y A B D,
    if exactHistoryAccepted G n D r then
      exactFairHistoryPriorWeight G n D r *
        exactFairAliceHistoryEntropyIncrement G n S D r
    else 0

/-- The entropy quantity for exact fair accepted bob. -/
def exactFairAcceptedBobEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  ∑ r : ExactHistoryFlag X Y A B D,
    if exactHistoryAccepted G n D r then
      exactFairHistoryPriorWeight G n D r *
        exactFairBobHistoryEntropyIncrement G n S D r
    else 0

private def exactFairAcceptedAliceVariation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  ∑ r : ExactHistoryFlag X Y A B D,
    if exactHistoryAccepted G n D r then
      exactFairHistoryPriorWeight G n D r *
        exactFairAliceHistoryVariation G n S D r
    else 0

private def exactFairAcceptedBobVariation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  ∑ r : ExactHistoryFlag X Y A B D,
    if exactHistoryAccepted G n D r then
      exactFairHistoryPriorWeight G n D r *
        exactFairBobHistoryVariation G n S D r
    else 0

/-- The numerical bound for exact fair operator entropy. -/
def ExactFairOperatorEntropyBound
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (η : ℝ) : Prop :=
  exactFairAcceptedAliceEntropy G n S D ≤
      2 * (repeatedPostselectionMass G n S D * η) ∧
  exactFairAcceptedBobEntropy G n S D ≤
      2 * (repeatedPostselectionMass G n S D * η)

end

end QuantumParallelRepetition

end
