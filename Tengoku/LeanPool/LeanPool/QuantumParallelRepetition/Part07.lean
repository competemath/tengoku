/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import Tengoku.LeanPool.LeanPool.QuantumParallelRepetition.Part06

/-! # Quantum parallel repetition, part 07 -/

@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The finite outcome encoding for DSV density rational heterogeneous actual common stop scheduled.
-/
def dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (i : Fin (L + 1)) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
       DSVUniformDensityThresholdLocalIndex N d) :=
  dSVDensityRationalCompleteStoppedOptionalOutcome
    (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
      width schedule i) N ξ ζ
    (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
      L j.succ i)
    (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
      L j.succ i)

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

private def dSVDensityRationalPureBaseExactFlagBornMass
    {A C : Type*} [Fintype A] [Fintype C] {L : ℕ}
    (alice : A → Fin (L + 1)) (bob : C → Fin (L + 1))
    (z : EuclideanSpace ℂ (A × C))
    (flagAlice flagBob : Fin (L + 1)) : ℝ :=
  ∑ a : A, ∑ c : C,
    ‖z (a, c)‖ ^ 2 *
      if alice a = flagAlice ∧ bob c = flagBob then 1 else 0

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

attribute [local instance] Classical.propDecidable

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def dSVDensityRationalPublicBucketPhysicalCommonRank
    {N : ℕ} (r s : Fin (N + 1)) : Fin (N + 1) :=
  ⟨min r.val s.val, by
    have left := r.isLt
    have right := s.isLt
    omega⟩

private def dSVDensityRationalPublicBucketPhysicalPhaseWeightedMixedError
    {d N n B : ℕ} (Q : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ) : ℝ :=
  ∑ phase : Fin B,
    dSVDensityRationalPublicLogRankPhaseWeight B phase *
      ∑ i : Fin d, ∑ j : Fin d,
        (dSVDensityRationalPrefixHarmonicSpectralOverlap
          ξ ζ i j / ((d : ℝ) * (N : ℝ))) *
          ‖localUnitaryAction
              (A phase
                (dSVDensityRationalPublicLogRankBucket Q phase
                  (dSVDensityRationalPhysicalAcceptedRank
                    w N ξ i)))
              (C phase
                (dSVDensityRationalPublicLogRankBucket Q phase
                  (dSVDensityRationalPhysicalAcceptedRank
                    w N ζ j)))
              (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                n
                (dSVDensityRationalPhysicalMixedAcceptedPrefixWork
                  w N ξ ζ i j)) -
            Real.sqrt
                ((dSVDensityRationalPhysicalAcceptedRank
                  w N ξ i).val : ℝ) •
              embezzlementState (N * n)‖ ^ 2

/-- The quantum state representing DSV density rational public bucket physical coherent mixed. -/
def dSVDensityRationalPublicBucketPhysicalCoherentMixedState
    {d N B : ℕ} (w : ℝ) (n : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin (N * n)) ×
       (Σ _ : Fin B × Fin d, Fin (N * n))) :=
  dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
    (dSVDensityRationalLocalSpectralPairHistory N ξ ζ)
    (fun _ i j =>
      dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor n
        (dSVDensityRationalPhysicalMixedAcceptedPrefixWork
          w N ξ ζ i j))

/-- The quantum state representing DSV density rational public bucket physical coherent target. -/
def dSVDensityRationalPublicBucketPhysicalCoherentTargetState
    {d N B : ℕ} (w : ℝ) (n : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin (N * n)) ×
       (Σ _ : Fin B × Fin d, Fin (N * n))) :=
  dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
    (dSVDensityRationalLocalSpectralPairHistory N ξ ζ)
    (fun _ i _ =>
      Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) •
        embezzlementState (N * n))

/--
The DSV density rational public bucket physical coherent local reset construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
    {d N B n : ℕ} (Q : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin (N * n)) ×
       (Σ _ : Fin B × Fin d, Fin (N * n)))) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin (N * n)) ×
       (Σ _ : Fin B × Fin d, Fin (N * n))) :=
  dSVUniformDensityPhysicalAsyncSigmaContinuation
    (fun q : Fin B × Fin d =>
      A q.1
        (dSVDensityRationalPublicLogRankBucket Q q.1
          (dSVDensityRationalPhysicalAcceptedRank
            w N ξ q.2)))
    (fun q : Fin B × Fin d =>
      C q.1
        (dSVDensityRationalPublicLogRankBucket Q q.1
          (dSVDensityRationalPhysicalAcceptedRank
            w N ζ q.2))) z

end

section

open scoped BigOperators

end

section

open scoped BigOperators ComplexOrder MatrixOrder

private def dSVDensityRationalPublicLogRankPhaseWeightedCrossing
    {N : ℕ} (Q B : ℕ) (r s : Fin (N + 1)) : ℝ :=
  ∑ phase : Fin B,
    dSVDensityRationalPublicLogRankPhaseWeight B phase *
      (if
        dSVDensityRationalPublicLogRankBucket Q phase r =
          dSVDensityRationalPublicLogRankBucket Q phase s
       then (0 : ℝ) else 1)

end

section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : ℝ :=
  dSVDensityRationalPrefixHarmonicSpectralOverlap ξ ζ i j /
    ((d : ℝ) * (N : ℝ))

private def dSVDensityRationalHeterogeneousCommonStopSpectralRankGap
    {d : ℕ} (N : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
      N ξ ζ i j *
      |((dSVDensityRationalPhysicalAcceptedRank w N ξ i).val : ℝ) -
        ((dSVDensityRationalPhysicalAcceptedRank w N ζ j).val : ℝ)|

private def dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass
    {d : ℕ} (N : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
      N ξ ζ i j *
      ((dSVDensityRationalPhysicalAcceptedRank w N ξ i).val : ℝ)

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

/--
The DSV density rational heterogeneous common stop gauge stage error construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousCommonStopGaugeStageError
    {d N B : ℕ} (Q : ℕ) (w : ℝ) (n : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ) : ℝ :=
  ‖dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
        Q w ξ ζ A C
        (dSVDensityRationalPublicBucketPhysicalCoherentMixedState
          (N := N) (B := B) w n ξ ζ) -
      dSVDensityRationalPublicBucketPhysicalCoherentTargetState
        (N := N) (B := B) w n ξ ζ‖ ^ 2

private def dSVDensityRationalHeterogeneousStoppedCommonStopGaugeError
    {d N B S L : ℕ} (Q : ℕ) (n : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ) : ℝ :=
  ∑ k : Fin L,
    dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ k.val *
      dSVDensityRationalHeterogeneousCommonStopGaugeStageError
        Q (width (schedule k)) n ξ ζ A C

/-- The joint failure vector at a stage preceding the stopping position. -/
def dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (i : Fin j.val) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
       DSVUniformDensityThresholdLocalIndex N d) :=
  dSVDensityRationalCompleteProjectiveOutcome
    (width (schedule ⟨i.val, lt_trans i.isLt j.isLt⟩))
    N ξ ζ false false

/--
The state vector representing DSV density rational heterogeneous stopped common prefix failure.
-/
def dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) :
    EuclideanSpace ℂ
      (Fin j.val →
        (DSVUniformDensityThresholdLocalIndex N d ×
         DSVUniformDensityThresholdLocalIndex N d)) :=
  finiteTensorVector
    (dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy
      width schedule ξ ζ j)

/--
The DSV density rational heterogeneous stopped common prefix hazard construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
    {d N B S L : ℕ} (Q n : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ) : ℝ :=
  ∑ j : Fin L,
    ‖dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
          (N := N) width schedule ξ ζ j‖ ^ 2 *
      dSVDensityRationalHeterogeneousCommonStopGaugeStageError
        Q (width (schedule j)) n ξ ζ A C

end

section

private def unconditionalPublicBucketLoss
    (B Q : ℕ) (asynchronous precision : ℝ) : ℝ :=
  (10 + 8 * ((Q : ℝ) / (B : ℝ))) * asynchronous +
    (4 * precision ^ 2 +
      16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
      8 / (B : ℝ))

/--
The unconditional prefactor bucket coefficient construction used in the quantum parallel-
repetition argument.
-/
def unconditionalPrefactorBucketCoefficient : ℝ :=
  16 * (Real.exp 1 - 1) + 4

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactLocalQuestionHistoryEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    (LocalQuestionContext X Y D ×
      ExactHistoryFlag X Y A B D) ≃
      ExactLocallySampleableTuple X Y A B D where
  toFun t := (t.1.1, t.1.2.1, t.1.2.2, t.2)
  invFun t := ((t.1, t.2.1, t.2.2.1), t.2.2.2)
  left_inv t := by
    rcases t with ⟨⟨i, x, y⟩, r⟩
    rfl
  right_inv t := by
    rcases t with ⟨i, x, y, r⟩
    rfl

/--
The exact locally sampleable ja rounded construction used in the quantum parallel-repetition
argument.
-/
def exactLocallySampleableJARounded
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  G.questionWeight t.2.1 t.2.2.1 *
    ((numerator (.inl (t.1, t.2.1)) t.2.2.2 : ℝ) /
      denominator) /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

/--
The exact locally sampleable jb rounded construction used in the quantum parallel-repetition
argument.
-/
def exactLocallySampleableJBRounded
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  G.questionWeight t.2.1 t.2.2.1 *
    ((numerator (.inr (t.1, t.2.2.1)) t.2.2.2 : ℝ) /
      denominator) /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

/--
The exact locally sampleable permutation mismatch construction used in the quantum parallel-
repetition argument.
-/
def exactLocallySampleablePermutationMismatch
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty) : ℝ :=
  ∑ c : LocalQuestionContext X Y D,
    localQuestionWeight G n D c *
      uniformPermutationProbability
        (fun permutation :
          Equiv.Perm
            (ExactHistoryFlag X Y A B D × Fin denominator) =>
          rationalPermutationOutput denominator
              (numerator (.inl (c.1, c.2.1)))
              (nonempty (.inl (c.1, c.2.1))) permutation ≠
            rationalPermutationOutput denominator
              (numerator (.inr (c.1, c.2.2)))
              (nonempty (.inr (c.1, c.2.2))) permutation)

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The type used to represent exact source shared flag in the exact sampling construction. -/
abbrev ExactSourceSharedFlag
    (X Y A B : Type)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ) :=
  SourceRemainingCoordinate D ×
    Equiv.Perm
      (ExactHistoryFlag X Y A B D × Fin denominator)

/-- The probability weight for exact source shared flag. -/
def exactSourceSharedFlagWeight
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (_ : ExactSourceSharedFlag X Y A B D denominator) : ℝ :=
  (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        (ExactHistoryFlag X Y A B D × Fin denominator)) : ℝ))

/-- The transcript representation for exact source alice permutation. -/
def exactSourceAlicePermutationHistory
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (j : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) : ExactHistoryFlag X Y A B D :=
  rationalPermutationOutput denominator
    (numerator (.inl (j.1, x)))
    (nonempty (.inl (j.1, x))) j.2

/-- The transcript representation for exact source bob permutation. -/
def exactSourceBobPermutationHistory
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (j : ExactSourceSharedFlag X Y A B D denominator)
    (y : Y) : ExactHistoryFlag X Y A B D :=
  rationalPermutationOutput denominator
    (numerator (.inr (j.1, y)))
    (nonempty (.inr (j.1, y))) j.2

/--
The exact source permutation matched construction used in the quantum parallel-repetition
argument.
-/
def exactSourcePermutationMatched
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (ω : ExactSourceSharedFlag X Y A B D denominator ×
      (X × Y)) : Bool := by
  classical
  exact decide
    (exactSourceAlicePermutationHistory
      D denominator numerator nonempty ω.1 ω.2.1 =
      exactSourceBobPermutationHistory
        D denominator numerator nonempty ω.1 ω.2.2)

/-- The Boolean shared-permutation test reflects equality of the two decoded histories. -/
theorem exactSourcePermutationMatched_eq_true_iff
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (ω : ExactSourceSharedFlag X Y A B D denominator × (X × Y)) :
    exactSourcePermutationMatched D denominator numerator nonempty ω = true ↔
      exactSourceAlicePermutationHistory
          D denominator numerator nonempty ω.1 ω.2.1 =
        exactSourceBobPermutationHistory
          D denominator numerator nonempty ω.1 ω.2.2 := by
  classical
  simp only [exactSourcePermutationMatched, decide_eq_true_eq]

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

private def finiteIndependentProductWeight
    {ι V : Type*} [Fintype ι]
    (q : ι → V → ℝ) (x : ι → V) : ℝ :=
  ∏ i : ι, q i (x i)

private def finiteCoordinateMarginal
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (i : ι) : V → ℝ := by
  classical
  exact groupedMass (fun x : ι → V => x i) p

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def repeatedAlicePostselectedQuestionLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : (Fin n → X) → ℝ := by
  classical
  exact groupedMass
    (fun ω : ExactOutcome X Y A B n => ω.1)
    (repeatedConditionedOutcomeLaw G n S D)

private def repeatedBobPostselectedQuestionLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : (Fin n → Y) → ℝ := by
  classical
  exact groupedMass
    (fun ω : ExactOutcome X Y A B n => ω.2.1)
    (repeatedConditionedOutcomeLaw G n S D)

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

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The information increment contributed by exact conditioned reverse alice prefix entropy. -/
def exactConditionedReverseAlicePrefixEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (k : Fin side.card) : ℝ :=
  reweightedSeedPrefixEntropyIncrement
    (exactReverseAliceConditionalSeedLaw
      (remainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseAliceSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)
    default k

/-- The information increment contributed by exact conditioned reverse bob prefix entropy. -/
def exactConditionedReverseBobPrefixEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (k : Fin side.card) : ℝ :=
  reweightedSeedPrefixEntropyIncrement
    (exactReverseBobConditionalSeedLaw
      (remainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseBobSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)
    default k

/--
The exact conditioned reverse alice prefix information construction used in the quantum
parallel-repetition argument.
-/
def exactConditionedReverseAlicePrefixInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : Y) : ℝ :=
  ∑ side : Finset (SourceRemainingCoordinate D),
    reversePartitionWeight side *
      ((∑ k : Fin side.card,
        exactConditionedReverseAlicePrefixEntropyIncrement
          G n S D remaining side default k) /
        (side.card : ℝ))

/--
The exact conditioned reverse bob prefix information construction used in the quantum parallel-
repetition argument.
-/
def exactConditionedReverseBobPrefixInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X) : ℝ :=
  ∑ side : Finset (SourceRemainingCoordinate D),
    reversePartitionWeight side *
      ((∑ k : Fin side.card,
        exactConditionedReverseBobPrefixEntropyIncrement
          G n S D remaining side default k) /
        (side.card : ℝ))

/--
The exact reverse alice conditional history identification construction used in the quantum
parallel-repetition argument.
-/
def ExactReverseAliceConditionalHistoryIdentification
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D)
    (default : Y) : Prop :=
  exactAliceSourceConditionalInformation G n S D base =
    exactConditionedReverseAlicePrefixInformation
      G n S D remaining default

/--
The exact reverse bob conditional history identification construction used in the quantum
parallel-repetition argument.
-/
def ExactReverseBobConditionalHistoryIdentification
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D)
    (default : X) : Prop :=
  exactBobSourceConditionalInformation G n S D base =
    exactConditionedReverseBobPrefixInformation
      G n S D remaining default

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

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

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The type used to represent exact reverse alice next context in the exact sampling construction.
-/
abbrev ExactReverseAliceNextContext
    (X Y A B : Type*)
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :=
  (ExactReverseAliceFixedInformation X Y D side ×
    ConditionedAnswerFlag A B D) ×
    (Fin side.card → Y)

/-- The type used to represent exact reverse bob next context in the exact sampling construction. -/
abbrev ExactReverseBobNextContext
    (X Y A B : Type*)
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :=
  (ExactReverseBobFixedInformation X Y D side ×
    ConditionedAnswerFlag A B D) ×
    (Fin side.card → X)

/--
The exact conditioned reverse alice next joint construction used in the quantum parallel-
repetition argument.
-/
def exactConditionedReverseAliceNextJoint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactReverseAliceNextContext X Y A B D side → ℝ :=
  reweightedSeedPrefixJoint
    (exactReverseAliceConditionalSeedLaw
      (remainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseAliceSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)

/--
The exact conditioned reverse alice next prior construction used in the quantum parallel-
repetition argument.
-/
def exactConditionedReverseAliceNextPrior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactReverseAliceNextContext X Y A B D side → ℝ :=
  reweightedSeedPrefixPrior
    (exactReverseAliceConditionalSeedLaw
      (remainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseAliceSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)

/--
The exact conditioned reverse bob next joint construction used in the quantum parallel-
repetition argument.
-/
def exactConditionedReverseBobNextJoint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactReverseBobNextContext X Y A B D side → ℝ :=
  reweightedSeedPrefixJoint
    (exactReverseBobConditionalSeedLaw
      (remainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseBobSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)

/--
The exact conditioned reverse bob next prior construction used in the quantum parallel-
repetition argument.
-/
def exactConditionedReverseBobNextPrior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactReverseBobNextContext X Y A B D side → ℝ :=
  reweightedSeedPrefixPrior
    (exactReverseBobConditionalSeedLaw
      (remainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseBobSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)

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

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The data context recording exact reverse alice marked history. -/
def exactReverseAliceMarkedHistoryContext
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : Y)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseAliceNextContext X Y A B D
      (exactReverseLeftSide seed) :=
  let side := exactReverseLeftSide seed
  let marker :=
    (exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩
  let projection :=
    exactReverseAliceSourceProjection
      (X := X) (Y := Y) (A := A) (B := B)
      D side (seed, outcome)
  finitePrefixMask default marker.castSucc
    ((projection.1,
      repeatedConditionedAnswerFlag G n S D outcome),
      projection.2)

/-- The data context recording exact reverse bob marked history. -/
def exactReverseBobMarkedHistoryContext
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : X)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseBobNextContext X Y A B D
      (exactReverseRightSide seed) :=
  let side := exactReverseRightSide seed
  let marker :=
    (exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩
  let projection :=
    exactReverseBobSourceProjection
      (X := X) (Y := Y) (A := A) (B := B)
      D side (seed, outcome)
  finitePrefixMask default marker.castSucc
    ((projection.1,
      repeatedConditionedAnswerFlag G n S D outcome),
      projection.2)

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

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

end QuantumParallelRepetition

end
