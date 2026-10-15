/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import Tengoku.LeanPool.LeanPool.QuantumParallelRepetition.Part07

/-! # Quantum parallel repetition, part 08 -/

@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The product encoding of exact source alice sample. -/
def exactSourceAliceSampleTuple
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y)) :
    ExactLocallySampleableTuple X Y A B D :=
  (outcome.1.1, outcome.2.1, outcome.2.2,
    exactSourceAlicePermutationHistory
      D denominator numerator nonempty outcome.1 outcome.2.1)

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {Ω T : Type*} [Fintype Ω] [Fintype T] [DecidableEq T]

/-- Reweight each projection fiber to its target mass while retaining its relative weights. -/
def exactFiniteFiberLift
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (outcome : Ω) : ℝ :=
  target (projection outcome) * original outcome /
    groupedMass projection original (projection outcome)

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- Alice's local source measurement obtained by purifying the coordinate refinement. -/
def exactSourceAliceRefinedPOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) :
    POVM A (ExactAliceLocalIndex G n S D r) := by
  classical
  exact purificationAlicePOVM
    (exactAliceRefinedPOVM G n S D r a₀ x)

/-- Bob's local source measurement obtained by purifying the coordinate refinement. -/
def exactSourceBobRefinedPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (b₀ : B) (y : Y) :
    POVM B (ExactBobLocalIndex G n S D r) :=
  exactBobRefinedPOVM G n S D r b₀ y

/-- The tensor product of the two refined local source effects. -/
def exactSourceJointEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) (a : A) (b : B) :
    Matrix
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) ℂ :=
  (exactSourceAliceRefinedPOVM G n S D r a₀ x).effect a ⊗ₖ
    (exactSourceBobRefinedPOVM G n S D r b₀ y).effect b

/-- The sum of refined joint effects over answers accepted by the game predicate. -/
def exactSourceWinningEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    Matrix
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true
    then exactSourceJointEffect G n S D r a₀ b₀ x y a b
    else 0

/-- The continuous linear map implementing exact source winning effect. -/
def exactSourceWinningEffectCLM
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    EuclideanSpace ℂ
        (ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r) →L[ℂ]
      EuclideanSpace ℂ
        (ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r) := by
  classical
  exact Matrix.toEuclideanCLM
    (n := ExactAliceLocalIndex G n S D r ×
      ExactBobLocalIndex G n S D r) (𝕜 := ℂ)
    (exactSourceWinningEffect G n S D r a₀ b₀ x y)

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The postselected mass of outcomes with the specified code that win the selected coordinate. -/
def exactSourceAcceptedCoordinateMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  ∑ q : ExactJointOutcome X Y A B D,
    if exactLocallySampleableCode D q = t ∧
      repeatedCoordinateWin G n q.1.coordinate.val q.2 = true then
      exactPostselectedJointLaw G n S D q
    else 0

/-- The probability of exact source conditional winning. -/
def exactSourceConditionalWinningProbability
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  exactSourceAcceptedCoordinateMass G n S D t /
    exactLocallySampleableLaw G n S D t

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B dA dB : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]

/--
The exact source alice flag coupling construction used in the quantum parallel-repetition
argument.
-/
def exactSourceAliceFlagCoupling
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty) :
    ExactSourceSharedFlag X Y A B D denominator × (X × Y) → ℝ :=
  exactFiniteFiberLift
    (exactSourceAliceSampleTuple
      D denominator numerator nonempty)
    (flaggedQuestionWeight G
      (exactSourceSharedFlagWeight D denominator))
    (exactLocallySampleableLaw G n S D)

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactFairWinningOutcomeBornMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ outcome : ExactOutcome X Y A B n,
    if exactLocallySampleableCode D (history.seed, outcome) =
        (history.seed.coordinate, x, y, history) ∧
      repeatedCoordinateWin G n history.seed.coordinate.val outcome = true
    then (strategyEventLaw (G.repeat n) S).weight outcome
    else 0

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactFairCoordinateRefinedWinningBornMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
    exactFiberQuestionWeight
        G n D history.seed history.history x y xs ys *
      (∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then
          bornTracePairing S.state.matrix
            (conditionedAliceCoordinateEffect G n S D
              history.aliceAnswer xs history.seed.coordinate.val a)
            (conditionedBobCoordinateEffect G n S D
              history.bobAnswer ys history.seed.coordinate.val b)
        else 0)

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The positive operator-valued measurement implementing dependent block. -/
def dependentBlockPOVM
    {R C : Type*} [Fintype R] [DecidableEq R] [Fintype C]
    {ι : R → Type*}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (P : (r : R) → POVM C (ι r)) :
    POVM C (Σ r : R, ι r) where
  effect c := Matrix.blockDiagonal' fun r => (P r).effect c
  positive c := by
    apply posSemidef_blockDiagonal'
    intro r
    exact (P r).positive c
  complete := by
    classical
    ext ⟨r, u⟩ ⟨s, v⟩
    by_cases same : r = s
    · subst s
      have completed := congrArg
        (fun M : Matrix (ι r) (ι r) ℂ => M u v)
        (P r).complete
      simpa only [Matrix.sum_apply, blockDiagonal'_apply, ↓reduceDIte, cast_eq, Matrix.one_apply,
        Sigma.mk.injEq, heq_eq_eq, true_and] using completed
    · simp only [Matrix.sum_apply, blockDiagonal'_apply, same, ↓reduceDIte, sum_const_zero, ne_eq,
        Sigma.mk.injEq, false_and, not_false_eq_true, one_apply_ne]

/-- The positive operator-valued measurement implementing reindexed. -/
def reindexedPOVM
    {C d e : Type*} [Fintype C]
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (basis : d ≃ e) (P : POVM C d) : POVM C e where
  effect c := (P.effect c).submatrix basis.symm basis.symm
  positive c := (P.positive c).submatrix basis.symm
  complete := by
    classical
    ext i j
    have completed := congrArg
      (fun M : Matrix d d ℂ => M (basis.symm i) (basis.symm j))
      P.complete
    simpa only [Matrix.sum_apply, submatrix_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq] using completed

/-- Combine two measurements as a direct-sum measurement on their local spaces. -/
def twoBlockPOVM
    {C d e : Type} [Fintype C]
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM C d) (Q : POVM C e) :
    POVM C (d ⊕ e) := by
  classical
  letI : (b : Bool) → Fintype (bif b then e else d)
    | false => inferInstanceAs (Fintype d)
    | true => inferInstanceAs (Fintype e)
  letI : (b : Bool) → DecidableEq (bif b then e else d)
    | false => inferInstanceAs (DecidableEq d)
    | true => inferInstanceAs (DecidableEq e)
  let blocks : (b : Bool) → POVM C (bif b then e else d)
    | false => P
    | true => Q
  exact reindexedPOVM
    (Equiv.sumEquivSigmaBool d e).symm
    (dependentBlockPOVM blocks)

/-- The positive operator-valued measurement implementing deterministic outcome. -/
def deterministicOutcomePOVM
    {C d : Type*} [Fintype C] [DecidableEq C]
    [Fintype d] [DecidableEq d] (default : C) : POVM C d where
  effect c := if c = default then 1 else 0
  positive c := by
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  complete := by
    classical
    simp only [sum_ite_eq', mem_univ, ↓reduceIte]

/-- Transport a POVM between equality decisions while retaining every effect matrix. -/
def pOVMChangeDecidableEq
    {C d : Type*} [Fintype C] [Fintype d]
    (source target : DecidableEq d)
    (P : @POVM C d inferInstance inferInstance source) :
    @POVM C d inferInstance inferInstance target where
  effect c := @POVM.effect C d inferInstance inferInstance source P c
  positive c := @POVM.positive C d
    inferInstance inferInstance source P c
  complete := by
    classical
    ext i j
    have completed := congrArg
      (fun M : Matrix d d ℂ => M i j)
      (@POVM.complete C d inferInstance inferInstance source P)
    simp only [Matrix.sum_apply, Matrix.one_apply] at completed ⊢
    by_cases same : i = j
    · subst j
      simpa only [↓reduceIte] using completed
    · simpa only [same, ↓reduceIte] using completed

/-- Pad Alice's refined measurement with deterministic outcomes on the unused blocks. -/
def exactSourceAlicePaddedPOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) :
    POVM A (ExactPaddedLocalIndex G n S D r) := by
  classical
  exact twoBlockPOVM
    (deterministicOutcomePOVM (d := PUnit) a₀)
    (twoBlockPOVM
      (exactSourceAliceRefinedPOVM G n S D r a₀ x)
      (deterministicOutcomePOVM
        (d := ExactBobLocalIndex G n S D r) a₀))

/-- Pad Bob's refined measurement with deterministic outcomes on the unused blocks. -/
def exactSourceBobPaddedPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (b₀ : B) (y : Y) :
    POVM B (ExactPaddedLocalIndex G n S D r) := by
  classical
  exact twoBlockPOVM
    (deterministicOutcomePOVM (d := PUnit) b₀)
    (twoBlockPOVM
      (deterministicOutcomePOVM
        (d := ExactAliceLocalIndex G n S D r) b₀)
      (exactSourceBobRefinedPOVM G n S D r b₀ y))

/-- The positive operator-valued measurement implementing exact source global alice. -/
def exactSourceGlobalAlicePOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (x : X) :
    POVM A (ExactGlobalHistoryLocalIndex G n S D) := by
  classical
  let actual := twoBlockPOVM
    (deterministicOutcomePOVM (d := PUnit) a₀)
    (dependentBlockPOVM
      (fun r : ExactHistoryFlag X Y A B D =>
        exactSourceAlicePaddedPOVM G n S D r a₀ x))
  exact pOVMChangeDecidableEq
    (@instDecidableEqSum PUnit
      (Σ r : ExactHistoryFlag X Y A B D,
        ExactPaddedLocalIndex G n S D r)
      inferInstance inferInstance)
    (Classical.decEq
      (ExactGlobalHistoryLocalIndex G n S D))
    actual

/-- The positive operator-valued measurement implementing exact source global bob. -/
def exactSourceGlobalBobPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (b₀ : B) (y : Y) :
    POVM B (ExactGlobalHistoryLocalIndex G n S D) := by
  classical
  let actual := twoBlockPOVM
    (deterministicOutcomePOVM (d := PUnit) b₀)
    (dependentBlockPOVM
      (fun r : ExactHistoryFlag X Y A B D =>
        exactSourceBobPaddedPOVM G n S D r b₀ y))
  exact pOVMChangeDecidableEq
    (@instDecidableEqSum PUnit
      (Σ r : ExactHistoryFlag X Y A B D,
        ExactPaddedLocalIndex G n S D r)
      inferInstance inferInstance)
    (Classical.decEq
      (ExactGlobalHistoryLocalIndex G n S D))
    actual

/-- The positive operator-valued measurement implementing exact source global catalyst alice. -/
def exactSourceGlobalCatalystAlicePOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) (a₀ : A) (x : X) :
    POVM A
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) := by
  classical
  exact reindexedPOVM finProdFinEquiv
    (purificationAlicePOVM (k := Fin e)
      (reindexedPOVM
        (Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D))
        (exactSourceGlobalAlicePOVM G n S D a₀ x)))

/-- The positive operator-valued measurement implementing exact source global catalyst bob. -/
def exactSourceGlobalCatalystBobPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) (b₀ : B) (y : Y) :
    POVM B
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) := by
  classical
  exact reindexedPOVM finProdFinEquiv
    (purificationAlicePOVM (k := Fin e)
      (reindexedPOVM
        (Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D))
        (exactSourceGlobalBobPOVM G n S D b₀ y)))

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

@[simp] private theorem twoBlockPOVM_effect_inl
    {C d e : Type} [Fintype C]
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM C d) (Q : POVM C e)
    (c : C) (i j : d) :
    (twoBlockPOVM P Q).effect c
      (.inl i) (.inl j) = P.effect c i j := by
  classical
  simp only [twoBlockPOVM, reindexedPOVM, dependentBlockPOVM,
    Equiv.sumEquivSigmaBool, Bool.cond_false, Bool.cond_true,
    Equiv.symm_mk, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl,
    blockDiagonal'_apply, ↓reduceDIte, cast_eq]

@[simp] private theorem twoBlockPOVM_effect_inr
    {C d e : Type} [Fintype C]
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM C d) (Q : POVM C e)
    (c : C) (i j : e) :
    (twoBlockPOVM P Q).effect c
      (.inr i) (.inr j) = Q.effect c i j := by
  classical
  simp only [twoBlockPOVM, reindexedPOVM, dependentBlockPOVM,
    Equiv.sumEquivSigmaBool, Bool.cond_false, Bool.cond_true,
    Equiv.symm_mk, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inr,
    blockDiagonal'_apply, ↓reduceDIte, cast_eq]

/--
@isnad1 id=eq.0h8v.s7.ae1cd7a012bf from=translated src=- shape=72ff4f16 vocab=5abcf8e9
-/
@[simp] theorem dependentBlockPOVM_effect_same
    {R C : Type*} [Fintype R] [DecidableEq R] [Fintype C]
    {ι : R → Type*}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (P : (r : R) → POVM C (ι r))
    (r : R) (c : C) (i j : ι r) :
    (dependentBlockPOVM P).effect c
      ⟨r, i⟩ ⟨r, j⟩ = (P r).effect c i j := by
  classical
  simp only [dependentBlockPOVM, blockDiagonal'_apply, ↓reduceDIte, cast_eq]

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

@[simp] private theorem exactSourceGlobalAlicePOVM_effect
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ a : A) (x : X)
    (i j : ExactAliceLocalIndex G n S D r) :
    (exactSourceGlobalAlicePOVM G n S D a₀ x).effect a
      (.inr ⟨r, .inr (.inl i)⟩)
      (.inr ⟨r, .inr (.inl j)⟩) =
      (exactSourceAliceRefinedPOVM G n S D r a₀ x).effect a i j := by
  classical
  simp only [exactSourceGlobalAlicePOVM, pOVMChangeDecidableEq, exactSourceAlicePaddedPOVM,
    twoBlockPOVM_effect_inr, dependentBlockPOVM_effect_same, twoBlockPOVM_effect_inl]

@[simp] private theorem exactSourceGlobalBobPOVM_effect
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (b₀ b : B) (y : Y)
    (i j : ExactBobLocalIndex G n S D r) :
    (exactSourceGlobalBobPOVM G n S D b₀ y).effect b
      (.inr ⟨r, .inr (.inr i)⟩)
      (.inr ⟨r, .inr (.inr j)⟩) =
      (exactSourceBobRefinedPOVM G n S D r b₀ y).effect b i j := by
  classical
  simp only [exactSourceGlobalBobPOVM, pOVMChangeDecidableEq, exactSourceBobPaddedPOVM,
    twoBlockPOVM_effect_inr, dependentBlockPOVM_effect_same]

private def exactSourceGlobalJointBasis
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    (ExactAliceLocalIndex G n S D r ×
      ExactBobLocalIndex G n S D r) →
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D)
  | (i, j) =>
    (.inr ⟨r, .inr (.inl i)⟩, .inr ⟨r, .inr (.inr j)⟩)

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The measurement effect for exact source global winning. -/
def exactSourceGlobalWinningEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    Matrix
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D)
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (exactSourceGlobalAlicePOVM G n S D a₀ x).effect a ⊗ₖ
        (exactSourceGlobalBobPOVM G n S D b₀ y).effect b
    else 0

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
@isnad1 id=eq.0h9v.s9.b1953c98e55e from=translated src=- shape=2246f75e vocab=b84c565b
-/
@[simp] theorem reindexedCatalystPOVM_effect
    {C d : Type*} [Fintype C] [Fintype d] [DecidableEq d]
    (P : POVM C d) (e : ℕ) (c : C)
    (i j : d) (k l : Fin e) :
    (reindexedPOVM finProdFinEquiv
      (purificationAlicePOVM (k := Fin e)
        (reindexedPOVM (Fintype.equivFin d) P))).effect c
      (finProdFinEquiv ((Fintype.equivFin d) i, k))
      (finProdFinEquiv ((Fintype.equivFin d) j, l)) =
      P.effect c i j * (if k = l then 1 else 0) := by
  classical
  simp only [reindexedPOVM, purificationAlicePOVM, submatrix_apply, Equiv.symm_apply_apply,
    kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
@isnad1 id=eq.0h16v.s20.58ee9c3f809c from=translated src=- shape=e92e0a44 vocab=c4506291
-/
@[simp] theorem exactSourceGlobalCatalystBobPOVM_effect
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) (b₀ b : B) (y : Y)
    (i j : ExactGlobalHistoryLocalIndex G n S D)
    (k l : Fin e) :
    (exactSourceGlobalCatalystBobPOVM G n S D e b₀ y).effect b
      (finProdFinEquiv
        (Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D) i, k))
      (finProdFinEquiv
        (Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D) j, l)) =
      (exactSourceGlobalBobPOVM G n S D b₀ y).effect b i j *
        (if k = l then 1 else 0) := by
  classical
  simp only [exactSourceGlobalCatalystBobPOVM, reindexedPOVM, purificationAlicePOVM,
    submatrix_apply, Equiv.symm_apply_apply, kroneckerMap_apply, Matrix.one_apply, mul_ite,
    mul_one, mul_zero]

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

private def exactAliceSourceAtomCode
    {n : ℕ} (D : Finset (Fin n)) :
    ExactJointOutcome X Y A B D →
      (SourceRemainingCoordinate D × X) ×
        (ExactHistoryFlag X Y A B D × Y) :=
  fun point =>
    ((point.1.coordinate, point.2.1 point.1.coordinate.val),
      (exactHistoryCode D point,
        point.2.2.1 point.1.coordinate.val))

private def exactBobSourceAtomCode
    {n : ℕ} (D : Finset (Fin n)) :
    ExactJointOutcome X Y A B D →
      (SourceRemainingCoordinate D × Y) ×
        (ExactHistoryFlag X Y A B D × X) :=
  fun point =>
    ((point.1.coordinate, point.2.2.1 point.1.coordinate.val),
      (exactHistoryCode D point,
        point.2.1 point.1.coordinate.val))

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

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactReverseAliceContextOutcomeProjection
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseAliceFixedInformation X Y D side ×
      (Fin side.card → Y) :=
  (⟨context,
     (fun j => outcome.1 j.val),
     (fun j => outcome.2.1 j.val),
     (fun j => outcome.1 j.val.val),
     (fun j => outcome.2.1 j.val.val),
     (fun j => outcome.1 j.val.val)⟩,
    fun marker =>
      outcome.2.1 (context.sideRank.symm marker).val.val)

private def exactReverseBobContextOutcomeProjection
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseBobFixedInformation X Y D side ×
      (Fin side.card → X) :=
  (⟨context,
     (fun j => outcome.1 j.val),
     (fun j => outcome.2.1 j.val),
     (fun j => outcome.2.1 j.val.val),
     (fun j => outcome.1 j.val.val),
     (fun j => outcome.2.1 j.val.val)⟩,
    fun marker =>
      outcome.1 (context.sideRank.symm marker).val.val)

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactReverseAliceMaskedQuestionRegister
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (flag : ConditionedAnswerFlag A B D)
    (seed : ExactRemainingSeed D)
    (xs : Fin n → X) (ys : Fin n → Y) :
    ExactReverseAliceNextContext X Y A B D side :=
  let context := exactReverseAliceContextAt side seed
  let fixed : ExactReverseAliceFixedInformation X Y D side :=
    ⟨context,
      (fun j => xs j.val),
      (fun j => ys j.val),
      (fun j => xs j.val.val),
      (fun j => ys j.val.val),
      (fun j => xs j.val.val)⟩
  finitePrefixMask default marker.castSucc
    ((fixed, flag),
      fun position => ys (context.sideRank.symm position).val.val)

private def exactReverseBobMaskedQuestionRegister
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (flag : ConditionedAnswerFlag A B D)
    (seed : ExactRemainingSeed D)
    (xs : Fin n → X) (ys : Fin n → Y) :
    ExactReverseBobNextContext X Y A B D side :=
  let context := exactReverseBobContextAt side seed
  let fixed : ExactReverseBobFixedInformation X Y D side :=
    ⟨context,
      (fun j => xs j.val),
      (fun j => ys j.val),
      (fun j => ys j.val.val),
      (fun j => xs j.val.val),
      (fun j => ys j.val.val)⟩
  finitePrefixMask default marker.castSucc
    ((fixed, flag),
      fun position => xs (context.sideRank.symm position).val.val)

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactReverseAliceMaskedOutcomeContext
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseAliceNextContext X Y A B D side :=
  let projection :=
    exactReverseAliceContextOutcomeProjection
      (X := X) (Y := Y) (A := A) (B := B)
      D side context outcome
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

private def exactReverseAliceContextMarkerInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : Y)
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  ∑ outcome : ExactOutcome X Y A B n,
    repeatedConditionedOutcomeLaw G n S D outcome *
      finiteRelativeEntropy
        (jointConditional
          (groupedMass
            (exactPrefixNextCode default marker)
            (exactConditionedReverseAliceNextJoint
              G n S D remaining side))
          (exactReverseAliceMaskedOutcomeContext
            G n S D side default marker context outcome))
        (jointConditional
          (groupedMass
            (exactPrefixNextCode default marker)
            (exactConditionedReverseAliceNextPrior
              G n S D remaining side))
          (exactReverseAliceMaskedOutcomeContext
            G n S D side default marker context outcome))

private def exactAliceSourceSeedBornInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) : ℝ :=
  ∑ outcome : ExactOutcome X Y A B n,
    repeatedConditionedOutcomeLaw G n S D outcome *
      finiteRelativeEntropy
        (jointConditional
          (fun atom :
            ((SourceRemainingCoordinate D × X) ×
              ExactHistoryFlag X Y A B D) × Y =>
            exactAliceInformationPosterior G n S D
              (atom.1.1, (atom.1.2, atom.2)))
          ((seed.coordinate, outcome.1 seed.coordinate.val),
            exactHistoryCode D (seed, outcome)))
        (G.conditionalYGivenX
          (outcome.1 seed.coordinate.val))

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

private def exactReverseBobMaskedOutcomeContext
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseBobNextContext X Y A B D side :=
  let projection :=
    exactReverseBobContextOutcomeProjection
      (X := X) (Y := Y) (A := A) (B := B)
      D side context outcome
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

private def exactReverseBobContextMarkedEntropyScore
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card)
    (outcome : ExactOutcome X Y A B n) : ℝ :=
  let target :=
    exactReverseBobMaskedOutcomeContext
      G n S D side default marker context outcome
  finiteRelativeEntropy
    (jointConditional
      (groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextJoint
          G n S D remaining side))
      target)
    (jointConditional
      (groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextPrior
          G n S D remaining side))
      target)

private def exactReverseBobActualMarkedEntropyScore
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (side : Finset (SourceRemainingCoordinate D))
    (seed : ExactRemainingSeed D)
    (marker : Fin side.card)
    (outcome : ExactOutcome X Y A B n) : ℝ :=
  exactReverseBobContextMarkedEntropyScore G n S D remaining default side
    (exactReverseBobContextAt side seed) marker outcome

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
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The exact source support preserving classical sampler construction used in the quantum parallel-
repetition argument.
-/
def ExactSourceSupportPreservingClassicalSampler
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (kappa gamma : ℝ) : Prop :=
  ∃ denominator : ℕ, 0 < denominator ∧
    ∃ numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ,
      (∀ index, (∑ history, numerator index history) = denominator) ∧
      (∀ index, finiteTotalVariation
        (exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index)
        (fun history =>
          (numerator index history : ℝ) / denominator) < gamma) ∧
      (∀ index history,
        0 < exactLocalConditionalFamily D base
            (exactLocallySampleableLaw G n S D)
            index history →
          0 < numerator index history) ∧
      ∃ nonempty : ∀ index,
        (rationalMarked denominator (numerator index)).Nonempty,
        finiteTotalVariation
            (exactLocallySampleableLaw G n S D)
            (exactLocallySampleableJARounded
              G n D denominator numerator) ≤ kappa + gamma ∧
        finiteTotalVariation
            (exactLocallySampleableLaw G n S D)
            (exactLocallySampleableJBRounded
              G n D denominator numerator) ≤ kappa + gamma ∧
        exactLocallySampleablePermutationMismatch
            G n D denominator numerator nonempty ≤
          4 * (kappa + gamma)

end

end QuantumParallelRepetition

end
