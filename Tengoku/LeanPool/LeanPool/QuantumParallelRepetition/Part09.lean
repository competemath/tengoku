/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import Tengoku.LeanPool.LeanPool.QuantumParallelRepetition.Part08

/-! # Quantum parallel repetition, part 09 -/

@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open Filter
open scoped Topology

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The one-coordinate strategy and error data extracted from an exact source. -/
def ExactSourceOneGameRounding
    (G : Game X Y A B) : Prop :=
  ∃ K₀ : ℝ, 0 ≤ K₀ ∧
    ∀ (n : ℕ) (S : Strategy (G.repeat n))
      (D : Finset (Fin n)),
      0 < (Finset.univ \ D).card →
      0 < repeatedPostselectionMass G n S D →
      ∀ (α gamma : ℝ),
        0 < α → α ≤ 1 → 0 < gamma →
        uniformRemainingFailure
            (strategyEventLaw (G.repeat n) S)
            (repeatedCoordinateWin G n) D <
          (1 - entangledValue G) / 2 →
        ∃ rounded : Strategy G,
          roundedWinningLowerBound (1 - entangledValue G)
              K₀ α (martingaleRate G n S D)
              (exactSourcePinskerRate G n S D + gamma) ≤
            rounded.winProbability

end

section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The positive operator-valued measurement implementing unitary conjugate. -/
def unitaryConjugatePOVM
    {C d : Type} [Fintype C] [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (P : POVM C d) : POVM C d where
  effect c :=
    (U : Matrix d d ℂ)ᴴ * P.effect c * (U : Matrix d d ℂ)
  positive c := by
    have positive :=
      (P.positive c).mul_mul_conjTranspose_same
        ((U : Matrix d d ℂ)ᴴ)
    simpa only [conjTranspose_conjTranspose] using positive
  complete := by
    classical
    have unitary :
        (U : Matrix d d ℂ)ᴴ * (U : Matrix d d ℂ) = 1 := by
      simpa only [star_eq_conjTranspose] using
        (Matrix.mem_unitaryGroup_iff').mp U.property
    calc
      (∑ c : C,
        (U : Matrix d d ℂ)ᴴ * P.effect c * (U : Matrix d d ℂ)) =
          (U : Matrix d d ℂ)ᴴ *
            (∑ c : C, P.effect c) *
            (U : Matrix d d ℂ) := by
              simp only [mul_sum, sum_mul]
      _ = 1 := by rw [P.complete, Matrix.mul_one, unitary]

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactSourceGlobalCatalystWinningEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    Matrix
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e))
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (exactSourceGlobalCatalystAlicePOVM
        G n S D e a₀ x).effect a ⊗ₖ
      (exactSourceGlobalCatalystBobPOVM
        G n S D e b₀ y).effect b
    else 0

private def exactSourceGlobalCatalystBasisEquiv
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) :
    ((ExactGlobalHistoryLocalIndex G n S D ×
       ExactGlobalHistoryLocalIndex G n S D) ×
      (Fin e × Fin e)) ≃
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) := by
  classical
  let localEquiv :
      (ExactGlobalHistoryLocalIndex G n S D × Fin e) ≃
        Fin (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D) * e) :=
    (Equiv.prodCongr
      (Fintype.equivFin
        (ExactGlobalHistoryLocalIndex G n S D))
      (Equiv.refl (Fin e))).trans finProdFinEquiv
  exact
    (Equiv.prodProdProdComm
      (ExactGlobalHistoryLocalIndex G n S D)
      (ExactGlobalHistoryLocalIndex G n S D)
      (Fin e) (Fin e)).trans (Equiv.prodCongr localEquiv localEquiv)

@[simp] theorem exactSourceGlobalCatalystAlicePOVM_effect_global
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) (a₀ a : A) (x : X)
    (i j : ExactGlobalHistoryLocalIndex G n S D)
    (k l : Fin e) :
    (exactSourceGlobalCatalystAlicePOVM
      G n S D e a₀ x).effect a
      (finProdFinEquiv
        ((Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D)) i, k))
      (finProdFinEquiv
        ((Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D)) j, l)) =
      (exactSourceGlobalAlicePOVM
        G n S D a₀ x).effect a i j *
        (if k = l then 1 else 0) := by
  classical
  change
    (reindexedPOVM finProdFinEquiv
      (purificationAlicePOVM (k := Fin e)
        (reindexedPOVM
          (Fintype.equivFin
            (ExactGlobalHistoryLocalIndex G n S D))
          (exactSourceGlobalAlicePOVM G n S D a₀ x)))).effect a
      (finProdFinEquiv
        ((Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D)) i, k))
      (finProdFinEquiv
        ((Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D)) j, l)) = _
  exact reindexedCatalystPOVM_effect
    (exactSourceGlobalAlicePOVM G n S D a₀ x)
    e a i j k l

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/--
The unconditional matched verifier tensor construction used in the quantum parallel-repetition
argument.
-/
def unconditionalMatchedVerifierTensor
    {s t : Type*}
    (target : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    EuclideanSpace ℂ (s × t) :=
  toLp 2 (fun q : s × t => target q.1 * work q.2)

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/--
The type used to represent unconditional selected copy local index in the exact sampling
construction.
-/
abbrev UnconditionalSelectedCopyLocalIndex
    (B d N m : ℕ) :=
  Σ _ : Fin B × Fin d, Fin (N * m)

/-- The selected mixed stage after applying its coherent local bucket resets. -/
def unconditionalSelectedCopyCleanedStage
    {d N B m : ℕ}
    (Q : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    EuclideanSpace ℂ
      (UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) :=
  dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
    Q w ξ ζ A C
    (dSVDensityRationalPublicBucketPhysicalCoherentMixedState
      (N := N) (B := B) w m ξ ζ)

private def unconditionalSelectedCopyIdealStage
    {d N B m : ℕ}
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) :=
  dSVDensityRationalPublicBucketPhysicalCoherentTargetState
    (N := N) (B := B) w m ξ ζ

/-- Tensor the common failure prefix with the work retained after the selected stage. -/
def unconditionalSelectedCopyRetainedWork
    {S N d L : ℕ} {τ : Type*}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ τ) :
    EuclideanSpace ℂ
      ((Fin j.val →
        (DSVUniformDensityThresholdLocalIndex N d ×
         DSVUniformDensityThresholdLocalIndex N d)) × τ) :=
  unconditionalMatchedVerifierTensor
    (dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
      (N := N) width schedule ξ ζ j)
    rest

/--
The unconditional selected copy cleaned matched branch construction used in the quantum
parallel-repetition argument.
-/
def unconditionalSelectedCopyCleanedMatchedBranch
    {S N d L B m : ℕ} {τ : Type*}
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) (rest : EuclideanSpace ℂ τ) :
    EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex B d N m ×
          UnconditionalSelectedCopyLocalIndex B d N m) ×
        ((Fin j.val →
          (DSVUniformDensityThresholdLocalIndex N d ×
            DSVUniformDensityThresholdLocalIndex N d)) × τ)) :=
  unconditionalMatchedVerifierTensor
    (unconditionalSelectedCopyCleanedStage
      (N := N) (B := B) (m := m)
      Q (width (schedule j)) ξ ζ A C)
    (unconditionalSelectedCopyRetainedWork
      (N := N) width schedule ξ ζ j rest)

private def unconditionalSelectedCopyIdealMatchedBranch
    {S N d L B m : ℕ} {τ : Type*}
    (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ τ) :
    EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex B d N m ×
          UnconditionalSelectedCopyLocalIndex B d N m) ×
        ((Fin j.val →
          (DSVUniformDensityThresholdLocalIndex N d ×
            DSVUniformDensityThresholdLocalIndex N d)) × τ)) :=
  unconditionalMatchedVerifierTensor
    (unconditionalSelectedCopyIdealStage
      (N := N) (B := B) (m := m) (width (schedule j)) ξ ζ)
    (unconditionalSelectedCopyRetainedWork
      (N := N) width schedule ξ ζ j rest)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/-- The state vector representing unconditional conjugate pure. -/
def unconditionalConjugatePureVector
    {ι : Type*} (z : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  toLp 2 (fun i : ι => star (z i))

@[simp] theorem unconditionalConjugatePureVector_apply
    {ι : Type*}
    (z : EuclideanSpace ℂ ι) (i : ι) :
    unconditionalConjugatePureVector z i = star (z i) := by
  rfl

/-- Transpose every effect of a POVM to obtain the conjugate measurement. -/
def unconditionalConjugatePOVM
    {A ι : Type*} [Fintype A] [Fintype ι] [DecidableEq ι]
    (P : POVM A ι) : POVM A ι where
  effect a := (P.effect a).transpose
  positive a := (P.positive a).transpose
  complete := by
    classical
    rw [← Matrix.transpose_sum]
    rw [P.complete, Matrix.transpose_one]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def unconditionalConjugateSourceGlobalCatalystWinningEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    Matrix
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e))
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystAlicePOVM
          G n S D e a₀ x)).effect a ⊗ₖ
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystBobPOVM
          G n S D e b₀ y)).effect b
    else 0

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The unconditional mixed conjugate sigma atom lift construction used in the quantum parallel-
repetition argument.
-/
def unconditionalMixedConjugateSigmaAtomLift
    {d m : ℕ} (B : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup
      (Σ _ : Fin B × Fin d, Fin m) ℂ := by
  classical
  let e : ((Fin B × Fin d) × Fin m) ≃
      (Σ _ : Fin B × Fin d, Fin m) :=
    (Equiv.sigmaEquivProd (Fin B × Fin d) (Fin m)).symm
  let M : Matrix ((Fin B × Fin d) × Fin m)
      ((Fin B × Fin d) × Fin m) ℂ :=
    ((1 : Matrix (Fin B) (Fin B) ℂ) ⊗ₖ
      (U : Matrix (Fin d) (Fin d) ℂ)) ⊗ₖ
      (1 : Matrix (Fin m) (Fin m) ℂ)
  have unitary : M ∈ Matrix.unitaryGroup
      ((Fin B × Fin d) × Fin m) ℂ :=
    Matrix.kronecker_mem_unitary
      (Matrix.kronecker_mem_unitary
        (Matrix.unitaryGroup (Fin B) ℂ).one_mem U.property)
      (Matrix.unitaryGroup (Fin m) ℂ).one_mem
  refine ⟨Matrix.reindex e e M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have compatible :
      star (Matrix.reindex e e M) =
        Matrix.reindex e e (star M) := by
    ext i j
    simp only [reindex_apply, star_apply, submatrix_apply, RCLike.star_def, star_eq_conjTranspose,
      conjTranspose_apply]
  rw [compatible]
  change
    (Matrix.reindexRingEquiv ℂ e) (star M) *
      (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp unitary]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

private def unconditionalMixedConjugateSigmaLocalAction
    {d m : ℕ} (B : ℕ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin m) ×
        (Σ _ : Fin B × Fin d, Fin m))) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin m) ×
        (Σ _ : Fin B × Fin d, Fin m)) :=
  toLp 2
    ((((unconditionalMixedConjugateSigmaAtomLift (m := m) B U :
          Matrix (Σ _ : Fin B × Fin d, Fin m)
            (Σ _ : Fin B × Fin d, Fin m) ℂ) ⊗ₖ
        (unconditionalMixedConjugateSigmaAtomLift (m := m) B V :
          Matrix (Σ _ : Fin B × Fin d, Fin m)
            (Σ _ : Fin B × Fin d, Fin m) ℂ)).mulVec
      (ofLp z)))

private def unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
    {d N B : ℕ} (w : ℝ) (n : ℕ)
    (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin (N * n)) ×
       (Σ _ : Fin B × Fin d, Fin (N * n))) :=
  dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
    (unconditionalConjugatePureVector
      (dSVDensityRationalCanonicalAcceptedTarget w N ξ))
    (fun _ _ _ => embezzlementState (N * n))

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The unitary operator implementing unconditional mixed conjugate selected branch. -/
def unconditionalMixedConjugateSelectedBranchUnitary
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup ((ι × ι) × τ) ℂ := by
  classical
  refine
    ⟨(((U : Matrix ι ι ℂ) ⊗ₖ
        (V : Matrix ι ι ℂ)) ⊗ₖ
        (1 : Matrix τ τ ℂ)), ?_⟩
  exact Matrix.kronecker_mem_unitary
    (Matrix.kronecker_mem_unitary U.property V.property)
    (Matrix.unitaryGroup τ ℂ).one_mem

/-- The operator action for unconditional mixed conjugate selected branch local. -/
def unconditionalMixedConjugateSelectedBranchLocalAction
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ ((ι × ι) × τ)) :
    EuclideanSpace ℂ ((ι × ι) × τ) :=
  toLp 2
    ((unconditionalMixedConjugateSelectedBranchUnitary
        (τ := τ) U V :
      Matrix ((ι × ι) × τ) ((ι × ι) × τ) ℂ).mulVec
      (ofLp z))

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

section DependentStoppingBlocks

variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι κ : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
variable [∀ r, Fintype (κ r)] [∀ r, DecidableEq (κ r)]

/-- The state vector representing actual stopping branch. -/
def actualStoppingBranchVector
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ s, κ s)))
    (r s : R) : EuclideanSpace ℂ (ι r × κ s) :=
  toLp 2 fun q => z (⟨r, q.1⟩, ⟨s, q.2⟩)

/-- The measurement effect for actual stopping branch winning. -/
def actualStoppingBranchWinningEffect
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (r s : R) (x : X) (y : Y) :
    Matrix (ι r × κ s) (ι r × κ s) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (PA r x).effect a ⊗ₖ (PB s y).effect b
    else 0

private def actualStoppingGlobalWinningEffect
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (x : X) (y : Y) :
    Matrix ((Σ r, ι r) × (Σ s, κ s))
      ((Σ r, ι r) × (Σ s, κ s)) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (dependentBlockPOVM
        (fun r => PA r x)).effect a ⊗ₖ
        (dependentBlockPOVM
          (fun s => PB s y)).effect b
    else 0

end DependentStoppingBlocks

end

section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

section QuestionLocalStopping

variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]

/-- The operator action for actual stopping question local. -/
def actualStoppingQuestionLocalAction
    (U V : Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ r, ι r))) :
    EuclideanSpace ℂ ((Σ r, ι r) × (Σ r, ι r)) :=
  toLp 2
    (((U : Matrix (Σ r, ι r) (Σ r, ι r) ℂ) ⊗ₖ
      (V : Matrix (Σ r, ι r) (Σ r, ι r) ℂ)).mulVec
      (ofLp z))

end QuestionLocalStopping

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

private abbrev DSVDensityRationalPublicLogPhaseHistoryFamily
    (B N d L : ℕ) :=
  BipartiteUnitVector d →
    Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ

private def dSVDensityRationalPublicLogPhaseStoppedState
    (B N d L m : ℕ)
    (S T : DSVDensityRationalPublicLogPhaseHistoryFamily
      B N d L)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicLogPhaseResidual
          B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicLogPhaseResidual
          B N d L m)) :=
  localUnitaryAction
    (dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
      B N d L m (S ξ))
    (dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
      B N d L m (T ζ))
    (dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
      B N d L m)

private def dSVDensityRationalPublicMultiscaleOriginalSigmaTargetFirstEquiv
    (S B N d L m : ℕ) :
    (Σ _ :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ×
        DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L,
      Fin m) ≃
      Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) :=
  (dSVDensityRationalPublicBucketCoherentPhaseSigmaProductEquiv
    (H := DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L)
    (Fintype.card
      (DSVDensityRationalPublicMultiscalePhase S B)) m).trans
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
      S B N d L m)

private def dSVDensityRationalHeterogeneousOriginalAliceHistoryFamily
    (S B N d L : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S) :
    DSVDensityRationalPublicLogPhaseHistoryFamily
      (Fintype.card
        (DSVDensityRationalPublicMultiscalePhase S B))
      N d L :=
  fun ξ =>
    dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
      (Fintype.card
        (DSVDensityRationalPublicMultiscalePhase S B))
      (dSVDensityRationalHeterogeneousActualAliceUnitary
        N width schedule ξ)

private def dSVDensityRationalHeterogeneousOriginalBobHistoryFamily
    (S B N d L : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S) :
    DSVDensityRationalPublicLogPhaseHistoryFamily
      (Fintype.card
        (DSVDensityRationalPublicMultiscalePhase S B))
      N d L :=
  fun ζ =>
    dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
      (Fintype.card
        (DSVDensityRationalPublicMultiscalePhase S B))
      (dSVDensityRationalHeterogeneousActualBobUnitary
        N width schedule ζ)

private def dSVDensityRationalHeterogeneousOriginalStoppedState
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) :=
  dSVDensityRationalPublicLogPhaseStoppedState
    (Fintype.card
      (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m
    (dSVDensityRationalHeterogeneousOriginalAliceHistoryFamily
      S B N d L width schedule)
    (dSVDensityRationalHeterogeneousOriginalBobHistoryFamily
      S B N d L width schedule)
    ξ ζ

private def dSVDensityRationalHeterogeneousOriginalSameStopStateEquiv
    (S B N d L m : ℕ) :
    EuclideanSpace ℂ
      ((Σ _ :
        DSVDensityRationalPublicMultiscalePhaseIndex S B ×
          DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L,
        Fin m) ×
       (Σ _ :
        DSVDensityRationalPublicMultiscalePhaseIndex S B ×
          DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L,
        Fin m)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (Fin (d *
          dSVDensityRationalPublicMultiscalePhaseResidual
            S B N d L m) ×
         Fin (d *
          dSVDensityRationalPublicMultiscalePhaseResidual
            S B N d L m)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr
      (dSVDensityRationalPublicMultiscaleOriginalSigmaTargetFirstEquiv
        S B N d L m)
      (dSVDensityRationalPublicMultiscaleOriginalSigmaTargetFirstEquiv
        S B N d L m))

private def dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) :=
  dSVDensityRationalHeterogeneousOriginalSameStopStateEquiv
      S B N d L m
    (dSVDensityRationalHeterogeneousPureStoppedSigmaState
      width schedule ξ ζ
      (fun _ _ _ => embezzlementState m))

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def directDSVRemainingCopyEquiv
    {L : ℕ} {β : Type*} (j : Fin L) :
    ((Fin j.val → β) × (Fin (L - j.val) → β)) ≃ (Fin L → β) where
  toFun z i :=
    if before : i.val < j.val then z.1 ⟨i.val, before⟩
    else z.2 ⟨i.val - j.val, by omega⟩
  invFun z :=
    (fun i => z ⟨i.val, by omega⟩,
     fun i => z ⟨j.val + i.val, by omega⟩)
  left_inv z := by
    rcases z with ⟨before, after⟩
    apply Prod.ext
    · funext i
      simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]
    · funext i
      simp only [add_lt_iff_neg_left, not_lt_zero, ↓reduceDIte, add_tsub_cancel_left, Fin.eta]
  right_inv z := by
    funext i
    dsimp
    split_ifs with before
    · rfl
    · apply congrArg z
      apply Fin.ext
      change j.val + (i.val - j.val) = i.val
      omega

private def directDSVSelectedCopyLocalHistoryEquiv
    {L : ℕ} {β : Type*} (j : Fin L) :
    (β × ((Fin j.val → β) × (Fin (L - j.val) → β))) ≃
      (Fin (L + 1) → β) :=
  (Equiv.prodCongr (Equiv.refl β)
    (directDSVRemainingCopyEquiv (β := β) j)).trans
    (Fin.insertNthEquiv (fun _ : Fin (L + 1) => β) j.castSucc)

@[simp] private theorem directDSVSelectedCopyLocalHistoryEquiv_hit
    {L : ℕ} {β : Type*} (j : Fin L)
    (selected : β) (before : Fin j.val → β)
    (after : Fin (L - j.val) → β) :
    directDSVSelectedCopyLocalHistoryEquiv j
        (selected, (before, after)) j.castSucc = selected := by
  simp only [directDSVSelectedCopyLocalHistoryEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map_apply, id_eq, Fin.insertNthEquiv_apply, Fin.insertNth_apply_same]

@[simp] private theorem directDSVSelectedCopyLocalHistoryEquiv_before
    {L : ℕ} {β : Type*} (j : Fin L)
    (selected : β) (before : Fin j.val → β)
    (after : Fin (L - j.val) → β) (i : Fin j.val) :
    directDSVSelectedCopyLocalHistoryEquiv j
        (selected, (before, after))
        ⟨i.val, by omega⟩ = before i := by
  let k : Fin L := ⟨i.val, by omega⟩
  have earlier : k < j := by
    change i.val < j.val
    exact i.isLt
  have selected_index :
      j.castSucc.succAbove k =
        (⟨i.val, by omega⟩ : Fin (L + 1)) := by
    rw [Fin.succAbove_castSucc_of_lt j k earlier]
    rfl
  unfold directDSVSelectedCopyLocalHistoryEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply,
    Fin.insertNthEquiv_apply]
  rw [← selected_index, Fin.insertNth_apply_succAbove]
  change
    (if h : k.val < j.val
      then before ⟨k.val, h⟩
      else after ⟨k.val - j.val, by omega⟩) = before i
  simp only [k, i.isLt, ↓reduceDIte]

@[simp] private theorem directDSVSelectedCopyLocalHistoryEquiv_after
    {L : ℕ} {β : Type*} (j : Fin L)
    (selected : β) (before : Fin j.val → β)
    (after : Fin (L - j.val) → β) (i : Fin (L - j.val)) :
    directDSVSelectedCopyLocalHistoryEquiv j
        (selected, (before, after))
        ⟨j.val + 1 + i.val, by omega⟩ = after i := by
  let k : Fin L := ⟨j.val + i.val, by omega⟩
  have later : j ≤ k := by
    change j.val ≤ j.val + i.val
    omega
  have selected_index :
      j.castSucc.succAbove k =
        (⟨j.val + 1 + i.val, by omega⟩ : Fin (L + 1)) := by
    rw [Fin.succAbove_castSucc_of_le j k later]
    apply Fin.ext
    change j.val + i.val + 1 = j.val + 1 + i.val
    omega
  unfold directDSVSelectedCopyLocalHistoryEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply,
    Fin.insertNthEquiv_apply]
  rw [← selected_index, Fin.insertNth_apply_succAbove]
  change
    (if h : k.val < j.val
      then before ⟨k.val, h⟩
      else after ⟨k.val - j.val, by omega⟩) = after i
  have not_before : ¬ j.val + i.val < j.val := by omega
  simp only [not_before, ↓reduceDIte, add_tsub_cancel_left, Fin.eta, k]

/--
The type used to represent unconditional source physical stopping phase fiber in the exact
sampling construction.
-/
abbrev UnconditionalSourcePhysicalStoppingPhaseFiber
    (S B N d L m : ℕ) :=
  Σ _ : DSVDensityRationalPublicMultiscalePhaseIndex S B ×
    DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d, Fin m

/-- Regroup phase, stopped history, and harmonic indices by their stopping flag. -/
def unconditionalSourcePhysicalStoppingPhaseHarmonicIndexEquiv
    (S B N d L m : ℕ) :
    ((DSVDensityRationalPublicMultiscalePhaseIndex S B ×
        DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) ×
      Fin m) ≃
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber S B N d L m)
    where
  toFun q := ⟨q.1.2.1, ⟨(q.1.1, q.1.2.2), q.2⟩⟩
  invFun q := ((q.2.1.1, ⟨q.1, q.2.1.2⟩), q.2.2)
  left_inv := by
    intro q
    rcases q with ⟨⟨phase, ⟨flag, history⟩⟩, work⟩
    rfl
  right_inv := by
    intro q
    rcases q with ⟨flag, ⟨⟨phase, history⟩, work⟩⟩
    rfl

/-- Convert the target-first index into stopping flags and their physical fibers. -/
def unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
    (S B N d L m : ℕ) :
    Fin (d *
      dSVDensityRationalPublicMultiscalePhaseResidual
        S B N d L m) ≃
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber S B N d L m) :=
  (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
      S B N d L m).symm.trans
    (unconditionalSourcePhysicalStoppingPhaseHarmonicIndexEquiv
      S B N d L m)

/-- The bipartite isometry induced by the target-first stopping index equivalence. -/
def unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
    (S B N d L m : ℕ) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ
      ((Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m) ×
       (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr
      (unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
        S B N d L m)
      (unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
        S B N d L m))

/-- Transport a unitary matrix along an equivalence of its row and column indices. -/
def unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup κ ℂ := by
  classical
  let M : Matrix ι ι ℂ := U.val
  refine ⟨Matrix.reindex e e M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have compatible :
      star (Matrix.reindex e e M) = Matrix.reindex e e (star M) := by
    ext i j
    simp only [reindex_apply, star_apply, submatrix_apply, RCLike.star_def, star_eq_conjTranspose,
      conjTranspose_apply]
  rw [compatible]
  change
    (Matrix.reindexRingEquiv ℂ e) (star M) *
      (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp U.property]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

/-- Insert the selected phase into the family of phases at all other scales. -/
def unconditionalSelectedMultiscalePhaseIndexEquiv
    {S B : ℕ} (scale : Fin (S + 1)) :
    (Fin B × Fin (Fintype.card (Fin S → Fin B))) ≃
      DSVDensityRationalPublicMultiscalePhaseIndex (S + 1) B :=
  ((Equiv.prodCongr (Equiv.refl (Fin B))
      (Fintype.equivFin (Fin S → Fin B)).symm).trans
    (Fin.insertNthEquiv
      (fun _ : Fin (S + 1) => Fin B) scale)).trans
      (Fintype.equivFin (Fin (S + 1) → Fin B))

/-- Split the actual phase family into its selected phase and remaining phases. -/
def unconditionalActualMultiscalePhaseIndexEquiv
    {S B : ℕ} (scale : Fin S) :
    (Fin B × Fin (Fintype.card (Fin (S - 1) → Fin B))) ≃
      DSVDensityRationalPublicMultiscalePhaseIndex S B := by
  cases S with
  | zero => exact Fin.elim0 scale
  | succ S =>
      exact unconditionalSelectedMultiscalePhaseIndexEquiv
        (S := S) scale

/-- Reindex a cleaned unitary through an equivalence of its local index spaces. -/
def unconditionalSourcePhysicalCleanedReindexedUnitary
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ)
    (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup κ ℂ := by
  classical
  let M : Matrix ι ι ℂ := U.val
  refine ⟨Matrix.reindex e e M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have compatible :
      star (Matrix.reindex e e M) =
        Matrix.reindex e e (star M) := by
    ext i j
    simp only [reindex_apply, star_apply, submatrix_apply, RCLike.star_def, star_eq_conjTranspose,
      conjTranspose_apply]
  rw [compatible]
  change
    (Matrix.reindexRingEquiv ℂ e) (star M) *
      (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp U.property]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

/-- Transport a target-first unitary to the physical stopping fibers. -/
def unconditionalSourcePhysicalCleanedTargetFirstUnitary
    (S B N d L m : ℕ)
    (U : Matrix.unitaryGroup
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) ℂ) :
    Matrix.unitaryGroup
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m) ℂ :=
  unconditionalSourcePhysicalCleanedReindexedUnitary
    (unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
      S B N d L m) U

/-- The source object for unconditional source physical cleaned stopping fixed. -/
def unconditionalSourcePhysicalCleanedStoppingFixedSource
    (S B N d L m : ℕ) :
    EuclideanSpace ℂ
      ((Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m) ×
       (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m)) :=
  unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
    S B N d L m
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource
      S B N d L m)

/-- Split a history into the selected coordinate, its prefix, and its suffix. -/
def unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
    {L : ℕ} (j : Fin L) (β : Type*) :
    (Fin (L + 1) → β) ≃
      β × ((Fin j.val → β) × (Fin (L - j.val) → β)) where
  toFun f :=
    (f j.castSucc,
      (fun i => f ⟨i.val, by omega⟩,
       fun i => f ⟨j.val + 1 + i.val, by omega⟩))
  invFun q i :=
    if before : i.val < j.val then
      q.2.1 ⟨i.val, before⟩
    else if hit : i.val = j.val then q.1
    else q.2.2 ⟨i.val - (j.val + 1), by omega⟩
  left_inv := by
    intro f
    funext i
    dsimp
    split <;> rename_i before
    · apply congrArg f
      apply Fin.ext
      rfl
    · split <;> rename_i hit
      · apply congrArg f
        apply Fin.ext
        exact hit.symm
      · apply congrArg f
        apply Fin.ext
        simp only
        omega
  right_inv := by
    intro q
    rcases q with ⟨selected, before, later⟩
    apply Prod.ext
    · simp only [Fin.val_castSucc, lt_self_iff_false, ↓reduceDIte]
    · apply Prod.ext
      · funext i
        simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]
      · funext i
        have not_before : ¬ j.val + 1 + i.val < j.val := by omega
        have not_hit : ¬ j.val + 1 + i.val = j.val := by omega
        simp only [not_before, ↓reduceDIte, not_hit, add_tsub_cancel_left, Fin.eta]

/-- The finite equivalence encoding unconditional source physical cleaned full local index. -/
def unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
    {P R : Type*} {B N d L m : ℕ}
    (phaseSplit : P ≃ Fin B × R) (j : Fin L) :
    (Σ _ : P × (Fin (L + 1) →
        DSVUniformDensityThresholdLocalIndex N d), Fin m) ≃
      UnconditionalSelectedCopyLocalIndex B d N m ×
        ((Fin j.val →
          DSVUniformDensityThresholdLocalIndex N d) ×
         ((Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d) × R)) where
  toFun q :=
    let phase := phaseSplit q.1.1
    let history :=
      unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
        (DSVUniformDensityThresholdLocalIndex N d) q.1.2
    (⟨(phase.1, history.1.2),
       finProdFinEquiv (history.1.1, q.2)⟩,
      (history.2.1, (history.2.2, phase.2)))
  invFun q :=
    let work := finProdFinEquiv.symm q.1.2
    ⟨(phaseSplit.symm (q.1.1.1, q.2.2.2),
      (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
        (DSVUniformDensityThresholdLocalIndex N d)).symm
        (⟨work.1, q.1.1.2⟩, (q.2.1, q.2.2.1))),
      work.2⟩
  left_inv := by
    rintro ⟨⟨phase, history⟩, work⟩
    simp only [Equiv.symm_apply_apply]
    change
      (⟨(phaseSplit.symm
          ((phaseSplit phase).1, (phaseSplit phase).2),
        (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
          (DSVUniformDensityThresholdLocalIndex N d)).symm
          ((unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
            (DSVUniformDensityThresholdLocalIndex N d) history).1,
           ((unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
             (DSVUniformDensityThresholdLocalIndex N d) history).2.1,
            (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
              (DSVUniformDensityThresholdLocalIndex N d) history).2.2))),
        work⟩ :
        Σ _ : P × (Fin (L + 1) →
          DSVUniformDensityThresholdLocalIndex N d), Fin m) =
          ⟨(phase, history), work⟩
    simp only [Prod.mk.eta, Equiv.symm_apply_apply,
      unconditionalSourcePhysicalCleanedSelectedHistoryEquiv]
  right_inv := by
    rintro ⟨⟨⟨phase, spectral⟩, packed⟩,
      ⟨before, ⟨later, remainder⟩⟩⟩
    simp only [Equiv.apply_symm_apply, finProdFinEquiv_symm_apply, Prod.mk.injEq, Sigma.mk.injEq,
      heq_eq_eq, true_and, and_true]
    exact finProdFinEquiv.apply_symm_apply packed

/-- Group the selected pair together and retain the bilateral prefix and tail indices. -/
def unconditionalSourcePhysicalCleanedFullBilateralRegroup
    {R : Type*} {B N d L m : ℕ} (j : Fin L) :
    ((UnconditionalSelectedCopyLocalIndex B d N m ×
       ((Fin j.val → DSVUniformDensityThresholdLocalIndex N d) ×
        ((Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d) × R))) ×
     (UnconditionalSelectedCopyLocalIndex B d N m ×
       ((Fin j.val → DSVUniformDensityThresholdLocalIndex N d) ×
        ((Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d) × R)))) ≃
    ((UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) ×
      ((Fin j.val →
        (DSVUniformDensityThresholdLocalIndex N d ×
         DSVUniformDensityThresholdLocalIndex N d)) ×
       (((Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d) ×
         (Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d)) ×
        (R × R)))) where
  toFun q :=
    ((q.1.1, q.2.1),
      ((fun i => (q.1.2.1 i, q.2.2.1 i)),
       ((q.1.2.2.1, q.2.2.2.1),
        (q.1.2.2.2, q.2.2.2.2))))
  invFun q :=
    ((q.1.1,
       ((fun i => (q.2.1 i).1),
        (q.2.2.1.1, q.2.2.2.1))),
     (q.1.2,
       ((fun i => (q.2.1 i).2),
        (q.2.2.1.2, q.2.2.2.2))))
  left_inv := by
    rintro ⟨⟨selectedA, beforeA, laterA, phaseA⟩,
      ⟨selectedB, beforeB, laterB, phaseB⟩⟩
    simp only
  right_inv := by
    rintro ⟨⟨selectedA, selectedB⟩,
      ⟨before, ⟨⟨laterA, laterB⟩, ⟨phaseA, phaseB⟩⟩⟩⟩
    simp only [Prod.mk.eta]

/-- The linear isometry implementing unconditional source physical cleaned full bilateral state. -/
def unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
    {P R : Type*} [Fintype P] [Fintype R]
    {B N d L m : ℕ}
    (phaseSplit : P ≃ Fin B × R) (j : Fin L) :
    EuclideanSpace ℂ
      ((Σ _ : P × (Fin (L + 1) →
          DSVUniformDensityThresholdLocalIndex N d), Fin m) ×
       (Σ _ : P × (Fin (L + 1) →
          DSVUniformDensityThresholdLocalIndex N d), Fin m)) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex B d N m ×
        UnconditionalSelectedCopyLocalIndex B d N m) ×
       ((Fin j.val →
         (DSVUniformDensityThresholdLocalIndex N d ×
          DSVUniformDensityThresholdLocalIndex N d)) ×
        (((Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d) ×
          (Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d)) ×
         (R × R)))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.prodCongr
      (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
        phaseSplit j)
      (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
        phaseSplit j)).trans
      (unconditionalSourcePhysicalCleanedFullBilateralRegroup
        (R := R) (B := B) (N := N) (d := d) (m := m) j))

private def unconditionalSourcePhysicalCleanedSelectedStageUnitary
    {B N d m : ℕ}
    (Q : ℕ) (w : ℝ) (ξ : BipartiteUnitVector d)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  dSVDensityRationalPublicBucketCoherentPhaseLocalUnitary
    (dSVDensityRationalPhysicalAcceptedRank w N ξ)
    (dSVDensityRationalPublicLogRankBucket Q)
    A

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/-- Retained local histories before and after the selected stopping stage. -/
abbrev UnconditionalActualCleanedSelectedRetainedIndex
    {N d L : ℕ} (j : Fin L) (R : Type) :=
  (Fin j.val → DSVUniformDensityThresholdLocalIndex N d) ×
    ((Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d) × R)

private def unconditionalActualCleanedSelectedTensorUnitary
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) :
    Matrix.unitaryGroup (ι × κ) ℂ :=
  ⟨(U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ),
    Matrix.kronecker_mem_unitary U.property V.property⟩

private def unconditionalActualCleanedSelectedStageBucketUnitary
    {B N d m : ℕ} (Q : ℕ) (w : ℝ)
    (ξ : BipartiteUnitVector d)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  unconditionalSourcePhysicalCleanedSelectedStageUnitary Q w ξ A

private def unconditionalActualCleanedSelectedStagePhysicalIndexEquiv
    (B N d m : ℕ) :
    (Σ _ : Fin B,
      DSVUniformDensityThresholdLocalIndex N d × Fin m) ≃
      UnconditionalSelectedCopyLocalIndex B d N m where
  toFun q :=
    ⟨(q.1, q.2.1.2), finProdFinEquiv (q.2.1.1, q.2.2)⟩
  invFun q :=
    let work := finProdFinEquiv.symm q.2
    ⟨q.1.1, (⟨work.1, q.1.2⟩, work.2)⟩
  left_inv := by
    rintro ⟨phase, ⟨⟨threshold, spectral⟩, harmonic⟩⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨phase, spectral⟩, work⟩
    simp only [finProdFinEquiv_symm_apply, Sigma.mk.injEq, heq_eq_eq, true_and]
    exact finProdFinEquiv.apply_symm_apply work

private def unconditionalActualCleanedSelectedStageSpectralUnitary
    {B N d m : ℕ}
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
    (unconditionalActualCleanedSelectedStagePhysicalIndexEquiv
      B N d m)
    (coherentSharedRandomControlledUnitary
      (fun _ : Fin B =>
        unconditionalActualCleanedSelectedTensorUnitary
          spectral (1 : Matrix.unitaryGroup (Fin m) ℂ)))

private def unconditionalActualCleanedSelectedFullStageUnitary
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    Matrix.unitaryGroup
      (UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m) ℂ := by
  let retained :=
    UnconditionalActualCleanedSelectedRetainedIndex
      (N := N) (d := d) j R
  let selected := UnconditionalSelectedCopyLocalIndex B d N m
  let regroup :
      UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m ≃ (Σ _ : retained, selected) :=
    (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      phaseSplit j).trans
      ((Equiv.prodComm selected retained).trans
        (Equiv.sigmaEquivProd retained selected).symm)
  exact
    unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
      regroup.symm
      (coherentSharedRandomControlledUnitary
        (fun _ : retained =>
          unconditionalActualCleanedSelectedStageBucketUnitary
            Q (width (schedule j)) ξ A *
          unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m) spectral))

private def unconditionalActualCleanedSelectedFiniteStageDecoder
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Fin (L + 1) → Matrix.unitaryGroup
      (UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m) ℂ :=
  Fin.cases 1 (fun j =>
    unconditionalActualCleanedSelectedFullStageUnitary
      phaseSplit Q width schedule ξ spectral A j)

@[simp] private theorem
    unconditionalActualCleanedSelectedFiniteStageDecoder_succ
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    unconditionalActualCleanedSelectedFiniteStageDecoder
        phaseSplit Q width schedule ξ spectral A j.succ =
      unconditionalActualCleanedSelectedFullStageUnitary
        phaseSplit Q width schedule ξ spectral A j := by
  simp only [unconditionalActualCleanedSelectedFiniteStageDecoder, Fin.cases_succ]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The type used to represent unconditional source flag controlled retained index in the exact
sampling construction.
-/
abbrev UnconditionalSourceFlagControlledRetainedIndex
    {N d L : ℕ} (j : Fin L) (R : Type) :=
  (Fin j.val → DSVUniformDensityThresholdLocalIndex N d) ×
    ((Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d) × R)

/-- The tensor product of two unitaries acting on paired local indices. -/
def unconditionalSourceFlagControlledTensorUnitary
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) :
    Matrix.unitaryGroup (ι × κ) ℂ :=
  ⟨(U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ),
    Matrix.kronecker_mem_unitary U.property V.property⟩

/-- Regroup phase, threshold, spectral, and harmonic indices into the selected-copy index. -/
def unconditionalSourceFlagControlledStagePhysicalIndexEquiv
    (B N d m : ℕ) :
    (Σ _ : Fin B,
      DSVUniformDensityThresholdLocalIndex N d × Fin m) ≃
      UnconditionalSelectedCopyLocalIndex B d N m where
  toFun q :=
    ⟨(q.1, q.2.1.2), finProdFinEquiv (q.2.1.1, q.2.2)⟩
  invFun q :=
    let work := finProdFinEquiv.symm q.2
    ⟨q.1.1, (⟨work.1, q.1.2⟩, work.2)⟩
  left_inv := by
    rintro ⟨phase, ⟨⟨threshold, spectral⟩, harmonic⟩⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨phase, spectral⟩, work⟩
    simp only [finProdFinEquiv_symm_apply, Sigma.mk.injEq, heq_eq_eq, true_and]
    exact finProdFinEquiv.apply_symm_apply work

/-- Apply the spectral unitary at each public phase, retaining the harmonic coordinate. -/
def unconditionalSourceFlagControlledStageSpectralUnitary
    {B N d m : ℕ}
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
    (unconditionalSourceFlagControlledStagePhysicalIndexEquiv
      B N d m)
    (coherentSharedRandomControlledUnitary
      (fun _ : Fin B =>
        unconditionalSourceFlagControlledTensorUnitary
          spectral (1 : Matrix.unitaryGroup (Fin m) ℂ)))

/-- Apply the unitary selected by the public phase and the accepted-rank bucket. -/
def unconditionalSourceFlagControlledStageBucketUnitary
    {B N d m : ℕ} (Q : ℕ) (w : ℝ)
    (ξ : BipartiteUnitVector d)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun q : Fin B × Fin d =>
      A q.1 (dSVDensityRationalPublicLogRankBucket Q q.1
        (dSVDensityRationalPhysicalAcceptedRank w N ξ q.2)))

/-- The controlled physical unitary at a selected stage of the scheduled source. -/
def unconditionalSourceFlagControlledFullStageUnitary
    {S B N d L m : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    Matrix.unitaryGroup
      (UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m) ℂ := by
  let retained :=
    UnconditionalSourceFlagControlledRetainedIndex
      (N := N) (d := d) j R
  let selected := UnconditionalSelectedCopyLocalIndex B d N m
  let regroup :
      UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m ≃ (Σ _ : retained, selected) :=
    (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      phaseSplit j).trans
      ((Equiv.prodComm selected retained).trans
        (Equiv.sigmaEquivProd retained selected).symm)
  exact
    unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
      regroup.symm
      (coherentSharedRandomControlledUnitary
        (fun _ : retained =>
          unconditionalSourceFlagControlledStageBucketUnitary
            Q (width (schedule j)) ξ A *
          unconditionalSourceFlagControlledStageSpectralUnitary
            (B := B) (m := m) spectral))

/-- The family of controlled decoding unitaries indexed by the stopping flag. -/
def unconditionalSourceFlagControlledFiniteStageDecoder
    {S B N d L m : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Fin (L + 1) → Matrix.unitaryGroup
      (UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m) ℂ :=
  Fin.cases 1 (fun j =>
    unconditionalSourceFlagControlledFullStageUnitary
      phaseSplit Q width schedule ξ spectral A j)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

private def unconditionalActualPhysicalMixedAcceptedRawStage
    {B N d m : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) :=
  toLp 2 fun q =>
    ePRState B (q.1.1.1, q.2.1.1) *
      dSVDensityRationalPhysicalAcceptedOutcome w N ξ ζ
        (⟨(finProdFinEquiv.symm q.1.2).1, q.1.1.2⟩,
         ⟨(finProdFinEquiv.symm q.2.2).1, q.2.1.2⟩) *
      embezzlementState m
        ((finProdFinEquiv.symm q.1.2).2,
         (finProdFinEquiv.symm q.2.2).2)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The type used to represent unconditional actual canonical retained phase index in the exact
sampling construction.
-/
abbrev UnconditionalActualCanonicalRetainedPhaseIndex (S B : ℕ) :=
  Fin (Fintype.card (Fin (S - 1) → Fin B))

/--
The unconditional actual canonical retained phase tail construction used in the quantum
parallel-repetition argument.
-/
def unconditionalActualCanonicalRetainedPhaseTail
    {S B N d L : ℕ} (j : Fin L) :
    EuclideanSpace ℂ
      (((Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d) ×
        (Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d)) ×
       (UnconditionalActualCanonicalRetainedPhaseIndex S B ×
        UnconditionalActualCanonicalRetainedPhaseIndex S B)) :=
  toLp 2 fun q =>
    dSVUniformDensityIndependentSharedState (L - j.val) N d q.1 *
      ePRState
        (Fintype.card (Fin (S - 1) → Fin B)) q.2

private def unconditionalActualCanonicalFixedSourceMatchedBranch
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    EuclideanSpace ℂ
      (UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m ×
       UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m) :=
  actualStoppingBranchVector
    (actualStoppingQuestionLocalAction
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
          S B N d L m width schedule ξ))
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
          S B N d L m width schedule ζ))
      (unconditionalSourcePhysicalCleanedStoppingFixedSource
        S B N d L m)) j.succ j.succ

private def unconditionalActualCanonicalRawSelectedPhysicalStage
    {B N d m : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) :=
  toLp 2 fun q =>
    ePRState B (q.1.1.1, q.2.1.1) *
      dSVDensityRationalPhysicalAcceptedOutcome w N ξ ζ
        (⟨(finProdFinEquiv.symm q.1.2).1, q.1.1.2⟩,
         ⟨(finProdFinEquiv.symm q.2.2).1, q.2.1.2⟩) *
      embezzlementState m
        ((finProdFinEquiv.symm q.1.2).2,
         (finProdFinEquiv.symm q.2.2).2)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/-- The positive operator-valued measurement implementing direct DSV actual reindexed retained. -/
def directDSVActualReindexedRetainedPOVM
    {C s t ι : Type*}
    [Fintype C] [Fintype s] [Fintype t] [Fintype ι]
    [DecidableEq s] [DecidableEq t] [DecidableEq ι]
    (e : ι ≃ s × t)
    (P : POVM C s) : POVM C ι :=
  reindexedPOVM e.symm (purificationAlicePOVM (k := t) P)

@[simp] theorem directDSVActualReindexedRetainedPOVM_effect
    {C s t ι : Type*}
    [Fintype C] [Fintype s] [Fintype t] [Fintype ι]
    [DecidableEq s] [DecidableEq t] [DecidableEq ι]
    (e : ι ≃ s × t)
    (P : POVM C s) (a : C) (i j : ι) :
    (directDSVActualReindexedRetainedPOVM e P).effect a i j =
      P.effect a (e i).1 (e j).1 *
        if (e i).2 = (e j).2 then 1 else 0 := by
  change
    (P.effect a ⊗ₖ (1 : Matrix t t ℂ)) (e i) (e j) = _
  simp only [kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]

/-- The finite equivalence encoding direct DSV actual bilateral retained index. -/
def directDSVActualBilateralRetainedIndexEquiv
    {s t u v ι κ : Type*}
    (eA : ι ≃ s × t) (eB : κ ≃ u × v) :
    (ι × κ) ≃ ((s × u) × (t × v)) :=
  (Equiv.prodCongr eA eB).trans
    (Equiv.prodProdProdComm s t u v)

/-- The measurement effect for direct DSV actual local POVM winning. -/
def directDSVActualLocalPOVMWinningEffect
    {X Y A B s t : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    (G : Game X Y A B)
    (PA : POVM A s) (PB : POVM B t)
    (x : X) (y : Y) : Matrix (s × t) (s × t) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      PA.effect a ⊗ₖ PB.effect b
    else 0

/-- A stopping branch uses the winning effect of its two selected measurements. -/
theorem actualStoppingBranchWinningEffect_eq_direct
    {X Y A B R : Type} {ι κ : R → Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    [∀ r, Fintype (κ r)] [∀ r, DecidableEq (κ r)]
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (r s : R) (x : X) (y : Y) :
    actualStoppingBranchWinningEffect G PA PB r s x y =
      directDSVActualLocalPOVMWinningEffect G (PA r x) (PB s y) x y := rfl

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def unconditionalSelectedRetainedBilateralRegroup
    (ι τ : Type) :
    ((ι × τ) × (ι × τ)) ≃ ((ι × ι) × (τ × τ)) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv := by rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl
  right_inv := by rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/-- The finite equivalence encoding unconditional actual fixed source retained history pair. -/
def unconditionalActualFixedSourceRetainedHistoryPairEquiv
    {N d L : ℕ} {R : Type} (j : Fin L) :
    (UnconditionalActualCleanedSelectedRetainedIndex
      (N := N) (d := d) j R ×
     UnconditionalActualCleanedSelectedRetainedIndex
      (N := N) (d := d) j R) ≃
    ((Fin j.val →
        (DSVUniformDensityThresholdLocalIndex N d ×
         DSVUniformDensityThresholdLocalIndex N d)) ×
      (((Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d) ×
        (Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d)) ×
       (R × R))) where
  toFun p :=
    ((fun i => (p.1.1 i, p.2.1 i)),
      ((p.1.2.1, p.2.2.1), (p.1.2.2, p.2.2.2)))
  invFun p :=
    ((fun i => (p.1 i).1, (p.2.1.1, p.2.2.1)),
      (fun i => (p.1 i).2, (p.2.1.2, p.2.2.2)))
  left_inv := by
    rintro ⟨⟨beforeA, afterA, phaseA⟩,
      ⟨beforeB, afterB, phaseB⟩⟩
    simp only
  right_inv := by
    rintro ⟨before, ⟨⟨afterA, afterB⟩, ⟨phaseA, phaseB⟩⟩⟩
    simp only [Prod.mk.eta]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

/-- The finite equivalence encoding physical 8 selected global target work. -/
def physical8SelectedGlobalTargetWorkEquiv
    (P N d m : ℕ) :
    UnconditionalSelectedCopyLocalIndex P d N m ≃
      Fin d × (Fin P × Fin (N * m)) where
  toFun q := (q.1.2, (q.1.1, q.2))
  invFun q := ⟨(q.2.1, q.1), q.2.2⟩
  left_inv := by
    rintro ⟨⟨phase, atom⟩, work⟩
    rfl
  right_inv := by
    rintro ⟨atom, phase, work⟩
    rfl

/-- The finite equivalence encoding physical 8 one scale actual global fiber. -/
def physical8OneScaleActualGlobalFiberEquiv
    {P N d L m : ℕ} {R : Type}
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (j : Fin L) :
    UnconditionalSourcePhysicalStoppingPhaseFiber 1 P N d L m ≃
      Fin d ×
        ((Fin P × Fin (N * m)) ×
          UnconditionalSourceFlagControlledRetainedIndex
            (N := N) (d := d) j R) :=
  (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      phaseSplit j).trans
    ((Equiv.prodCongr
        (physical8SelectedGlobalTargetWorkEquiv P N d m)
        (Equiv.refl
          (UnconditionalSourceFlagControlledRetainedIndex
            (N := N) (d := d) j R))).trans
      (Equiv.prodAssoc (Fin d) (Fin P × Fin (N * m))
        (UnconditionalSourceFlagControlledRetainedIndex
          (N := N) (d := d) j R)))

/-- The positive operator-valued measurement implementing physical 8 one scale original flag. -/
def physical8OneScaleOriginalFlagPOVM
    {C Z : Type*} [Fintype C] [DecidableEq C]
    {P N d L m : ℕ} {R : Type}
    [Fintype R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (default : C) (sourcePOVM : Z → POVM C (Fin d)) :
    Fin (L + 1) → Z →
      POVM C
        (UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m) :=
  Fin.cases
    (fun _ => deterministicOutcomePOVM default)
    (fun j x =>
      directDSVActualReindexedRetainedPOVM
        (physical8OneScaleActualGlobalFiberEquiv
          (N := N) (d := d) (m := m) phaseSplit j)
        (sourcePOVM x))

/-- The unitary operator implementing physical 8 one scale actual alice stopping. -/
def physical8OneScaleActualAliceStoppingUnitary
    {F Z : Type*} {P N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (Q : ℕ) (width : Fin 1 → ℝ)
    (schedule : Fin L → Fin 1)
    (target : F → Z → BipartiteUnitVector d)
    (cleanup : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    F → Z → Matrix.unitaryGroup
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m) ℂ :=
  fun flag x =>
    coherentSharedRandomControlledUnitary
        (unconditionalSourceFlagControlledFiniteStageDecoder
          phaseSplit Q width schedule (target flag x)
          (dSVUniformDensityAliceHistorySpectralCopy
            (N := N) (target flag x)) cleanup) *
      unconditionalSourcePhysicalCleanedTargetFirstUnitary
        1 P N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
          1 P N d L m width schedule (target flag x))

/-- The unitary operator implementing physical 8 one scale actual bob stopping. -/
def physical8OneScaleActualBobStoppingUnitary
    {F Z : Type*} {P N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (Q : ℕ) (width : Fin 1 → ℝ)
    (schedule : Fin L → Fin 1)
    (target : F → Z → BipartiteUnitVector d)
    (cleanup : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    F → Z → Matrix.unitaryGroup
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m) ℂ :=
  fun flag y =>
    coherentSharedRandomControlledUnitary
        (unconditionalSourceFlagControlledFiniteStageDecoder
          phaseSplit Q width schedule (target flag y)
          ((dSVUniformDensityBobHistoryCopyBasis
            (N := N) (target flag y))⁻¹) cleanup) *
      unconditionalSourcePhysicalCleanedTargetFirstUnitary
        1 P N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
          1 P N d L m width schedule (target flag y))

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The unconditional actual one scale fixed source phase split construction used in the quantum
parallel-repetition argument.
-/
def unconditionalActualOneScaleFixedSourcePhaseSplit (P : ℕ) :
    DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
      Fin P × UnconditionalActualCanonicalRetainedPhaseIndex 1 P :=
  (unconditionalActualMultiscalePhaseIndexEquiv
    (B := P) (0 : Fin 1)).symm

private def unconditionalActualOneScaleFixedSourceDecodedState
    {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    EuclideanSpace ℂ
      ((Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N d L m) ×
       (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N d L m)) :=
  dSVUniformDensityPhysicalAsyncSigmaContinuation
    (unconditionalSourceFlagControlledFiniteStageDecoder
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      Q width schedule ξ
      (dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ) A)
    (unconditionalSourceFlagControlledFiniteStageDecoder
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      Q width schedule ζ
      ((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ζ)⁻¹) C)
    (actualStoppingQuestionLocalAction
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        1 P N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
          1 P N d L m width schedule ξ))
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        1 P N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
          1 P N d L m width schedule ζ))
      (unconditionalSourcePhysicalCleanedStoppingFixedSource
        1 P N d L m))

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The unconditional exact fair gamma unit construction used in the quantum parallel-repetition
argument.
-/
def unconditionalExactFairGammaUnit
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (u : ExactLocallySampleableTuple X Y A B D) :
    BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  ⟨exactSourceTupleGamma G n S D u,
    exactSourceTupleGamma_norm G n S D u⟩

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/--
The type used to represent integrator actual c 485 tail index in the exact sampling
construction.
-/
abbrev IntegratorActualC485TailIndex
    (S B N d L : ℕ) (j : Fin L) :=
  (((Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d) ×
    (Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d)) ×
   (UnconditionalActualCanonicalRetainedPhaseIndex S B ×
    UnconditionalActualCanonicalRetainedPhaseIndex S B))

/--
The type used to represent integrator actual c 485 retained index in the exact sampling
construction.
-/
abbrev IntegratorActualC485RetainedIndex
    (S B N d L : ℕ) (j : Fin L) :=
  (Fin j.val →
    (DSVUniformDensityThresholdLocalIndex N d ×
     DSVUniformDensityThresholdLocalIndex N d)) ×
    IntegratorActualC485TailIndex S B N d L j

/--
The type used to represent integrator actual c 485 branch space in the exact sampling
construction.
-/
abbrev IntegratorActualC485BranchSpace
    (S B N d L m : ℕ) (j : Fin L) :=
  EuclideanSpace ℂ
    ((UnconditionalSelectedCopyLocalIndex B d N m ×
      UnconditionalSelectedCopyLocalIndex B d N m) ×
     IntegratorActualC485RetainedIndex S B N d L j)

/-- The original retained prefix and canonical phase tail at the selected stage. -/
def integratorActualC485OriginalRetainedWork
    {S B N d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    EuclideanSpace ℂ
      (IntegratorActualC485RetainedIndex S B N d L j) :=
  unconditionalSelectedCopyRetainedWork
    (N := N) width schedule ξ ζ j
    (unconditionalActualCanonicalRetainedPhaseTail
      (S := S) (B := B) (N := N) (d := d) (L := L) j)

/--
The integrator actual c 485 normalized diagonal work construction used in the quantum parallel-
repetition argument.
-/
def integratorActualC485NormalizedDiagonalWork
    {S B N d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    EuclideanSpace ℂ
      (IntegratorActualC485RetainedIndex S B N d L j) :=
  (‖dSVDensityRationalCanonicalAcceptedTarget
      (width (schedule j)) N ξ‖ /
    Real.sqrt (width (schedule j) * (d : ℝ))) •
      integratorActualC485OriginalRetainedWork
        (B := B) width schedule ξ ζ j

open Classical in
/-- The state vector representing integrator actual c 485 cleaned. -/
def integratorActualC485CleanedVector
    {S B N d L m : ℕ}
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    IntegratorActualC485BranchSpace S B N d L m j :=
  unconditionalMixedConjugateSelectedBranchLocalAction
    (unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) B
      (conjugateUnitary
        (dSVDensityRationalCanonicalAliceBasis ξ)))
    (unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) B
      (conjugateUnitary
        (dSVUniformDensityThresholdLeftBobBasis ζ)))
    (unconditionalSelectedCopyCleanedMatchedBranch
      (N := N) (B := B) (m := m)
      Q width schedule ξ ζ A C j
      (unconditionalActualCanonicalRetainedPhaseTail
        (S := S) (B := B) (N := N) (d := d) (L := L) j))

/-- The state vector representing integrator actual c 485 canonical. -/
def integratorActualC485CanonicalVector
    {S B N d L m : ℕ}
    {width : Fin S → ℝ}
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L)
    (positive : 0 < width (schedule j))
    (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    IntegratorActualC485BranchSpace S B N d L m j :=
  unconditionalMatchedVerifierTensor
    (dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
      (unconditionalConjugatePureVector
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          positive grid fine ξ).val)
      (fun _ _ _ => embezzlementState (N * m)))
    (integratorActualC485NormalizedDiagonalWork
      (B := B) width schedule ξ ζ j)

/-- The state vector representing integrator actual c 485 source. -/
def integratorActualC485SourceVector
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (ψ : EuclideanSpace ℂ (Fin d × Fin d))
    (j : Fin L) :
    IntegratorActualC485BranchSpace S B N d L m j :=
  unconditionalMatchedVerifierTensor
    (dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
      (unconditionalConjugatePureVector ψ)
      (fun _ _ _ => embezzlementState (N * m)))
    (integratorActualC485NormalizedDiagonalWork
      (B := B) width schedule ξ ζ j)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

end

section

open scoped BigOperators

open QuantumParallelRepetition.ClassicalSampling

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/-- The positive operator-valued measurement implementing integrator actual c 485 source alice. -/
def integratorActualC485SourceAlicePOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (x : X) :
    POVM A
      (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))) := by
  classical
  exact
    reindexedPOVM
      (finCongr
        (Nat.mul_one
          (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))))
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystAlicePOVM G n S D 1 a₀ x))

/-- The positive operator-valued measurement implementing integrator actual c 485 source bob. -/
def integratorActualC485SourceBobPOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (b₀ : B) (y : Y) :
    POVM B
      (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))) := by
  classical
  exact
    reindexedPOVM
      (finCongr
        (Nat.mul_one
          (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))))
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystBobPOVM G n S D 1 b₀ y))

/-- The positive operator-valued measurement implementing integrator actual c 485 selected alice. -/
def integratorActualC485SelectedAlicePOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A)
    (P N m : ℕ) (x : X) :
    POVM A
      (UnconditionalSelectedCopyLocalIndex
        P (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        N m) := by
  classical
  exact
    directDSVActualReindexedRetainedPOVM
      (physical8SelectedGlobalTargetWorkEquiv
        P N (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) m)
      (integratorActualC485SourceAlicePOVM G n S D a₀ x)

/-- The positive operator-valued measurement implementing integrator actual c 485 selected bob. -/
def integratorActualC485SelectedBobPOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (b₀ : B)
    (P N m : ℕ) (y : Y) :
    POVM B
      (UnconditionalSelectedCopyLocalIndex
        P (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        N m) := by
  classical
  exact
    directDSVActualReindexedRetainedPOVM
      (physical8SelectedGlobalTargetWorkEquiv
        P N (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) m)
      (integratorActualC485SourceBobPOVM G n S D b₀ y)

/-- The measurement effect for integrator actual c 485 winning. -/
def integratorActualC485WinningEffect
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (j : Fin L) (x : X) (y : Y) :
    IntegratorActualC485BranchSpace
      1 P N
        (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        L m j →L[ℂ]
      IntegratorActualC485BranchSpace
        1 P N
          (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
          L m j := by
  classical
  let d : ℕ :=
    Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
  let selected : Type := UnconditionalSelectedCopyLocalIndex
    P d N m
  let retained : Type :=
    IntegratorActualC485RetainedIndex 1 P N d L j
  exact Matrix.toEuclideanCLM
    (n := (selected × selected) × retained) (𝕜 := ℂ)
    (directDSVActualLocalPOVMWinningEffect G
      (integratorActualC485SelectedAlicePOVM
        G n S D a₀ P N m x)
      (integratorActualC485SelectedBobPOVM
        G n S D b₀ P N m y) x y ⊗ₖ
      (1 : Matrix retained retained ℂ))

private def unconditionalActualFairSourceBaseWinningCLM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    (x : X) (y : Y) :
    ExactSourceGlobalState G n S D →L[ℂ]
      ExactSourceGlobalState G n S D := by
  classical
  exact Matrix.toEuclideanCLM (𝕜 := ℂ)
    (directDSVActualLocalPOVMWinningEffect G
      (integratorActualC485SourceAlicePOVM G n S D a₀ x)
      (integratorActualC485SourceBobPOVM G n S D b₀ y)
      x y)

private def unconditionalActualFairSourcePhaseHarmonicWork
    (P k : ℕ) :
    EuclideanSpace ℂ
      ((Fin P × Fin k) × (Fin P × Fin k)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodProdProdComm
      (Fin P) (Fin P) (Fin k) (Fin k))
    (unconditionalMatchedVerifierTensor
      (ePRState P) (embezzlementState k))

end

end QuantumParallelRepetition

end
