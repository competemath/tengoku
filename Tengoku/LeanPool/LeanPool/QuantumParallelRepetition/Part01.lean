/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import Tengoku

/-! # Quantum parallel repetition, part 01 -/

@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

/-- The local matrix norm instance used while elaborating part one. -/
noncomputable local instance matrixComplexContinuousENormPartOne
    {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix m n ℂ)
    (Matrix.normedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup)

/-- The local matrix norm instance used while elaborating part one. -/
noncomputable local instance matrixComplexESeminormedAddCommMonoidPartOne
    {m n : Type*} [Fintype m] [Fintype n] :
    ESeminormedAddCommMonoid (Matrix m n ℂ) :=
  let base := @NormedAddCommGroup.toENormedAddCommMonoid (Matrix m n ℂ)
    Matrix.normedAddCommGroup
  { toContinuousENorm := inferInstance
    toAddCommMonoid := base.toAddCommMonoid
    enorm_zero := base.enorm_zero
    enorm_add_le := base.enorm_add_le }

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

variable {X Y A B : Type*}

/-- A finite two-player nonlocal game with a question distribution and winning predicate. -/
structure Game (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  /-- The probability weight assigned to a pair of questions. -/
  questionWeight : X → Y → ℝ
  weight_nonneg : ∀ x y, 0 ≤ questionWeight x y
  weight_normalized : (∑ x : X, ∑ y : Y, questionWeight x y) = 1
  /-- The Boolean predicate deciding whether a pair of answers wins. -/
  predicate : X → Y → A → B → Bool

namespace Game

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The first-question marginal of a game. -/
def marginalX (G : Game X Y A B) (x : X) : ℝ :=
  ∑ y : Y, G.questionWeight x y

/-- The second-question marginal of a game. -/
def marginalY (G : Game X Y A B) (y : Y) : ℝ :=
  ∑ x : X, G.questionWeight x y

/--
@isnad1 id=le.0h6v.s5.23dd5b301a83 from=translated src=- shape=02254200 vocab=6b3273ab
-/
theorem marginalX_nonneg (G : Game X Y A B) (x : X) :
    0 ≤ G.marginalX x := by
  unfold marginalX
  exact Finset.sum_nonneg fun y _ => G.weight_nonneg x y

/--
@isnad1 id=le.0h6v.s5.8e0e45c5d09b from=translated src=- shape=9569fe2b vocab=44486f45
-/
theorem marginalY_nonneg (G : Game X Y A B) (y : Y) :
    0 ≤ G.marginalY y := by
  unfold marginalY
  exact Finset.sum_nonneg fun x _ => G.weight_nonneg x y

/-- The coordinatewise repeated game. -/
def «repeat» (G : Game X Y A B) (n : ℕ) :
    Game (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) where
  questionWeight xs ys := ∏ i : Fin n, G.questionWeight (xs i) (ys i)
  weight_nonneg xs ys :=
    Finset.prod_nonneg fun i _ => G.weight_nonneg (xs i) (ys i)
  weight_normalized := by
    classical
    calc
      (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        ∏ i : Fin n, G.questionWeight (xs i) (ys i)) =
          ∑ xs : Fin n → X, ∏ i : Fin n, ∑ y : Y,
            G.questionWeight (xs i) y := by
              apply Finset.sum_congr rfl
              intro xs _
              exact (Fintype.prod_sum
                (fun i : Fin n => fun y : Y => G.questionWeight (xs i) y)).symm
      _ = ∏ _i : Fin n, ∑ x : X, ∑ y : Y,
            G.questionWeight x y := by
              exact (Fintype.prod_sum
                (fun _i : Fin n => fun x : X => ∑ y : Y,
                  G.questionWeight x y)).symm
      _ = 1 := by simp only [G.weight_normalized, Finset.prod_const_one]
  predicate xs ys as bs :=
    decide (∀ i : Fin n, G.predicate (xs i) (ys i) (as i) (bs i) = true)

/--
@isnad1 id=eq.0h8v.s7.01e39c814763 from=translated src=- shape=30d00d5d vocab=ca3ecda3
-/
@[simp] theorem repeat_questionWeight (G : Game X Y A B) (n : ℕ)
    (xs : Fin n → X) (ys : Fin n → Y) :
    (G.repeat n).questionWeight xs ys =
      ∏ i : Fin n, G.questionWeight (xs i) (ys i) := rfl

/--
@isnad1 id=iff.0h10v.s7.e576bf84e13c from=translated src=- shape=925c9eb4 vocab=8cdc97e9
-/
@[simp] theorem repeat_predicate_eq_true (G : Game X Y A B) (n : ℕ)
    (xs : Fin n → X) (ys : Fin n → Y)
    (as : Fin n → A) (bs : Fin n → B) :
    (G.repeat n).predicate xs ys as bs = true ↔
      ∀ i : Fin n, G.predicate (xs i) (ys i) (as i) (bs i) = true := by
  simp only [«repeat», decide_eq_true_eq]

end Game

/-- A finite-dimensional positive semidefinite matrix of trace one. -/
structure DensityMatrix (d : Type*) [Fintype d] where
  /-- The matrix underlying a density matrix. -/
  matrix : Matrix d d ℂ
  positive : matrix.PosSemidef
  trace_one : Matrix.trace matrix = 1

/-- A finite-outcome positive operator-valued measurement. -/
structure POVM (ι d : Type*) [Fintype ι] [Fintype d] [DecidableEq d] where
  /-- The positive operator associated with a measurement outcome. -/
  effect : ι → Matrix d d ℂ
  positive : ∀ i, (effect i).PosSemidef
  complete : (∑ i : ι, effect i) = 1

/-- A finite-dimensional entangled strategy for a nonlocal game. -/
structure Strategy [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (_G : Game X Y A B) where
  /-- Alice's finite Hilbert-space basis type. -/
  Alice : Type
  /-- Bob's finite Hilbert-space basis type. -/
  Bob : Type
  [aliceFintype : Fintype Alice]
  [bobFintype : Fintype Bob]
  [aliceDecidableEq : DecidableEq Alice]
  [bobDecidableEq : DecidableEq Bob]
  /-- The shared bipartite state of the strategy. -/
  state : DensityMatrix (Alice × Bob)
  /-- Alice's measurement for each question. -/
  aliceMeasurement : X → POVM A Alice
  /-- Bob's measurement for each question. -/
  bobMeasurement : Y → POVM B Bob

attribute [instance] Strategy.aliceFintype Strategy.bobFintype
  Strategy.aliceDecidableEq Strategy.bobDecidableEq

/--
@isnad1 id=le.2h3v.s6.f522a6094be5 from=translated src=- shape=fea69071 vocab=32511440
-/
theorem trace_mul_posSemidef_nonneg {d : Type*} [Fintype d]
    {R E : Matrix d d ℂ} (hR : R.PosSemidef) (hE : E.PosSemidef) :
    0 ≤ (Matrix.trace (R * E)).re := by
  classical
  obtain ⟨K, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  have hpositive : (K * E * star K).PosSemidef := by
    simpa only [star_eq_conjTranspose] using hE.mul_mul_conjTranspose_same K
  have htrace : 0 ≤ (Matrix.trace (K * E * star K)).re :=
    (Complex.nonneg_iff.mp hpositive.trace_nonneg).1
  rw [Matrix.trace_mul_cycle] at htrace
  exact htrace

namespace Strategy

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

/-- The tensor product of Alice's and Bob's effects for a joint outcome. -/
def jointEffect (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ :=
  (S.aliceMeasurement x).effect a ⊗ₖ (S.bobMeasurement y).effect b

private theorem jointEffect_positive (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    (S.jointEffect x y a b).PosSemidef := by
  exact ((S.aliceMeasurement x).positive a).kronecker
    ((S.bobMeasurement y).positive b)

/-- The Born probability of a question-and-answer outcome. -/
def outcomeProbability (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  (Matrix.trace (S.state.matrix * S.jointEffect x y a b)).re

/--
@isnad1 id=le.0h10v.s6.53922c9e8bbf from=translated src=- shape=6e8d6d22 vocab=e575a5d0
-/
theorem outcomeProbability_nonneg (S : Strategy G)
    (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.outcomeProbability x y a b := by
  exact trace_mul_posSemidef_nonneg S.state.positive
    (S.jointEffect_positive x y a b)

private theorem jointEffect_complete (S : Strategy G) (x : X) (y : Y) :
    (∑ a : A, ∑ b : B, S.jointEffect x y a b) = 1 := by
  classical
  calc
    (∑ a : A, ∑ b : B, S.jointEffect x y a b) =
        (∑ a : A, (S.aliceMeasurement x).effect a) ⊗ₖ
          (∑ b : B, (S.bobMeasurement y).effect b) := by
            ext ⟨i, j⟩ ⟨k, l⟩
            simp only [jointEffect, Matrix.sum_apply, Matrix.kroneckerMap_apply]
            rw [Finset.sum_mul]
            simp_rw [Finset.mul_sum]
    _ = 1 := by
      rw [(S.aliceMeasurement x).complete, (S.bobMeasurement y).complete]
      exact Matrix.one_kronecker_one

/--
@isnad1 id=eq.0h8v.s6.97c03a48b02c from=translated src=- shape=387dd337 vocab=0d65db48
-/
theorem outcomeProbability_normalized (S : Strategy G) (x : X) (y : Y) :
    (∑ a : A, ∑ b : B, S.outcomeProbability x y a b) = 1 := by
  classical
  calc
    (∑ a : A, ∑ b : B, S.outcomeProbability x y a b) =
        (Matrix.trace
          (S.state.matrix * (∑ a : A, ∑ b : B, S.jointEffect x y a b))).re := by
            simp only [outcomeProbability, Matrix.mul_sum, trace_sum, Complex.re_sum]
    _ = (Matrix.trace S.state.matrix).re := by
      rw [S.jointEffect_complete x y]
      simp only [mul_one]
    _ = 1 := by rw [S.state.trace_one]; rfl

/-- The winning probability of the strategy. -/
def winProbability (S : Strategy G) : ℝ :=
  ∑ x : X, ∑ y : Y, G.questionWeight x y *
    ∑ a : A, ∑ b : B,
      if G.predicate x y a b = true then S.outcomeProbability x y a b else 0

end Strategy

/-- The supremal winning probability over finite-dimensional entangled strategies. -/
def entangledValue [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) : ℝ :=
  sSup (Set.range (Strategy.winProbability (G := G)))

/-- The entangled value of a coordinatewise repeated game. -/
def repeatedEntangledValue [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) : ℝ :=
  entangledValue (G.repeat n)

end

section

open scoped BigOperators ComplexConjugate InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The quadratic expectation construction used in the quantum parallel-repetition argument. -/
def quadraticExpectation (W : H →L[ℂ] H) (z : H) : ℝ :=
  (⟪z, W z⟫_ℂ).re

end

section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Strategy

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

/-- The measurement effect for winning. -/
def winningEffect (S : Strategy G) (x : X) (y : Y) :
    Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then S.jointEffect x y a b else 0

end Strategy

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

variable {X Y A B : Type*} {J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype J] [DecidableEq J]
variable {G : Game X Y A B}

/--
@isnad1 id=possemid.1h3v.s6.258b96fda66d from=translated src=- shape=d334933c vocab=3b2e22f7
-/
theorem posSemidef_blockDiagonal'
    {ι : Type*} [Finite ι] [DecidableEq ι]
    {d : ι → Type*} [∀ j, Finite (d j)]
    (M : ∀ j, Matrix (d j) (d j) ℂ)
    (hM : ∀ j, (M j).PosSemidef) :
    (Matrix.blockDiagonal' M).PosSemidef := by
  classical
  let _ := Fintype.ofFinite ι
  let _ (j : ι) := Fintype.ofFinite (d j)
  choose K hK using fun j =>
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hM j).nonneg
  apply Matrix.LE.le.posSemidef
  apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr
  refine ⟨Matrix.blockDiagonal' K, ?_⟩
  calc
    Matrix.blockDiagonal' M =
        Matrix.blockDiagonal' (fun j => star (K j) * K j) := by
          congr 1
          funext j
          exact hK j
    _ = star (Matrix.blockDiagonal' K) * Matrix.blockDiagonal' K := by
          simp only [star_eq_conjTranspose, blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]

/-- Alice's direct-sum index, retaining the chosen component of the mixture. -/
abbrev mixtureAlice (S : J → Strategy G) := Σ j : J, (S j).Alice

/-- Bob's direct-sum index, retaining the chosen component of the mixture. -/
abbrev mixtureBob (S : J → Strategy G) := Σ j : J, (S j).Bob

/-- Joint indices whose two players use the same mixture component. -/
abbrev mixtureMatched (S : J → Strategy G) :=
  Σ j : J, (S j).Alice × (S j).Bob

/-- Embed matching component indices into the product of the two direct sums. -/
def mixtureMatchedIndex (S : J → Strategy G) :
    mixtureMatched S → mixtureAlice S × mixtureBob S
  | ⟨j, (a, b)⟩ => (⟨j, a⟩, ⟨j, b⟩)

omit [Fintype J] [DecidableEq J] in
private theorem mixtureMatchedIndex_injective (S : J → Strategy G) :
    Function.Injective (mixtureMatchedIndex S) := by
  rintro ⟨i, a, b⟩ ⟨j, c, d⟩ h
  have hflag : i = j := congrArg (fun q => q.1.1) h
  subst j
  have ha : a = c :=
    eq_of_heq (Sigma.mk.inj (congrArg Prod.fst h)).2
  have hb : b = d :=
    eq_of_heq (Sigma.mk.inj (congrArg Prod.snd h)).2
  subst c
  subst d
  rfl

/-- The matrix embedding the matching component blocks into the joint space. -/
def mixtureEmbedding (S : J → Strategy G) :
    Matrix (mixtureAlice S × mixtureBob S) (mixtureMatched S) ℂ := by
  classical
  exact fun q r => if q = mixtureMatchedIndex S r then 1 else 0

/--
@isnad1 id=eq.0h7v.s9.7566137976d3 from=translated src=- shape=d9ed5d12 vocab=eee95902
-/
theorem mixtureEmbedding_isometry (S : J → Strategy G) :
    (mixtureEmbedding S)ᴴ * mixtureEmbedding S = 1 := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    simp only [Matrix.mul_apply, conjTranspose_apply, mixtureEmbedding, RCLike.star_def,
      MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, one_apply_eq]
  · have hindex : mixtureMatchedIndex S i ≠ mixtureMatchedIndex S j :=
      fun hij => h (mixtureMatchedIndex_injective S hij)
    simp only [Matrix.mul_apply, conjTranspose_apply, mixtureEmbedding, RCLike.star_def,
      MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, hindex.symm, ne_eq, h, not_false_eq_true, one_apply_ne]

/-- The block-diagonal state matrix weighted by the mixture probabilities. -/
def mixtureBlockMatrix (p : J → ℝ) (S : J → Strategy G) :
    Matrix (mixtureMatched S) (mixtureMatched S) ℂ :=
  Matrix.blockDiagonal' fun j => p j • (S j).state.matrix

omit [Fintype J] in
/--
@isnad1 id=possemid.1h8v.s6.c7ba94bf79f6 from=translated src=- shape=2e1afdc1 vocab=d8f08fe1
-/
theorem mixtureBlockMatrix_posSemidef
    [Finite J]
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (S : J → Strategy G) :
    (mixtureBlockMatrix p S).PosSemidef := by
  unfold mixtureBlockMatrix
  apply posSemidef_blockDiagonal'
  intro j
  exact (S j).state.positive.smul (hp j)

/--
@isnad1 id=eq.0h8v.s7.da08e790f73b from=translated src=- shape=c739b16a vocab=96b2e536
-/
theorem mixtureBlockMatrix_trace
    (p : J → ℝ) (S : J → Strategy G) :
    Matrix.trace (mixtureBlockMatrix p S) =
      (↑(∑ j : J, p j) : ℂ) := by
  unfold mixtureBlockMatrix
  rw [Matrix.trace_blockDiagonal']
  simp only [trace_smul, DensityMatrix.trace_one, Complex.real_smul, mul_one, Complex.ofReal_sum]

/-- The density matrix of the mixture, supported on matching component blocks. -/
def mixtureDensityMatrix (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (h_normalized : (∑ j : J, p j) = 1)
    (S : J → Strategy G) :
    DensityMatrix (mixtureAlice S × mixtureBob S) where
  matrix := mixtureEmbedding S * mixtureBlockMatrix p S *
    (mixtureEmbedding S)ᴴ
  positive :=
    (mixtureBlockMatrix_posSemidef p hp S).mul_mul_conjTranspose_same
      (mixtureEmbedding S)
  trace_one := by
    rw [Matrix.trace_mul_cycle, mixtureEmbedding_isometry,
      Matrix.one_mul, mixtureBlockMatrix_trace, h_normalized]
    norm_num

/-- Alice's measurement acting separately on each mixture component. -/
def mixtureAlicePOVM (S : J → Strategy G) (x : X) :
    POVM A (mixtureAlice S) where
  effect a := Matrix.blockDiagonal' fun j =>
    ((S j).aliceMeasurement x).effect a
  positive a := by
    apply posSemidef_blockDiagonal'
    intro j
    exact ((S j).aliceMeasurement x).positive a
  complete := by
    classical
    ext ⟨i, u⟩ ⟨j, v⟩
    by_cases h : i = j
    · subst j
      have h_complete := congrArg
        (fun M : Matrix (S i).Alice (S i).Alice ℂ => M u v)
        ((S i).aliceMeasurement x).complete
      simpa only [Matrix.sum_apply, blockDiagonal'_apply, ↓reduceDIte, cast_eq, Matrix.one_apply,
        Sigma.mk.injEq, heq_eq_eq, true_and] using h_complete
    · simp only [Matrix.sum_apply, blockDiagonal'_apply, h, ↓reduceDIte, Finset.sum_const_zero,
        ne_eq, Sigma.mk.injEq, false_and, not_false_eq_true, one_apply_ne]

/-- Bob's measurement acting separately on each mixture component. -/
def mixtureBobPOVM (S : J → Strategy G) (y : Y) :
    POVM B (mixtureBob S) where
  effect b := Matrix.blockDiagonal' fun j =>
    ((S j).bobMeasurement y).effect b
  positive b := by
    apply posSemidef_blockDiagonal'
    intro j
    exact ((S j).bobMeasurement y).positive b
  complete := by
    classical
    ext ⟨i, u⟩ ⟨j, v⟩
    by_cases h : i = j
    · subst j
      have h_complete := congrArg
        (fun M : Matrix (S i).Bob (S i).Bob ℂ => M u v)
        ((S i).bobMeasurement y).complete
      simpa only [Matrix.sum_apply, blockDiagonal'_apply, ↓reduceDIte, cast_eq, Matrix.one_apply,
        Sigma.mk.injEq, heq_eq_eq, true_and] using h_complete
    · simp only [Matrix.sum_apply, blockDiagonal'_apply, h, ↓reduceDIte, Finset.sum_const_zero,
        ne_eq, Sigma.mk.injEq, false_and, not_false_eq_true, one_apply_ne]

/-- A strategy that shares a component label and plays that component's strategy. -/
def convexMixtureStrategy (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (h_normalized : (∑ j : J, p j) = 1)
    (S : J → Strategy G) : Strategy G where
  Alice := mixtureAlice S
  Bob := mixtureBob S
  aliceFintype := inferInstance
  bobFintype := inferInstance
  aliceDecidableEq := inferInstance
  bobDecidableEq := inferInstance
  state := mixtureDensityMatrix p hp h_normalized S
  aliceMeasurement := mixtureAlicePOVM S
  bobMeasurement := mixtureBobPOVM S

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/-- The matrix representation of pure density. -/
def pureDensityMatrix
    {d : Type*} [Fintype d]
    (z : EuclideanSpace ℂ d) (hz : ‖z‖ = 1) : DensityMatrix d where
  matrix := Matrix.vecMulVec (ofLp z) (star (ofLp z))
  positive := Matrix.posSemidef_vecMulVec_self_star (ofLp z)
  trace_one := by
    rw [Matrix.trace_vecMulVec,
      ← EuclideanSpace.inner_eq_star_dotProduct z z,
      inner_self_eq_norm_sq_to_K, hz]
    norm_num

/-- The strategy implementing pure vector. -/
def pureVectorStrategy
    {X Y A B : Type*} {dA dB : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB) : Strategy G where
  Alice := dA
  Bob := dB
  aliceFintype := inferInstance
  bobFintype := inferInstance
  aliceDecidableEq := inferInstance
  bobDecidableEq := inferInstance
  state := pureDensityMatrix z hz
  aliceMeasurement := PA
  bobMeasurement := PB

/-- The strategy implementing pure flagged. -/
def pureFlaggedStrategy
    {X Y A B : Type*} {dA dB J : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    [Fintype J] [DecidableEq J]
    (G : Game X Y A B)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (h_normalized : (∑ j : J, p j) = 1)
    (z : J → EuclideanSpace ℂ (dA × dB))
    (hz : ∀ j, ‖z j‖ = 1)
    (PA : J → X → POVM A dA)
    (PB : J → Y → POVM B dB) : Strategy G :=
  convexMixtureStrategy p hp h_normalized
    (fun j => pureVectorStrategy G (z j) (hz j) (PA j) (PB j))

end

section

open scoped BigOperators

/-- A normalized nonnegative probability law on a finite sample space. -/
structure FiniteEventLaw (Ω : Type*) [Fintype Ω] where
  /-- The probability weight of a sample point. -/
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum : (∑ ω, weight ω) = 1

namespace FiniteEventLaw

variable {Ω ι : Type*} [Fintype Ω]

/-- The probability mass of a finite event. -/
def eventMass (law : FiniteEventLaw Ω) (event : Finset Ω) : ℝ :=
  ∑ ω ∈ event, law.weight ω

/-- The event on which every selected coordinate wins. -/
def winEvent
    (wins : ι → Ω → Bool) (D : Finset ι) : Finset Ω :=
  Finset.univ.filter (fun ω => ∀ i ∈ D, wins i ω = true)

/-- Membership in a finite-law win event is pointwise winning at every selected index.
@isnad1 id=iff.0h5v.s5.5c0ca8756728 from=translated src=- shape=a0c71414 vocab=f221b575
-/
theorem mem_winEvent_iff
    (wins : ι → Ω → Bool) (D : Finset ι) (ω : Ω) :
    ω ∈ winEvent wins D ↔ ∀ i ∈ D, wins i ω = true := by
  classical
  simp only [winEvent, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The conditional mass of failure at a selected coordinate. -/
def failureMass [DecidableEq ι]
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (D : Finset ι) (i : ι) : ℝ :=
  law.eventMass (winEvent wins D) -
    law.eventMass (winEvent wins (insert i D))

end FiniteEventLaw

section StrategyEventLaw

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The type used to represent strategy outcome in the exact sampling construction. -/
abbrev StrategyOutcome (X Y A B : Type*) :=
  X × Y × A × B

/-- The finite probability law for strategy event. -/
def strategyEventLaw (G : Game X Y A B) (S : Strategy G) :
    FiniteEventLaw (StrategyOutcome X Y A B) where
  weight ω :=
    G.questionWeight ω.1 ω.2.1 *
      S.outcomeProbability ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  weight_nonneg ω :=
    mul_nonneg (G.weight_nonneg ω.1 ω.2.1)
      (S.outcomeProbability_nonneg
        ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
  weight_sum := by
    classical
    change
      (∑ ω : X × Y × A × B,
        G.questionWeight ω.1 ω.2.1 *
          S.outcomeProbability
            ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) = 1
    simp_rw [Fintype.sum_prod_type]
    calc
      (∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
        G.questionWeight x y *
          S.outcomeProbability x y a b) =
        ∑ x : X, ∑ y : Y,
          G.questionWeight x y *
            (∑ a : A, ∑ b : B,
              S.outcomeProbability x y a b) := by
                apply Finset.sum_congr rfl
                intro x _
                apply Finset.sum_congr rfl
                intro y _
                simp only [Finset.mul_sum]
      _ = ∑ x : X, ∑ y : Y,
          G.questionWeight x y * 1 := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            rw [S.outcomeProbability_normalized x y]
      _ = 1 := by
            simpa only [mul_one] using G.weight_normalized

private def strategyWinEvent (G : Game X Y A B) :
    Finset (StrategyOutcome X Y A B) :=
  Finset.univ.filter
    (fun ω =>
      G.predicate ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = true)

/-- The repeated coordinate win construction used in the quantum parallel-repetition argument. -/
def repeatedCoordinateWin (G : Game X Y A B) (n : ℕ)
    (i : Fin n)
    (ω : StrategyOutcome
      (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B)) : Bool :=
  G.predicate (ω.1 i) (ω.2.1 i)
    (ω.2.2.1 i) (ω.2.2.2 i)

end StrategyEventLaw

end

section

open scoped BigOperators

variable {ι : Type*}

end

section

open scoped BigOperators

end

section

open scoped BigOperators ComplexOrder MatrixOrder

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology

/--
@isnad1 id=integrab.1h1v.s6.ece481bf128c from=translated src=- shape=fd09ba71 vocab=63c20184
-/
theorem scalar_resolvent_purification_integrable_of_pos
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun s : ℝ => (z / (z + s)) ^ 2) (Ioi 0) := by
  have hpower :
      IntegrableOn (fun s : ℝ => (s + z) ^ (-2 : ℝ)) (Ioi 0) := by
    exact integrableOn_add_rpow_Ioi_of_lt
      (a := (-2 : ℝ)) (c := (0 : ℝ)) (m := z)
      (by norm_num) (by linarith)
  have hscaled :
      IntegrableOn (fun s : ℝ => z ^ 2 * (s + z) ^ (-2 : ℝ))
        (Ioi 0) :=
    hpower.const_mul (z ^ 2)
  refine hscaled.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hspos : 0 < s + z := by
    have : 0 < s := hs
    linarith
  change z ^ 2 * (s + z) ^ (-2 : ℝ) = (z / (z + s)) ^ 2
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg hspos.le, Real.rpow_two]
  rw [div_pow]
  simp only [add_comm, div_eq_mul_inv]

/--
@isnad1 id=integrab.1h1v.s6.0e3d18934f5b from=translated src=- shape=fd09ba71 vocab=2aeea046
-/
theorem scalar_resolvent_purification_integrable
    {z : ℝ} (hz : 0 ≤ z) :
    IntegrableOn (fun s : ℝ => (z / (z + s)) ^ 2) (Ioi 0) := by
  rcases hz.eq_or_lt with rfl | hzpos
  · simp only [zero_add, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      enorm_zero, ENNReal.zero_ne_top, integrableOn_const_iff, Real.volume_Ioi, lt_self_iff_false,
      or_false]
  · exact scalar_resolvent_purification_integrable_of_pos hzpos

/--
@isnad1 id=eq.1h1v.s6.a57988f5bf97 from=translated src=- shape=91ffb982 vocab=3748f528
-/
theorem scalar_resolvent_purification_integral
    {z : ℝ} (hz : 0 ≤ z) :
    (∫ s in Ioi (0 : ℝ), (z / (z + s)) ^ 2) = z := by
  rcases hz.eq_or_lt with rfl | hzpos
  · simp only [zero_add, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero]
  · have hderiv :
        ∀ x ∈ Ici (0 : ℝ),
          HasDerivAt (fun t : ℝ => -(z ^ 2) / (z + t))
            ((z / (z + x)) ^ 2) x := by
      intro x hx
      have hden : z + x ≠ 0 := by
        have hx_nonneg : 0 ≤ x := hx
        exact ne_of_gt (by linarith)
      have hd := ((hasDerivAt_const x (-(z ^ 2))).div
        ((hasDerivAt_const x z).add (hasDerivAt_id x)) hden)
      have hfun :
          (fun t : ℝ => -(z ^ 2) / (z + t)) =
            (fun _t : ℝ => -(z ^ 2)) /
              ((fun _t : ℝ => z) + id) := by
        funext t
        rfl
      rw [hfun]
      simpa only [div_pow, Pi.add_apply, id_eq, zero_mul, zero_add, mul_one,
        sub_neg_eq_add] using hd
    have hlimit :
        Tendsto (fun t : ℝ => -(z ^ 2) / (z + t))
          atTop (𝓝 (0 : ℝ)) := by
      have hden : Tendsto (fun t : ℝ => t + z) atTop atTop :=
        tendsto_atTop_add_const_right atTop z tendsto_id
      have hzero : Tendsto (fun t : ℝ => -(z ^ 2) / (t + z))
          atTop (𝓝 (0 : ℝ)) :=
        tendsto_const_nhds.div_atTop hden
      simpa only [add_comm] using hzero
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto'
      hderiv (scalar_resolvent_purification_integrable_of_pos hzpos) hlimit
    calc
      (∫ s in Ioi (0 : ℝ), (z / (z + s)) ^ 2) =
          (0 : ℝ) - (-(z ^ 2) / (z + 0)) := hftc
      _ = z := by
        field_simp
        ring

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private def diagonalPurificationGram
    {d : Type*} [DecidableEq d]
    (eigenvalue : d → ℝ) (s : ℝ) : Matrix d d ℂ :=
  Matrix.diagonal fun i =>
    (((eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)

private theorem diagonalPurificationGram_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ)
    (h_nonneg : ∀ i, 0 ≤ eigenvalue i) :
    IntegrableOn (diagonalPurificationGram eigenvalue) (Ioi 0) := by
  apply MeasureTheory.Integrable.of_eval
  intro i
  apply MeasureTheory.Integrable.of_eval
  intro j
  classical
  by_cases h : i = j
  · subst j
    have hcomplex :
        Integrable
          (fun s : ℝ =>
            (((eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ))
          (volume.restrict (Ioi 0)) :=
      MeasureTheory.Integrable.ofReal (𝕜 := ℂ)
        (scalar_resolvent_purification_integrable (h_nonneg i))
    simpa only [diagonalPurificationGram, Matrix.diagonal_apply_eq] using
      hcomplex
  · simp only [diagonalPurificationGram, Complex.ofReal_pow, Complex.ofReal_div,
      Complex.ofReal_add, ne_eq, h, not_false_eq_true, Matrix.diagonal_apply_ne,
      integrable_fun_zero]

private theorem integral_diagonalPurificationGram
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ)
    (h_nonneg : ∀ i, 0 ≤ eigenvalue i) :
    (∫ s in Ioi (0 : ℝ), diagonalPurificationGram eigenvalue s) =
      Matrix.diagonal (fun i => (eigenvalue i : ℂ)) := by
  classical
  have hmatrix := diagonalPurificationGram_integrable eigenvalue h_nonneg
  have hrows :
      ∀ i : d,
        Integrable
          (fun s : ℝ => diagonalPurificationGram eigenvalue s i)
          (volume.restrict (Ioi 0)) :=
    fun i => hmatrix.eval i
  have hentry (i : d) :
      ∀ j : d,
        Integrable
          (fun s : ℝ => diagonalPurificationGram eigenvalue s i j)
          (volume.restrict (Ioi 0)) :=
    fun j => (hrows i).eval j
  ext i j
  rw [show
    (∫ s in Ioi (0 : ℝ), diagonalPurificationGram eigenvalue s) i j =
      (∫ s in Ioi (0 : ℝ), diagonalPurificationGram eigenvalue s i) j from
        congrArg (fun row : d → ℂ => row j)
          (MeasureTheory.eval_integral hrows i)]
  rw [show
    (∫ s in Ioi (0 : ℝ), diagonalPurificationGram eigenvalue s i) j =
      ∫ s in Ioi (0 : ℝ), diagonalPurificationGram eigenvalue s i j from
        MeasureTheory.eval_integral (hentry i) j]
  by_cases h : i = j
  · subst j
    simp only [diagonalPurificationGram, Matrix.diagonal_apply_eq]
    calc
      (∫ s in Ioi (0 : ℝ),
        (((eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)) =
          ((∫ s in Ioi (0 : ℝ),
            (eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ) :=
        integral_ofReal
      _ = (eigenvalue i : ℂ) := by
        rw [scalar_resolvent_purification_integral (h_nonneg i)]
  · simp only [diagonalPurificationGram, Complex.ofReal_pow, Complex.ofReal_div,
      Complex.ofReal_add, ne_eq, h, not_false_eq_true, Matrix.diagonal_apply_ne, integral_zero]

/-- The continuous linear map implementing spectral conjugation. -/
def spectralConjugationCLM
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) :
    Matrix d d ℂ →L[ℝ] Matrix d d ℂ :=
  LinearMap.toContinuousLinearMap
    (Unitary.conjStarAlgAut ℝ (Matrix d d ℂ) U).toAlgEquiv.toLinearEquiv.toLinearMap

/--
@isnad1 id=eq.0h3v.s9.6ea5e8058a35 from=translated src=- shape=23b0bde2 vocab=87cb93c2
-/
@[simp] theorem spectralConjugationCLM_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (A : Matrix d d ℂ) :
    spectralConjugationCLM U A =
      (U : Matrix d d ℂ) * A * star (U : Matrix d d ℂ) := by
  rfl

private def spectralPurificationGram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) :
    Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (diagonalPurificationGram hF.isHermitian.eigenvalues s)

private theorem spectralPurificationGram_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    IntegrableOn (spectralPurificationGram F hF) (Ioi 0) := by
  have hdiag := diagonalPurificationGram_integrable
    hF.isHermitian.eigenvalues (fun i => hF.eigenvalues_nonneg i)
  exact (spectralConjugationCLM hF.isHermitian.eigenvectorUnitary).integrable_comp
    hdiag

private theorem integral_spectralPurificationGram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (∫ s in Ioi (0 : ℝ), spectralPurificationGram F hF s) = F := by
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  have hdiag := diagonalPurificationGram_integrable
    eigenvalue (fun i => hF.eigenvalues_nonneg i)
  calc
    (∫ s in Ioi (0 : ℝ), spectralPurificationGram F hF s) =
        spectralConjugationCLM U
          (∫ s in Ioi (0 : ℝ), diagonalPurificationGram eigenvalue s) := by
            exact ContinuousLinearMap.integral_comp_comm
              (spectralConjugationCLM U) hdiag
    _ = spectralConjugationCLM U
          (Matrix.diagonal (fun i => (eigenvalue i : ℂ))) := by
            rw [integral_diagonalPurificationGram eigenvalue
              (fun i => hF.eigenvalues_nonneg i)]
    _ = F := by
          simpa only [spectralConjugationCLM_apply, Complex.coe_algebraMap, Function.comp_def,
            Unitary.conjStarAlgAut_apply, U, eigenvalue] using
            hF.isHermitian.spectral_theorem.symm

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Kronecker Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The spectral filter for spectral purification. -/
def spectralPurificationFilter
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) : Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (Matrix.diagonal fun i =>
      ((hF.isHermitian.eigenvalues i /
        (hF.isHermitian.eigenvalues i + s) : ℝ) : ℂ))

private theorem spectralPurificationFilter_gram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) :
    star (spectralPurificationFilter F hF s) *
        spectralPurificationFilter F hF s =
      spectralPurificationGram F hF s := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  let D : Matrix d d ℂ := Matrix.diagonal fun i =>
    ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) U
  have hDhermitian : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ) = _
    simp only [Complex.ofReal_div, Complex.ofReal_add, star_div₀, RCLike.star_def,
      Complex.conj_ofReal, star_add]
  have hDstar : star D = D := by
    simpa only [Matrix.star_eq_conjTranspose] using hDhermitian.eq
  have hDsquare : D * D = diagonalPurificationGram eigenvalue s := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst j
      simp only [Complex.ofReal_div, Complex.ofReal_add, Matrix.diagonal_apply_eq,
        diagonalPurificationGram, pow_two, Complex.ofReal_mul]
    · simp only [Complex.ofReal_div, Complex.ofReal_add, ne_eq, h, not_false_eq_true,
        Matrix.diagonal_apply_ne, diagonalPurificationGram, Complex.ofReal_pow]
  change star (e D) * e D = e (diagonalPurificationGram eigenvalue s)
  calc
    star (e D) * e D = e (star D) * e D := by rw [map_star]
    _ = e (star D * D) := (map_mul e (star D) D).symm
    _ = e (diagonalPurificationGram eigenvalue s) := by
      rw [hDstar, hDsquare]

/--
@isnad1 id=eq.1h2v.s7.6038a54e4318 from=translated src=- shape=2fb803af vocab=e615d543
-/
theorem integral_spectralPurificationFilter_gram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (∫ s in Ioi (0 : ℝ),
      star (spectralPurificationFilter F hF s) *
        spectralPurificationFilter F hF s) = F := by
  simp_rw [spectralPurificationFilter_gram]
  exact integral_spectralPurificationGram F hF

/--
@isnad1 id=integrab.1h2v.s7.3adfd0fb92a6 from=translated src=- shape=542ddd93 vocab=ba153a8d
-/
theorem spectralPurificationFilter_gram_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    IntegrableOn
      (fun s : ℝ => star (spectralPurificationFilter F hF s) *
        spectralPurificationFilter F hF s) (Ioi 0) := by
  simpa only [spectralPurificationFilter_gram] using
    spectralPurificationGram_integrable F hF

/-- The born trace pairing construction used in the quantum parallel-repetition argument. -/
def bornTracePairing
    {dA dB : Type*} [Fintype dA] [Fintype dB]
    (ρ : Matrix (dA × dB) (dA × dB) ℂ) :
    Matrix dA dA ℂ →ₗ[ℝ] Matrix dB dB ℂ →ₗ[ℝ] ℝ where
  toFun F :=
    { toFun := fun G => (Matrix.trace (ρ * (F ⊗ₖ G))).re
      map_add' := by
        intro G H
        simp only [Matrix.kronecker_add, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
      map_smul' := by
        intro r G
        simp only [Matrix.kronecker_smul, mul_smul_comm, Matrix.trace_smul, Complex.real_smul,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Real.ringHom_apply, smul_eq_mul] }
  map_add' := by
    intro F H
    ext G
    simp only [Matrix.add_kronecker, Matrix.mul_add, Matrix.trace_add, Complex.add_re,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  map_smul' := by
    intro r F
    ext G
    simp only [Matrix.smul_kronecker, mul_smul_comm, Matrix.trace_smul, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, LinearMap.coe_mk,
      AddHom.coe_mk, Real.ringHom_apply, LinearMap.smul_apply, smul_eq_mul]

end

section

open scoped BigOperators Kronecker

namespace Game

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The conditional y given x construction used in the quantum parallel-repetition argument. -/
def conditionalYGivenX (G : Game X Y A B) (x : X) (y : Y) : ℝ :=
  G.questionWeight x y / G.marginalX x

/-- The conditional x given y construction used in the quantum parallel-repetition argument. -/
def conditionalXGivenY (G : Game X Y A B) (y : Y) (x : X) : ℝ :=
  G.questionWeight x y / G.marginalY y

/--
@isnad1 id=le.0h7v.s5.e00c682e7bff from=translated src=- shape=71367199 vocab=6adbae34
-/
theorem conditionalYGivenX_nonneg
    (G : Game X Y A B) (x : X) (y : Y) :
    0 ≤ G.conditionalYGivenX x y := by
  exact div_nonneg (G.weight_nonneg x y)
    (G.marginalX_nonneg x)

/--
@isnad1 id=le.0h7v.s5.fbb030e4bb93 from=translated src=- shape=9ae037ac vocab=8baaa9a8
-/
theorem conditionalXGivenY_nonneg
    (G : Game X Y A B) (y : Y) (x : X) :
    0 ≤ G.conditionalXGivenY y x := by
  exact div_nonneg (G.weight_nonneg x y)
    (G.marginalY_nonneg y)

end Game

section MixedHistories

variable {X Y A B U V : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup V] [Module ℝ V]

/-- The finite average of conditional bob. -/
def conditionalBobAverage
    (G : Game X Y A B) (K : Y → V) (x : X) : V :=
  ∑ y : Y, G.conditionalYGivenX x y • K y

/-- The finite average of conditional alice. -/
def conditionalAliceAverage
    (G : Game X Y A B) (H : X → U) (y : Y) : U :=
  ∑ x : X, G.conditionalXGivenY y x • H x

end MixedHistories

section RepeatedQuantumFilters

open scoped ComplexOrder MatrixOrder

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The measurement effect for conditioned alice. -/
def conditionedAliceEffect
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {i : Fin n // i ∈ D} → A)
    (xs : Fin n → X) :
    Matrix S.Alice S.Alice ℂ := by
  classical
  exact
    ∑ answers : Fin n → A,
      if ∀ (i : Fin n) (hi : i ∈ D),
        answers i = α ⟨i, hi⟩
      then (S.aliceMeasurement xs).effect answers
      else 0

/-- The measurement effect for conditioned bob. -/
def conditionedBobEffect
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {i : Fin n // i ∈ D} → B)
    (ys : Fin n → Y) :
    Matrix S.Bob S.Bob ℂ := by
  classical
  exact
    ∑ answers : Fin n → B,
      if ∀ (i : Fin n) (hi : i ∈ D),
        answers i = β ⟨i, hi⟩
      then (S.bobMeasurement ys).effect answers
      else 0

/--
@isnad1 id=possemid.0h10v.s8.80fa037f126c from=translated src=- shape=a69f8ba6 vocab=0eda5753
-/
theorem conditionedAliceEffect_positive
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {i : Fin n // i ∈ D} → A)
    (xs : Fin n → X) :
    (conditionedAliceEffect G n S D α xs).PosSemidef := by
  classical
  unfold conditionedAliceEffect
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact (S.aliceMeasurement xs).positive answers
  · exact Matrix.PosSemidef.zero

/--
@isnad1 id=possemid.0h10v.s8.5be3b7678790 from=translated src=- shape=aa4ebc38 vocab=c1eab505
-/
theorem conditionedBobEffect_positive
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {i : Fin n // i ∈ D} → B)
    (ys : Fin n → Y) :
    (conditionedBobEffect G n S D β ys).PosSemidef := by
  classical
  unfold conditionedBobEffect
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact (S.bobMeasurement ys).positive answers
  · exact Matrix.PosSemidef.zero

end RepeatedQuantumFilters

end

section

open scoped BigOperators ComplexOrder MatrixOrder

/--
The spectral support functional construction used in the quantum parallel-repetition argument.
-/
def spectralSupportFunctional
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (f : ℝ → ℝ) : Matrix d d ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary)
      (Matrix.diagonal fun i => (f (hF.isHermitian.eigenvalues i) : ℂ))

/--
@isnad1 id=eq.1h4v.s6.f4757fd3cc95 from=translated src=- shape=0db68c27 vocab=a88b3fd1
-/
theorem spectralSupportFunctional_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (f g : ℝ → ℝ) :
    spectralSupportFunctional F hF f *
        spectralSupportFunctional F hF g =
      spectralSupportFunctional F hF (fun x => f x * g x) := by
  classical
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary
  change e _ * e _ = e _
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  push_cast
  rfl

/--
@isnad1 id=eq.1h2v.s5.6d51bedf9439 from=translated src=- shape=42961da1 vocab=ba802103
-/
theorem spectralSupportFunctional_id
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportFunctional F hF (fun x => x) = F := by
  simpa only [spectralSupportFunctional, Unitary.conjStarAlgAut_apply, Complex.coe_algebraMap,
    Function.comp_def] using
    hF.isHermitian.spectral_theorem.symm

/--
@isnad1 id=eq.2h4v.s6.4f0597d2f7eb from=translated src=- shape=b6c17202 vocab=392f79f9
-/
theorem spectralSupportFunctional_congr
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {f g : ℝ → ℝ}
    (h : ∀ i : d,
      f (hF.isHermitian.eigenvalues i) =
        g (hF.isHermitian.eigenvalues i)) :
    spectralSupportFunctional F hF f =
      spectralSupportFunctional F hF g := by
  unfold spectralSupportFunctional
  congr 2
  funext i
  exact_mod_cast h i

/--
@isnad1 id=ishermit.1h3v.s5.5a0146ebf1de from=translated src=- shape=a9da451d vocab=71bff156
-/
theorem spectralSupportFunctional_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (f : ℝ → ℝ) :
    (spectralSupportFunctional F hF f).IsHermitian := by
  classical
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary
  let D : Matrix d d ℂ :=
    Matrix.diagonal fun i => (f (hF.isHermitian.eigenvalues i) : ℂ)
  have hD : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star (f (hF.isHermitian.eigenvalues i) : ℂ) = _
    simp only [RCLike.star_def, Complex.conj_ofReal]
  have hDstar : star D = D := by
    simpa only [Matrix.star_eq_conjTranspose] using hD.eq
  change Matrix.conjTranspose (e D) = e D
  simpa only [Matrix.star_eq_conjTranspose] using
    (show star (e D) = e D by rw [← map_star, hDstar])

/-- Apply reciprocal eigenvalues to a positive matrix, with zero on its kernel. -/
def spectralSupportInverse
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) : Matrix d d ℂ :=
  spectralSupportFunctional F hF (fun x => x⁻¹)

private def spectralSupportProjection
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) : Matrix d d ℂ :=
  spectralSupportFunctional F hF (fun x => if x = 0 then 0 else 1)

/-- The positive square-root construction for spectral support. -/
def spectralSupportSqrt
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) : Matrix d d ℂ :=
  spectralSupportFunctional F hF Real.sqrt

private theorem spectralSupportInverse_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (spectralSupportInverse F hF).IsHermitian :=
  spectralSupportFunctional_isHermitian F hF _

private theorem spectralSupportInverse_penrose
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportInverse F hF * F *
        spectralSupportInverse F hF =
      spectralSupportInverse F hF := by
  change spectralSupportFunctional F hF (fun x => x⁻¹) * F *
      spectralSupportFunctional F hF (fun x => x⁻¹) =
    spectralSupportFunctional F hF (fun x => x⁻¹)
  calc
    spectralSupportFunctional F hF (fun x => x⁻¹) * F *
        spectralSupportFunctional F hF (fun x => x⁻¹) =
      (spectralSupportFunctional F hF (fun x => x⁻¹) *
        spectralSupportFunctional F hF (fun x => x)) *
          spectralSupportFunctional F hF (fun x => x⁻¹) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF
          (fun x => (x⁻¹ * x) * x⁻¹) := by
      rw [spectralSupportFunctional_mul,
        spectralSupportFunctional_mul]
    _ = _ := spectralSupportFunctional_congr F hF (by
      intro i
      by_cases hi : hF.isHermitian.eigenvalues i = 0
      · simp only [hi, inv_zero, mul_zero]
      · simp only [ne_eq, hi, not_false_eq_true, inv_mul_cancel₀, one_mul])

/--
@isnad1 id=eq.1h2v.s5.01af7a3bbb0c from=translated src=- shape=1ef1334b vocab=8e712272
-/
theorem spectralSupportSqrt_sq
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportSqrt F hF * spectralSupportSqrt F hF = F := by
  change spectralSupportFunctional F hF Real.sqrt *
    spectralSupportFunctional F hF Real.sqrt = F
  calc
    spectralSupportFunctional F hF Real.sqrt *
        spectralSupportFunctional F hF Real.sqrt =
      spectralSupportFunctional F hF
        (fun x => Real.sqrt x * Real.sqrt x) :=
      spectralSupportFunctional_mul F hF _ _
    _ = spectralSupportFunctional F hF (fun x => x) :=
      spectralSupportFunctional_congr F hF (by
        intro i
        exact Real.mul_self_sqrt (hF.eigenvalues_nonneg i))
    _ = F := spectralSupportFunctional_id F hF

end

section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

end

section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- The matrix `Γ F⁻¹ Γᴴ` formed using the inverse on the support of `F`. -/
def purificationRangeProjection
    {d e : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ) : Matrix e e ℂ :=
  Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ

private theorem purificationRangeProjection_isHermitian
    {d e : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ) :
    (purificationRangeProjection F hF Γ).IsHermitian := by
  unfold purificationRangeProjection
  change Matrix.conjTranspose
    (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) = _
  simp only [Matrix.mul_assoc, conjTranspose_mul, conjTranspose_conjTranspose,
    (spectralSupportInverse_isHermitian F hF).eq]

private theorem purificationRangeProjection_idempotent
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    purificationRangeProjection F hF Γ *
        purificationRangeProjection F hF Γ =
      purificationRangeProjection F hF Γ := by
  unfold purificationRangeProjection
  calc
    (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) *
        (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) =
      Γ * (spectralSupportInverse F hF *
        (Matrix.conjTranspose Γ * Γ) *
          spectralSupportInverse F hF) * Matrix.conjTranspose Γ := by
            simp only [Matrix.mul_assoc]
    _ = Γ * (spectralSupportInverse F hF * F *
          spectralSupportInverse F hF) * Matrix.conjTranspose Γ := by
            rw [hΓ]
    _ = Γ * spectralSupportInverse F hF *
          Matrix.conjTranspose Γ := by
            rw [spectralSupportInverse_penrose]

private theorem purificationRangeProjection_complement_posSemidef
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    (1 - purificationRangeProjection F hF Γ).PosSemidef := by
  let P := purificationRangeProjection F hF Γ
  have hPstar : Matrix.conjTranspose P = P :=
    (purificationRangeProjection_isHermitian F hF Γ).eq
  have hPsq : P * P = P :=
    purificationRangeProjection_idempotent F hF Γ hΓ
  have hsquare :
      Matrix.conjTranspose (1 - P) * (1 - P) = 1 - P := by
    calc
      Matrix.conjTranspose (1 - P) * (1 - P) =
          (1 - P) * (1 - P) := by
            simp only [conjTranspose_sub, conjTranspose_one, hPstar]
      _ = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPsq]; noncomm_ring
  have hpositive := Matrix.posSemidef_conjTranspose_mul_self
    (1 - P)
  rw [hsquare] at hpositive
  exact hpositive

/-- Transport an effect through the purification map and the support inverse. -/
def purifiedRefinementCore
    {ι d e : Type*}
    [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ) (a : ι) : Matrix e e ℂ :=
  Γ * spectralSupportInverse F hF * effect a *
    spectralSupportInverse F hF * Matrix.conjTranspose Γ

private theorem purifiedRefinementCore_posSemidef
    {ι d e : Type*}
    [Fintype d] [DecidableEq d]
    [Finite e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (a : ι) :
    (purifiedRefinementCore F hF Γ effect a).PosSemidef := by
  let _ := Fintype.ofFinite e
  have h := (hpositive a).mul_mul_conjTranspose_same
    (Γ * spectralSupportInverse F hF)
  simpa only [purifiedRefinementCore, Matrix.mul_assoc, conjTranspose_mul,
    (spectralSupportInverse_isHermitian F hF).eq] using h

private theorem purifiedRefinementCore_sum
    {ι d e : Type*} [Fintype ι]
    [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (hsum : (∑ a : ι, effect a) = F) :
    (∑ a : ι, purifiedRefinementCore F hF Γ effect a) =
      purificationRangeProjection F hF Γ := by
  unfold purifiedRefinementCore purificationRangeProjection
  calc
    (∑ a : ι,
      Γ * spectralSupportInverse F hF * effect a *
        spectralSupportInverse F hF * Matrix.conjTranspose Γ) =
      Γ * spectralSupportInverse F hF *
        (∑ a : ι, effect a) * spectralSupportInverse F hF *
          Matrix.conjTranspose Γ := by
            simp only [Matrix.mul_sum, Matrix.sum_mul]
    _ = Γ * spectralSupportInverse F hF * F *
          spectralSupportInverse F hF * Matrix.conjTranspose Γ := by
            rw [hsum]
    _ = Γ * (spectralSupportInverse F hF * F *
          spectralSupportInverse F hF) * Matrix.conjTranspose Γ := by
            simp only [Matrix.mul_assoc]
    _ = Γ * spectralSupportInverse F hF *
          Matrix.conjTranspose Γ := by
            rw [spectralSupportInverse_penrose]

/-- Complete the transported effects by assigning the unused range to outcome `a₀`. -/
def purifiedRefinedEffect
    {ι d e : Type*} [DecidableEq ι]
    [Fintype d] [DecidableEq d]
     [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (a₀ a : ι) : Matrix e e ℂ :=
  purifiedRefinementCore F hF Γ effect a +
    if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0

/--
@isnad1 id=possemid.3h8v.s7.b7002356b915 from=translated src=- shape=f6c02b54 vocab=81514e6a
-/
theorem purifiedRefinedEffect_posSemidef
    {ι d e : Type*} [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (a₀ a : ι) :
    (purifiedRefinedEffect F hF Γ effect a₀ a).PosSemidef := by
  change (purifiedRefinementCore F hF Γ effect a +
    if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0).PosSemidef
  refine (purifiedRefinementCore_posSemidef F hF Γ effect
    hpositive a).add ?_
  split
  · exact purificationRangeProjection_complement_posSemidef F hF Γ hΓ
  · exact Matrix.PosSemidef.zero

/--
@isnad1 id=eq.2h7v.s6.f8fa7d16d3ab from=translated src=- shape=8ce3ab3d vocab=a151e4f9
-/
theorem purifiedRefinedEffect_complete
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
     [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ : ι) :
    (∑ a : ι, purifiedRefinedEffect F hF Γ effect a₀ a) = 1 := by
  classical
  unfold purifiedRefinedEffect
  rw [Finset.sum_add_distrib]
  rw [purifiedRefinementCore_sum F hF Γ effect hsum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, add_sub_cancel]

/-- The positive operator-valued measurement implementing purified refined. -/
def purifiedRefinedPOVM
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ : ι) : POVM ι e where
  effect := purifiedRefinedEffect F hF Γ effect a₀
  positive a := purifiedRefinedEffect_posSemidef F hF Γ hΓ
    effect hpositive a₀ a
  complete := purifiedRefinedEffect_complete F hF Γ effect hsum a₀

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The set of coordinates remaining after full history. -/
def fullHistoryRemaining (n : ℕ)
    (D L : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ \ D) \ L

/-- A partial transcript split into conditioned, revealed, and remaining coordinates. -/
@[ext (iff := false)] structure FullSubsetHistory
    (X Y : Type*)
    (n : ℕ) (D L : Finset (Fin n)) where
  /-- Alice's questions on conditioned coordinates. -/
  aliceConditioned : {i : Fin n // i ∈ D} → X
  /-- Bob's questions on conditioned coordinates. -/
  bobConditioned : {i : Fin n // i ∈ D} → Y
  /-- Alice's questions on revealed coordinates. -/
  aliceRevealed : {i : Fin n // i ∈ L} → X
  /-- Bob's questions on the remaining coordinates. -/
  bobRemaining : {i : Fin n // i ∈ fullHistoryRemaining n D L} → Y
  deriving Fintype

/--
The full history alice question construction used in the quantum parallel-repetition argument.
-/
def fullHistoryAliceQuestion
    {X Y : Type*}
    {n : ℕ} {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X) :
    Fin n → X := fun i =>
  if hiD : i ∈ D then h.aliceConditioned ⟨i, hiD⟩
  else if hiL : i ∈ L then h.aliceRevealed ⟨i, hiL⟩
  else hidden ⟨i, by
    simp only [fullHistoryRemaining, Finset.mem_sdiff, Finset.mem_univ, hiD, not_false_eq_true,
      and_self, hiL]⟩

/-- The full history bob question construction used in the quantum parallel-repetition argument. -/
def fullHistoryBobQuestion
    {X Y : Type*}
    {n : ℕ} {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ L} → Y) :
    Fin n → Y := fun i =>
  if hiD : i ∈ D then h.bobConditioned ⟨i, hiD⟩
  else if hiL : i ∈ L then hidden ⟨i, hiL⟩
  else h.bobRemaining ⟨i, by
    simp only [fullHistoryRemaining, Finset.mem_sdiff, Finset.mem_univ, hiD, not_false_eq_true,
      and_self, hiL]⟩

private def fullHistoryQuestionEquiv
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D) :
    (FullSubsetHistory X Y n D L ×
      ({i : Fin n // i ∈ fullHistoryRemaining n D L} → X) ×
      ({i : Fin n // i ∈ L} → Y)) ≃
      ((Fin n → X) × (Fin n → Y)) where
  toFun t :=
    (fullHistoryAliceQuestion t.1 t.2.1,
      fullHistoryBobQuestion t.1 t.2.2)
  invFun q :=
    (⟨fun i => q.1 i,
      fun i => q.2 i,
      fun i => q.1 i,
      fun i => q.2 i⟩,
      (fun i => q.1 i),
      (fun i => q.2 i))
  left_inv := by
    rintro ⟨h, hx, hy⟩
    apply Prod.ext
    · apply FullSubsetHistory.ext
      · funext i
        simp only [fullHistoryAliceQuestion, i.property, ↓reduceDIte, Subtype.coe_eta]
      · funext i
        simp only [fullHistoryBobQuestion, i.property, ↓reduceDIte, Subtype.coe_eta]
      · funext i
        have hiD : (i : Fin n) ∉ D :=
          (Finset.mem_sdiff.mp (hL i.property)).2
        simp only [fullHistoryAliceQuestion, hiD, ↓reduceDIte, i.property, Subtype.coe_eta]
      · funext i
        have hiD : (i : Fin n) ∉ D := by
          have := i.property
          simpa only [fullHistoryRemaining] using
            (Finset.mem_sdiff.mp
              (Finset.mem_sdiff.mp i.property).1).2
        have hiL : (i : Fin n) ∉ L :=
          (Finset.mem_sdiff.mp i.property).2
        simp only [fullHistoryBobQuestion, hiD, ↓reduceDIte, hiL]
    · apply Prod.ext
      · funext i
        have hiD : (i : Fin n) ∉ D :=
          (Finset.mem_sdiff.mp
            (Finset.mem_sdiff.mp i.property).1).2
        have hiL : (i : Fin n) ∉ L :=
          (Finset.mem_sdiff.mp i.property).2
        simp only [fullHistoryAliceQuestion, hiD, ↓reduceDIte, hiL]
      · funext i
        have hiD : (i : Fin n) ∉ D :=
          (Finset.mem_sdiff.mp (hL i.property)).2
        simp only [fullHistoryBobQuestion, hiD, ↓reduceDIte, i.property, Subtype.coe_eta]
  right_inv := by
    rintro ⟨xs, ys⟩
    apply Prod.ext
    · funext i
      by_cases hiD : i ∈ D
      · simp only [fullHistoryAliceQuestion, hiD, ↓reduceDIte]
      · by_cases hiL : i ∈ L <;>
          simp only [fullHistoryAliceQuestion, hiD, ↓reduceDIte, hiL]
    · funext i
      by_cases hiD : i ∈ D
      · simp only [fullHistoryBobQuestion, hiD, ↓reduceDIte]
      · by_cases hiL : i ∈ L <;>
          simp only [fullHistoryBobQuestion, hiD, ↓reduceDIte, hiL]

section ActualHistoryWeights

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The probability weight for full history. -/
def fullHistoryWeight
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L) : ℝ :=
  (∏ i : {i : Fin n // i ∈ D},
    G.questionWeight (h.aliceConditioned i) (h.bobConditioned i)) *
  (∏ i : {i : Fin n // i ∈ L},
    G.marginalX (h.aliceRevealed i)) *
  (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
    G.marginalY (h.bobRemaining i))

/-- The probability weight for full history hidden alice. -/
def fullHistoryHiddenAliceWeight
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X) : ℝ :=
  ∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
    G.conditionalXGivenY (h.bobRemaining i) (hidden i)

/-- The probability weight for full history hidden bob. -/
def fullHistoryHiddenBobWeight
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ L} → Y) : ℝ :=
  ∏ i : {i : Fin n // i ∈ L},
    G.conditionalYGivenX (h.aliceRevealed i) (hidden i)

/-- The spectral filter for full history alice. -/
def fullHistoryAliceFilter
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A) :
    Matrix S.Alice S.Alice ℂ :=
  ∑ hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X,
    fullHistoryHiddenAliceWeight G h hidden •
      conditionedAliceEffect G n S D α
        (fullHistoryAliceQuestion h hidden)

/-- The spectral filter for full history bob. -/
def fullHistoryBobFilter
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (β : {i : Fin n // i ∈ D} → B) :
    Matrix S.Bob S.Bob ℂ :=
  ∑ hidden : {i : Fin n // i ∈ L} → Y,
    fullHistoryHiddenBobWeight G h hidden •
      conditionedBobEffect G n S D β
        (fullHistoryBobQuestion h hidden)

/-- The indicator function for full history win. -/
def fullHistoryWinIndicator
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) : ℝ := by
  classical
  exact if ∀ i : {i : Fin n // i ∈ D},
    G.predicate (h.aliceConditioned i) (h.bobConditioned i)
      (α i) (β i) = true then 1 else 0

private def fullQuestionWinIndicator
    (G : Game X Y A B) {n : ℕ}
    (D : Finset (Fin n))
    (xs : Fin n → X) (ys : Fin n → Y)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) : ℝ := by
  classical
  exact if ∀ i : {i : Fin n // i ∈ D},
    G.predicate (xs i) (ys i) (α i) (β i) = true
    then 1 else 0

end ActualHistoryWeights

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private def matrixQuadraticCLM
    {d : Type*} [Fintype d]
    (x : d → ℂ) : Matrix d d ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => star x ⬝ᵥ A.mulVec x
      map_add' := by
        intro A B
        simp only [dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec, Matrix.add_apply,
          add_mul, Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro r A
        change
          (∑ i, star (x i) *
            ∑ j, ((r : ℂ) * A i j) * x j) =
          (r : ℂ) *
            (∑ i, star (x i) * ∑ j, A i j * x j)
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring }

private def matrixAdjointCLM
    {d : Type*} [Fintype d] :
    Matrix d d ℂ →L[ℝ] Matrix d d ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => star A
      map_add' := by
        intro A B
        exact star_add A B
      map_smul' := by
        intro r A
        simp }

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/--
@isnad1 id=memlp.1h1v.s6.5f2833173b23 from=translated src=- shape=af0a8e25 vocab=85c82fb7
-/
theorem scalarResolventFilter_memLp_two
    {z : ℝ} (hz : 0 ≤ z) :
    MemLp (fun s : ℝ => z / (z + s)) 2
      (volume.restrict (Ioi 0)) := by
  have hmeas :
      AEStronglyMeasurable (fun s : ℝ => z / (z + s))
        (volume.restrict (Ioi 0)) := by
    exact (measurable_const.div
      (measurable_const.add measurable_id)).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hmeas).mpr
    (scalar_resolvent_purification_integrable hz)

/--
@isnad1 id=memlp.1h2v.s6.0d5e64a84bb0 from=translated src=- shape=79ee4e34 vocab=e963b1b4
-/
theorem spectralPurificationFilter_memLp_two
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    MemLp (spectralPurificationFilter F hF) 2
      (volume.restrict (Ioi 0)) := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  apply MemLp.of_eval
  intro i
  apply MemLp.of_eval
  intro j
  have hform :
      (fun s : ℝ => spectralPurificationFilter F hF s i j) =
        (fun s : ℝ => ∑ k : d,
          (U : Matrix d d ℂ) i k *
            ((eigenvalue k / (eigenvalue k + s) : ℝ) : ℂ) *
            star (U : Matrix d d ℂ) k j) := by
    funext s
    change
      ((U : Matrix d d ℂ) *
        Matrix.diagonal (fun k =>
          ((eigenvalue k / (eigenvalue k + s) : ℝ) : ℂ)) *
        star (U : Matrix d d ℂ)) i j = _
    simp only [Matrix.diagonal, Complex.ofReal_div, Complex.ofReal_add, Matrix.mul_apply,
      Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Matrix.star_apply, RCLike.star_def]
  rw [hform]
  apply memLp_finsetSum Finset.univ
  intro k _
  exact ((scalarResolventFilter_memLp_two
    (hF.eigenvalues_nonneg k)).ofReal.const_mul
      ((U : Matrix d d ℂ) i k)).mul_const
        (star (U : Matrix d d ℂ) k j)

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private def spectralEntropyKernel
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) :
    Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (Matrix.diagonal fun i =>
      ((hF.isHermitian.eigenvalues i / (1 + s) -
        hF.isHermitian.eigenvalues i /
          (hF.isHermitian.eigenvalues i + s) : ℝ) : ℂ))

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/--
The weighted spectral filter variance construction used in the quantum parallel-repetition
argument.
-/
def weightedSpectralFilterVariance
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (s : ℝ) : Matrix d d ℂ :=
  ∑ i : ι, weight i •
    (star (spectralPurificationFilter (F i) (positive i) s -
        spectralPurificationFilter M hM s) *
      (spectralPurificationFilter (F i) (positive i) s -
        spectralPurificationFilter M hM s))

private def weightedSpectralEntropyJensen
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (s : ℝ) : Matrix d d ℂ :=
  (∑ i : ι, weight i • spectralEntropyKernel (F i) (positive i) s) -
    spectralEntropyKernel M hM s

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private def diagonalEntropyKernel
    {d : Type*} [DecidableEq d]
    (eigenvalue : d → ℝ) (s : ℝ) : Matrix d d ℂ :=
  Matrix.diagonal fun i =>
    ((eigenvalue i / (1 + s) -
      eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

section HistoryContractions

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The potential function controlling full history alice entropy. -/
def fullHistoryAliceEntropyPotential
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) : ℝ :=
  ∑ h : FullSubsetHistory X Y n D L,
    ∑ α : {i : Fin n // i ∈ D} → A,
    ∑ β : {i : Fin n // i ∈ D} → B,
      fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
        bornTracePairing S.state.matrix
          (cfc (fun z : ℝ => z * Real.log z)
            (fullHistoryAliceFilter G n S D L h α))
          (fullHistoryBobFilter G n S D L h β)

end HistoryContractions

/-- The finite atom representing positive matrix spectral. -/
def positiveMatrixSpectralAtom
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i : d) :
    Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (Matrix.diagonal (Pi.single i (1 : ℂ)))

/--
@isnad1 id=possemid.1h3v.s5.8f154fb98c65 from=translated src=- shape=3432c47d vocab=ecab4a9d
-/
theorem positiveMatrixSpectralAtom_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i : d) :
    (positiveMatrixSpectralAtom F hF i).PosSemidef := by
  classical
  have hdiag :
      (Matrix.diagonal (Pi.single i (1 : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro j
    by_cases hij : i = j
    · subst j
      simp only [Pi.zero_apply, Pi.single_eq_same, zero_le_one]
    · simp only [Pi.zero_apply, ne_eq, hij, not_false_eq_true, Pi.single_eq_of_ne', Std.le_refl]
  unfold positiveMatrixSpectralAtom
  rw [spectralConjugationCLM_apply]
  simpa only [star_eq_conjTranspose] using
    hdiag.mul_mul_conjTranspose_same
      (hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ)

/--
@isnad1 id=eq.1h2v.s6.a3c5beb78074 from=translated src=- shape=568b97d9 vocab=516cbe40
-/
theorem positiveMatrixSpectralAtom_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (∑ i : d, positiveMatrixSpectralAtom F hF i) = 1 := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  have hdiag :
      (∑ i : d, Matrix.diagonal (Pi.single i (1 : ℂ))) =
        (1 : Matrix d d ℂ) := by
    ext j k
    by_cases hjk : j = k
    · subst k
      simp only [Matrix.sum_apply, diagonal_apply_eq, Pi.single_apply, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte, one_apply_eq]
    · simp only [Matrix.sum_apply, ne_eq, hjk, not_false_eq_true, diagonal_apply_ne,
        Finset.sum_const_zero, one_apply_ne]
  change
    (∑ i : d,
      spectralConjugationCLM U
        (Matrix.diagonal (Pi.single i (1 : ℂ)))) = 1
  rw [← map_sum, hdiag]
  simp only [spectralConjugationCLM_apply, mul_one, SetLike.coe_mem, Unitary.mul_star_self_of_mem]

private def leftSpectralBornWeight
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ)
    (i : dA) : ℝ :=
  bornTracePairing ρ.matrix
    (positiveMatrixSpectralAtom F hF i) G

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The quantum state representing raw embezzlement. -/
def rawEmbezzlementState (n : ℕ) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  toLp 2 fun q : Fin n × Fin n =>
    if q.1 = q.2 then
      (↑((Real.sqrt ((q.1.val : ℝ) + 1))⁻¹) : ℂ)
    else
      0

/--
@isnad1 id=ne.1h1v.s6.29665a685a9d from=translated src=- shape=943be05a vocab=cf09c58e
-/
theorem rawEmbezzlementState_ne_zero
    (n : ℕ) (hn : 0 < n) :
    rawEmbezzlementState n ≠ 0 := by
  intro h
  let j : Fin n := ⟨0, hn⟩
  have hj := congrArg
    (fun z : EuclideanSpace ℂ (Fin n × Fin n) => z (j, j)) h
  simp only [rawEmbezzlementState, Complex.ofReal_inv, ↓reduceIte, CharP.cast_eq_zero, zero_add,
    Real.sqrt_one, Complex.ofReal_one, inv_one, PiLp.zero_apply, one_ne_zero, j] at hj

/-- The harmonic number construction used in the quantum parallel-repetition argument. -/
def harmonicNumber (n : ℕ) : ℝ :=
  ∑ j : Fin n, ((j.val : ℝ) + 1)⁻¹

/-- The quantum state representing embezzlement. -/
def embezzlementState (n : ℕ) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  (‖rawEmbezzlementState n‖⁻¹ : ℝ) •
    rawEmbezzlementState n

/--
@isnad1 id=eq.1h1v.s6.718f4227a557 from=translated src=- shape=33c2324f vocab=e4af7ad6
-/
theorem embezzlementState_norm
    (n : ℕ) (hn : 0 < n) :
    ‖embezzlementState n‖ = 1 := by
  have hraw : ‖rawEmbezzlementState n‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (rawEmbezzlementState_ne_zero n hn)
  rw [embezzlementState, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hraw]

/-- The type used to represent bipartite unit vector in the exact sampling construction. -/
abbrev BipartiteUnitVector (d : ℕ) :=
  {ξ : EuclideanSpace ℂ (Fin d × Fin d) // ‖ξ‖ = 1}

/-- The overlap quantity for spectral atom. -/
def spectralAtomOverlap
    {d : Type*} [Fintype d] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (i j : d) : ℝ :=
  (Matrix.trace
    (positiveMatrixSpectralAtom F hF i *
      positiveMatrixSpectralAtom G hG j)).re

/--
@isnad1 id=eq.1h4v.s6.fed9644e8213 from=translated src=- shape=5354e9fe vocab=9c7d43cc
-/
theorem spectralAtom_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (i j : d) :
    positiveMatrixSpectralAtom F hF i *
      positiveMatrixSpectralAtom F hF j =
        if i = j then positiveMatrixSpectralAtom F hF i else 0 := by
  classical
  let e := Unitary.conjStarAlgAut ℝ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary
  change
    e (Matrix.diagonal (Pi.single i (1 : ℂ))) *
      e (Matrix.diagonal (Pi.single j (1 : ℂ))) =
        if i = j then
          e (Matrix.diagonal (Pi.single i (1 : ℂ)))
        else
          0
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    rw [← map_mul, Matrix.diagonal_mul_diagonal]
    congr 1
    ext k l
    simp only [Matrix.diagonal_apply, Pi.single_apply]
    split_ifs <;> simp_all
  · simp only [hij, ite_false]
    rw [← map_mul, Matrix.diagonal_mul_diagonal, ← map_zero e]
    congr 1
    ext k l
    by_cases hik : k = i
    · subst k
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Matrix.diagonal_apply, hij,
        ↓reduceIte, ite_self, Matrix.zero_apply]
    · simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Matrix.diagonal_apply, hik,
        ↓reduceIte, ite_self, Matrix.zero_apply]

/--
@isnad1 id=eq.1h3v.s6.0c6f70664951 from=translated src=- shape=a98905b3 vocab=c294eba6
-/
theorem spectralAtomSum_mul_self
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (s : Finset d) :
    (∑ i ∈ s, positiveMatrixSpectralAtom F hF i) *
      (∑ i ∈ s, positiveMatrixSpectralAtom F hF i) =
        ∑ i ∈ s, positiveMatrixSpectralAtom F hF i := by
  classical
  calc
    (∑ i ∈ s, positiveMatrixSpectralAtom F hF i) *
        (∑ i ∈ s, positiveMatrixSpectralAtom F hF i) =
      ∑ i ∈ s, ∑ j ∈ s,
        positiveMatrixSpectralAtom F hF i *
          positiveMatrixSpectralAtom F hF j := by
            simp only [Matrix.sum_mul, Matrix.mul_sum]
            rw [Finset.sum_comm]
    _ = ∑ i ∈ s, positiveMatrixSpectralAtom F hF i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [spectralAtom_mul, Finset.sum_ite_eq, hi, ↓reduceIte]

/-- The finite outcome encoding for coherent binary joint. -/
def coherentBinaryJointOutcome
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM Bool d) (Q : POVM Bool e)
    (z : EuclideanSpace ℂ (d × e))
    (a b : Bool) : EuclideanSpace ℂ (d × e) :=
  toLp 2
    (((P.effect a ⊗ₖ Q.effect b)).mulVec (ofLp z))

/-- The state vector representing finite tensor. -/
def finiteTensorVector
    {ι d : Type*} [Fintype ι]
    (v : ι → EuclideanSpace ℂ d) :
    EuclideanSpace ℂ (ι → d) :=
  toLp 2 fun q : ι → d => ∏ i : ι, v i (q i)

/--
@isnad1 id=eq.2h2v.s5.3abb603cd05f from=translated src=- shape=680cac4f vocab=bf60399c
-/
theorem positiveDensity_eigenvalues_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (htrace : Matrix.trace F = 1) :
    (∑ i : d, hF.isHermitian.eigenvalues i) = 1 := by
  have hspectral := congrArg Complex.re
    hF.isHermitian.trace_eq_sum_eigenvalues
  simpa only [Complex.coe_algebraMap, Complex.re_sum, Complex.ofReal_re, htrace,
    Complex.one_re] using hspectral.symm

/-- The probability of binary born. -/
def binaryBornProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e)
    (a b : Bool) : ℝ :=
  (Matrix.trace
    (ρ.matrix * (P.effect a ⊗ₖ Q.effect b))).re

/-- The probability of binary continue. -/
def binaryContinueProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) : ℝ :=
  binaryBornProbability ρ P Q false false

/-- The probability of binary joint success. -/
def binaryJointSuccessProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) : ℝ :=
  binaryBornProbability ρ P Q true true

/-- The probability of binary mismatch. -/
def binaryMismatchProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) : ℝ :=
  binaryBornProbability ρ P Q true false +
    binaryBornProbability ρ P Q false true

/--
The shared threshold resource raw construction used in the quantum parallel-repetition argument.
-/
def sharedThresholdResourceRaw
    {κ d : Type*}
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) :
    EuclideanSpace ℂ ((Σ _ : κ, d) × (Σ _ : κ, d)) :=
  toLp 2 fun q : (Σ _ : κ, d) × (Σ _ : κ, d) =>
    if q.1.1 = q.2.1 ∧ q.1.2 = q.2.2 then
      (τ q.1.1 : ℂ)
    else
      0

/--
@isnad1 id=ne.1h5v.s7.c7d6c9f96005 from=translated src=- shape=3d261b93 vocab=d109ab46
-/
theorem sharedThresholdResourceRaw_ne_zero
    {κ d : Type*}
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) (k : κ) (i : d) (hk : τ k ≠ 0) :
    sharedThresholdResourceRaw (d := d) τ ≠ 0 := by
  intro hzero
  have hentry := congrArg
    (fun z : EuclideanSpace ℂ
        ((Σ _ : κ, d) × (Σ _ : κ, d)) =>
      z (⟨k, i⟩, ⟨k, i⟩)) hzero
  have hcast : (τ k : ℂ) = 0 := by
    simpa only [Complex.ofReal_eq_zero, sharedThresholdResourceRaw, and_self, ↓reduceIte,
      PiLp.zero_apply] using hentry
  exact hk (by exact_mod_cast hcast)

/-- The auxiliary resource for shared threshold. -/
def sharedThresholdResource
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) :
    EuclideanSpace ℂ ((Σ _ : κ, d) × (Σ _ : κ, d)) :=
  (‖sharedThresholdResourceRaw (d := d) τ‖⁻¹ : ℝ) •
    sharedThresholdResourceRaw (d := d) τ

/--
@isnad1 id=eq.1h5v.s7.103c6e29de45 from=translated src=- shape=5b30e986 vocab=7953662a
-/
theorem sharedThresholdResource_norm
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) (k : κ) (i : d) (hk : τ k ≠ 0) :
    ‖sharedThresholdResource (d := d) τ‖ = 1 := by
  have hnorm : ‖sharedThresholdResourceRaw (d := d) τ‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (sharedThresholdResourceRaw_ne_zero τ k i hk)
  rw [sharedThresholdResource, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ hnorm]

/-- The positive operator-valued measurement implementing transpose. -/
def transposePOVM
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (P : POVM ι d) : POVM ι d where
  effect b := (P.effect b).transpose
  positive b := (P.positive b).transpose
  complete := by
    classical
    ext i j
    have hc := congrArg
      (fun M : Matrix d d ℂ => M j i) P.complete
    simpa only [Matrix.sum_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm] using hc

/--
@isnad1 id=eq.0h3v.s7.9611d0cf38a2 from=translated src=- shape=bd604f6c vocab=2a0c88df
-/
theorem matrixVectorization_norm_sq
    {d e : Type*} [Fintype d] [Fintype e]
    (K : Matrix d e ℂ) :
    ‖toLp 2 (Matrix.vec K)‖ ^ 2 =
      (Matrix.trace (K.conjTranspose * K)).re := by
  calc
    ‖toLp 2 (Matrix.vec K)‖ ^ 2 =
        (inner ℂ (toLp 2 (Matrix.vec K))
          (toLp 2 (Matrix.vec K))).re :=
            norm_sq_eq_re_inner (𝕜 := ℂ)
              (toLp 2 (Matrix.vec K))
    _ = (star (Matrix.vec K) ⬝ᵥ Matrix.vec K).re := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        (Matrix.vec K ⬝ᵥ star (Matrix.vec K)).re =
          (star (Matrix.vec K) ⬝ᵥ Matrix.vec K).re
      rw [dotProduct_comm]
    _ = (Matrix.trace (K.conjTranspose * K)).re := by
      rw [Matrix.star_vec_dotProduct_vec]

private def weightedComplexOverlapVector
    {ι κ : Type*}
    (σ : ι → ℝ) (μ : κ → ℝ)
    (L : ι → κ → ℂ) : EuclideanSpace ℂ (ι × κ) :=
  toLp 2 fun q : ι × κ =>
    (Real.sqrt (σ q.1 * μ q.2) : ℂ) * L q.1 q.2

/-- The target object for tensor embezzlement. -/
def tensorEmbezzlementTarget
    {d n : ℕ} (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin (d * n) × Fin (d * n)) :=
  toLp 2 fun q : Fin (d * n) × Fin (d * n) =>
    let a : Fin d × Fin n := finProdFinEquiv.symm q.1
    let b : Fin d × Fin n := finProdFinEquiv.symm q.2
    ξ.val (a.1, b.1) * embezzlementState n (a.2, b.2)

/-- The operator action for local unitary. -/
def localUnitaryAction {n : ℕ}
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : EuclideanSpace ℂ (Fin n × Fin n)) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  toLp 2
    (((U : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
      (V : Matrix (Fin n) (Fin n) ℂ)).mulVec (ofLp ψ))

/--
@isnad1 id=mem.0h3v.s9.2372343ab3ff from=translated src=- shape=c4c0de1a vocab=09e071b3
-/
theorem localUnitaryAction_matrix_mem_unitary {n : ℕ}
    (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    ((U : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
      (V : Matrix (Fin n) (Fin n) ℂ)) ∈
        Matrix.unitaryGroup (Fin n × Fin n) ℂ := by
  exact Matrix.kronecker_mem_unitary U.property V.property

/--
@isnad1 id=eq.0h4v.s8.1e58157e4817 from=translated src=- shape=d02ff03d vocab=c4da35d6
-/
theorem localUnitaryAction_norm {n : ℕ}
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : EuclideanSpace ℂ (Fin n × Fin n)) :
    ‖localUnitaryAction U V ψ‖ = ‖ψ‖ := by
  let M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
    (U : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
      (V : Matrix (Fin n) (Fin n) ℂ)
  have hM : M ∈ Matrix.unitaryGroup (Fin n × Fin n) ℂ :=
    localUnitaryAction_matrix_mem_unitary U V
  have hclm : Matrix.toEuclideanCLM
      (n := Fin n × Fin n) (𝕜 := ℂ) M ∈
      unitary
        (EuclideanSpace ℂ (Fin n × Fin n) →L[ℂ]
          EuclideanSpace ℂ (Fin n × Fin n)) :=
    Unitary.map_mem
      (Matrix.toEuclideanCLM (n := Fin n × Fin n) (𝕜 := ℂ)) hM
  exact ContinuousLinearMap.norm_map_of_mem_unitary hclm ψ

/-- The overlap quantity for unitary basis. -/
def unitaryBasisOverlap
    {d : Type*} [Fintype d] [DecidableEq d]
    (U V : Matrix.unitaryGroup d ℂ) :
    Matrix.unitaryGroup d ℂ := U⁻¹ * V

/-- The quantum state representing diagonal schmidt. -/
def diagonalSchmidtState
    {d : Type*} [DecidableEq d]
    (σ : d → ℝ) : EuclideanSpace ℂ (d × d) :=
  toLp 2 fun q : d × d =>
    if q.1 = q.2 then (σ q.1 : ℂ) else 0

/--
@isnad1 id=eq.0h2v.s6.6f07fe7974f7 from=translated src=- shape=2b522462 vocab=26a4bcca
-/
theorem diagonalSchmidtState_norm_sq
    {d : Type*} [Fintype d] [DecidableEq d]
    (σ : d → ℝ) :
    ‖diagonalSchmidtState σ‖ ^ 2 =
      ∑ i : d, σ i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change
    (∑ j : d, ‖if i = j then (σ i : ℂ) else 0‖ ^ 2) =
      σ i ^ 2
  have hterm (j : d) :
      ‖if i = j then (σ i : ℂ) else 0‖ ^ 2 =
        if i = j then σ i ^ 2 else 0 := by
    split_ifs <;> simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The state vector representing schmidt. -/
def schmidtVector
    {d : ℕ}
    (σ : Fin d → ℝ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  localUnitaryAction U V
    (diagonalSchmidtState σ)

/--
@isnad1 id=eq.0h4v.s8.e278e8cdc0d9 from=translated src=- shape=449c9efe vocab=4836586a
-/
theorem schmidtVector_norm_sq
    {d : ℕ}
    (σ : Fin d → ℝ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖schmidtVector σ U V‖ ^ 2 =
      ∑ i : Fin d, σ i ^ 2 := by
  rw [schmidtVector,
    localUnitaryAction_norm,
    diagonalSchmidtState_norm_sq]

/--
@isnad1 id=eq.0h6v.s9.f4a53050d5f7 from=translated src=- shape=272e1032 vocab=852dbb6e
-/
theorem schmidtVector_apply
    {d : ℕ}
    (σ : Fin d → ℝ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (a b : Fin d) :
    schmidtVector σ U V (a, b) =
      ∑ i : Fin d, (σ i : ℂ) * U a i * V b i := by
  classical
  simp only [schmidtVector, localUnitaryAction, diagonalSchmidtState, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, mul_comm, ite_mul, zero_mul, Fintype.sum_prod_type,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_assoc]

/--
@isnad1 id=eq.0h4v.s10.6a3a040dc107 from=translated src=- shape=a8512a3a vocab=418e65ae
-/
theorem matrixVectorization_inner
    {d e : Type*} [Fintype d] [Fintype e]
    (X Y : Matrix d e ℂ) :
    inner ℂ (toLp 2 (Matrix.vec X))
      (toLp 2 (Matrix.vec Y)) =
        Matrix.trace (X.conjTranspose * Y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change
    Matrix.vec Y ⬝ᵥ star (Matrix.vec X) =
      Matrix.trace (X.conjTranspose * Y)
  rw [dotProduct_comm, Matrix.star_vec_dotProduct_vec]

/--
@isnad1 id=eq.0h5v.s9.54515f7ea016 from=translated src=- shape=7677c98a vocab=44f1caf2
-/
@[simp] theorem unitaryBasisOverlap_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (U V : Matrix.unitaryGroup d ℂ) (i j : d) :
    unitaryBasisOverlap U V i j =
      (((U : Matrix d d ℂ).conjTranspose *
        (V : Matrix d d ℂ)) i j) := by
  rfl

end

section

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

end

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

/-- The unitary operator implementing orthonormal basis. -/
def orthonormalBasisUnitary
    {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℂ
      (EuclideanSpace ℂ (Fin d))) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩

/--
@isnad1 id=eq.0h4v.s8.1fd53221ca19 from=translated src=- shape=9adc4696 vocab=aff6e49d
-/
@[simp] theorem orthonormalBasisUnitary_apply
    {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℂ
      (EuclideanSpace ℂ (Fin d)))
    (i j : Fin d) :
    orthonormalBasisUnitary b i j = b j i := by
  rfl

/-- The unitary operator implementing conjugate. -/
def conjugateUnitary
    {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin d) ℂ := by
  refine ⟨(U.val.conjTranspose).transpose, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  change
    ((U.val.conjTranspose).transpose).conjTranspose *
      (U.val.conjTranspose).transpose = 1
  have htranspose :
      ((U.val.conjTranspose).transpose).conjTranspose =
        U.val.transpose := by
    ext i j
    simp only [conjTranspose_apply, transpose_apply, RCLike.star_def,
      RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [htranspose]
  have h := congrArg Matrix.transpose U.property.1
  simpa only [star_eq_conjTranspose, transpose_mul, transpose_one] using h

/--
@isnad1 id=eq.0h4v.s8.da446852637f from=translated src=- shape=34d40d55 vocab=9c0e575f
-/
@[simp] theorem conjugateUnitary_apply
    {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (i j : Fin d) :
    conjugateUnitary U i j = star (U i j) := by
  rfl

end

end QuantumParallelRepetition

end
