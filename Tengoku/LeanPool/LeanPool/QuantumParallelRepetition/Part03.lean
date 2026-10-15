/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import Tengoku.LeanPool.LeanPool.QuantumParallelRepetition.Part02

/-! # Quantum parallel repetition, part 03 -/

@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

/-- The local matrix norm instance used while elaborating part three. -/
noncomputable local instance matrixComplexContinuousENormPartThree
    {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix m n ℂ)
    (Matrix.normedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup)

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/-- The accepting effect of the left projective threshold measurement. -/
def dSVDensityRationalPhysicalProjector
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    Matrix (Fin d) (Fin d) ℂ :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).effect true

/--
@isnad1 id=possemid.0h5v.s4.b0ef11567809 from=translated src=- shape=31b82251 vocab=8460c764
-/
theorem dSVDensityRationalPhysicalProjector_pos
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (dSVDensityRationalPhysicalProjector w ξ k).PosSemidef :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).positive true

private theorem dSVDensityRationalPhysicalProjector_projective
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    dSVDensityRationalPhysicalProjector w ξ k *
        dSVDensityRationalPhysicalProjector w ξ k =
      dSVDensityRationalPhysicalProjector w ξ k := by
  exact dSVDensityRationalProjectiveThresholdPOVM_projective
    w N k (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ) true

/--
@isnad1 id=possemid.0h5v.s6.e47f23e09202 from=translated src=- shape=2ddc7ef6 vocab=38c5c72f
-/
theorem dSVDensityRationalPhysicalProjector_complement_pos
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (1 - dSVDensityRationalPhysicalProjector w ξ k).PosSemidef :=
  dSVProjectorComplement_posSemidef
    (dSVDensityRationalPhysicalProjector w ξ k)
    (dSVDensityRationalPhysicalProjector_pos w ξ k)
    (dSVDensityRationalPhysicalProjector_projective w ξ k)

/-- The binary measurement combining the accepting projectors over the threshold grid. -/
def dSVDensityRationalPhysicalGlobalPOVM
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) :
    POVM Bool (DSVUniformDensityThresholdLocalIndex N d) :=
  dSVGlobalProjectorBinaryPOVM
    (dSVDensityRationalPhysicalProjector w ξ)
    (dSVDensityRationalPhysicalProjector_pos w ξ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ξ)

/--
The DSV density rational physical diagonal born success construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalPhysicalDiagonalBornSuccess
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ : BipartiteUnitVector d) : ℝ :=
  binaryJointSuccessProbability
    (dSVUniformDensityThresholdSharedDensity grid dimension)
    (dSVDensityRationalPhysicalGlobalPOVM w ξ)
    (transposePOVM
      (dSVDensityRationalPhysicalGlobalPOVM w ξ))

/--
The DSV density rational physical projector cross hazard construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalPhysicalProjectorCrossHazard
    {d : ℕ} (N : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  (∑ k : Fin N,
    (Matrix.trace
      ((dSVDensityRationalPhysicalProjector w ξ k -
        dSVDensityRationalPhysicalProjector w ζ k) *
       (dSVDensityRationalPhysicalProjector w ξ k -
        dSVDensityRationalPhysicalProjector w ζ k))).re) /
      ((d : ℝ) * (N : ℝ))

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The accepting projector at the specified threshold in the complete measurement. -/
def dSVDensityRationalCompleteProjectiveThresholdProjector
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    Matrix (Fin d) (Fin d) ℂ :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).effect true

/--
@isnad1 id=possemid.0h5v.s4.3ca35a439622 from=translated src=- shape=79925a59 vocab=d5b417e3
-/
theorem dSVDensityRationalCompleteProjectiveThresholdProjector_pos
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (dSVDensityRationalCompleteProjectiveThresholdProjector
      w N ξ k).PosSemidef :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).positive true

private theorem dSVDensityRationalCompleteProjectiveThresholdEffect_false
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).effect false =
      1 - dSVDensityRationalCompleteProjectiveThresholdProjector
        w N ξ k := by
  have complete :=
    (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).complete
  rw [Fintype.sum_bool, add_comm] at complete
  exact eq_sub_of_add_eq complete

/--
@isnad1 id=possemid.0h5v.s6.75352b8ed098 from=translated src=- shape=1eeddc3a vocab=8261c1ba
-/
theorem
    dSVDensityRationalCompleteProjectiveThresholdProjector_complement_pos
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (1 - dSVDensityRationalCompleteProjectiveThresholdProjector
      w N ξ k).PosSemidef := by
  rw [← dSVDensityRationalCompleteProjectiveThresholdEffect_false]
  exact (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).positive false

/--
The positive operator-valued measurement implementing DSV density rational complete projective
binary.
-/
def dSVDensityRationalCompleteProjectiveBinaryPOVM
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    POVM Bool (DSVUniformDensityThresholdLocalIndex N d) :=
  dSVGlobalProjectorBinaryPOVM
    (dSVDensityRationalCompleteProjectiveThresholdProjector
      w N ξ)
    (dSVDensityRationalCompleteProjectiveThresholdProjector_pos
      w N ξ)
    (dSVDensityRationalCompleteProjectiveThresholdProjector_complement_pos
      w N ξ)

/-- The finite outcome encoding for DSV density rational complete projective. -/
def dSVDensityRationalCompleteProjectiveOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (a b : Bool) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  coherentBinaryJointOutcome
    (dSVDensityRationalCompleteProjectiveBinaryPOVM
      w N ξ)
    (transposePOVM
      (dSVDensityRationalCompleteProjectiveBinaryPOVM
        w N ζ))
    (dSVUniformDensityThresholdSharedState N d) a b

end

section

open scoped BigOperators ComplexOrder MatrixOrder

/--
@isnad1 id=le.0h2v.s4.4c66681d9852 from=translated src=- shape=787c1379 vocab=c45cf30c
-/
theorem dSVDensityRationalGridPrefix_nonneg
    (N : ℕ) (a : ℝ) :
    0 ≤ dSVUniformDensityGridPrefix N a := by
  unfold dSVUniformDensityGridPrefix
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg
    (dSVUniformDensityThresholdWeight_nonneg N k)
    (by split <;> norm_num)

/--
The DSV density rational canonical accepted coefficient construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalCanonicalAcceptedCoefficient
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) : ℝ :=
  Real.sqrt (w * dSVUniformDensityGridPrefix N
    (dSVRationalSoftPass w
      ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)))

/--
@isnad1 id=eq.1h5v.s6.e5c91ac9bd22 from=translated src=- shape=b5c44d2b vocab=b69d74eb
-/
theorem dSVDensityRationalCanonicalAcceptedCoefficient_sq
    {d : ℕ} {w : ℝ} (width : 0 < w) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    dSVDensityRationalCanonicalAcceptedCoefficient
        w N ξ i ^ 2 =
      w * dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)) := by
  unfold dSVDensityRationalCanonicalAcceptedCoefficient
  apply Real.sq_sqrt
  exact mul_nonneg width.le
    (dSVDensityRationalGridPrefix_nonneg _ _)

/--
The DSV density rational canonical alice basis construction used in the quantum parallel-
repetition argument.
-/
def dSVDensityRationalCanonicalAliceBasis
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  Classical.choose
    (exists_proofDSVUniformDensityPolarLeftCanonicalSchmidt ξ)

/-- The target object for DSV density rational canonical accepted. -/
def dSVDensityRationalCanonicalAcceptedTarget
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  schmidtVector
    (dSVDensityRationalCanonicalAcceptedCoefficient w N ξ)
    (dSVDensityRationalCanonicalAliceBasis ξ)
    (dSVUniformDensityThresholdLeftBobBasis ξ)

/--
@isnad1 id=eq.1h4v.s6.1e4c8829415e from=translated src=- shape=eced8cdf vocab=d0d69e39
-/
theorem dSVDensityRationalCanonicalAcceptedTarget_norm_sq
    {d : ℕ} {w : ℝ} (width : 0 < w) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    ‖dSVDensityRationalCanonicalAcceptedTarget w N ξ‖ ^ 2 =
      w * dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  unfold dSVDensityRationalCanonicalAcceptedTarget
  rw [schmidtVector_norm_sq]
  simp_rw [dSVDensityRationalCanonicalAcceptedCoefficient_sq width]
  unfold dSVDensityRationalLeftProjectiveDiagonalMass
  rw [Finset.mul_sum]

/--
@isnad1 id=ne.3h4v.s7.4ecafa5b2e1c from=translated src=- shape=e389e402 vocab=91aa28a2
-/
theorem dSVDensityRationalCanonicalAcceptedTarget_ne_zero
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    dSVDensityRationalCanonicalAcceptedTarget w N ξ ≠ 0 := by
  intro zero
  have actual :=
    dSVDensityRationalCanonicalAcceptedTarget_norm_sq
      width N ξ
  rw [zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at actual
  have lower :=
    dSVDensityRationalLeftProjectiveDiagonalMass_lower
      width grid ξ
  nlinarith

/-- Normalize the canonical accepted target vector. -/
def dSVDensityRationalCanonicalNormalizedTarget
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  NormedSpace.normalize
    (dSVDensityRationalCanonicalAcceptedTarget w N ξ)

/--
@isnad1 id=eq.3h4v.s7.b78c10968c07 from=translated src=- shape=cd58606e vocab=cf7afbaf
-/
theorem dSVDensityRationalCanonicalNormalizedTarget_norm
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    ‖dSVDensityRationalCanonicalNormalizedTarget
      w N ξ‖ = 1 := by
  unfold dSVDensityRationalCanonicalNormalizedTarget
  exact NormedSpace.norm_normalize
    (dSVDensityRationalCanonicalAcceptedTarget_ne_zero
      width grid fine ξ)

/-- The target object for DSV density rational canonical accepted unit. -/
def dSVDensityRationalCanonicalAcceptedUnitTarget
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    BipartiteUnitVector d :=
  ⟨dSVDensityRationalCanonicalNormalizedTarget w N ξ,
    dSVDensityRationalCanonicalNormalizedTarget_norm
      width grid fine ξ⟩

end

section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def dSVDensityRationalPhysicalMixedBornSuccess
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) : ℝ :=
  binaryJointSuccessProbability
    (dSVUniformDensityThresholdSharedDensity grid dimension)
    (dSVDensityRationalPhysicalGlobalPOVM w ξ)
    (transposePOVM
      (dSVDensityRationalPhysicalGlobalPOVM w ζ))

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

private def dSVDensityRationalActualMixedSuccessMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ‖dSVDensityRationalCompleteProjectiveOutcome
    w N ξ ζ true true‖ ^ 2

private def dSVDensityRationalActualMixedContinueMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ‖dSVDensityRationalCompleteProjectiveOutcome
    w N ξ ζ false false‖ ^ 2

private def dSVDensityRationalActualMixedAsynchronousMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ‖dSVDensityRationalCompleteProjectiveOutcome
      w N ξ ζ true false‖ ^ 2 +
    ‖dSVDensityRationalCompleteProjectiveOutcome
      w N ξ ζ false true‖ ^ 2

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The DSV density rational complete physical stopping copy accepted construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalCompletePhysicalStoppingCopyAccepted
    {N d : ℕ} (w : ℝ) (ξ : BipartiteUnitVector d)
    (q : DSVUniformDensityThresholdLocalIndex N d) : Prop :=
  dSVDensityRationalProjectiveThresholdBin w N q.1
    ((dSVSoftBobLeftReducedDensity_posSemidef
      ξ).isHermitian.eigenvalues q.2) = true

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The finite outcome encoding for DSV density rational physical accepted. -/
def dSVDensityRationalPhysicalAcceptedOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  dSVDensityRationalCompleteProjectiveOutcome
    w N ξ ζ true true

/-- The rank map for DSV density rational physical accepted. -/
def dSVDensityRationalPhysicalAcceptedRank
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    Fin (N + 1) :=
  let selected : Finset (Fin N) :=
    Finset.univ.filter fun k : Fin N =>
      dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ξ).isHermitian.eigenvalues i) = true
  ⟨selected.card, by
    have bounded : selected.card ≤ N := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ selected
    omega⟩

end

section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The DSV density rational prefix rank mismatch construction used in the quantum parallel-
repetition argument.
-/
def dSVDensityRationalPrefixRankMismatch
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  (∑ i : Fin d, ∑ j : Fin d,
    spectralAtomOverlap
      (dSVSoftBobLeftReducedDensity ξ)
      (dSVSoftBobLeftReducedDensity ζ)
      (dSVSoftBobLeftReducedDensity_posSemidef ξ)
      (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j *
      |((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) -
        ((dSVDensityRationalPhysicalAcceptedRank
            w N ζ j).val : ℝ)|) / (N : ℝ)

end

section

open scoped BigOperators ComplexOrder MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

private def dSVDensityRationalMixedSpectralAtomBlock
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Bool) (k : Fin N) : Matrix (Fin d) (Fin d) ℂ :=
  let F := dSVSoftBobLeftReducedDensity ξ
  let G := dSVSoftBobLeftReducedDensity ζ
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  let hG := dSVSoftBobLeftReducedDensity_posSemidef ζ
  ∑ i : Fin d, ∑ j : Fin d,
    if dSVDensityRationalProjectiveThresholdBin w N k
        (hF.isHermitian.eigenvalues i) = a ∧
      dSVDensityRationalProjectiveThresholdBin w N k
        (hG.isHermitian.eigenvalues j) = b
    then positiveMatrixSpectralAtom F hF i *
      positiveMatrixSpectralAtom G hG j
    else 0

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/-- The rank map for DSV density rational physical mixed accepted intersection. -/
def dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : Fin (N + 1) :=
  ⟨min
      (dSVDensityRationalPhysicalAcceptedRank w N ξ i).val
      (dSVDensityRationalPhysicalAcceptedRank w N ζ j).val,
    by
      have left :=
        (dSVDensityRationalPhysicalAcceptedRank w N ξ i).isLt
      have right :=
        (dSVDensityRationalPhysicalAcceptedRank w N ζ j).isLt
      omega⟩

/--
The DSV density rational physical mixed accepted prefix work construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalPhysicalMixedAcceptedPrefixWork
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (i j : Fin d) :
    EuclideanSpace ℂ (Fin N × Fin N) :=
  dSVCanonicalFailurePrefix
    (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
      w N ξ ζ i j)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The diagonal mask selecting accepted threshold and spectral coordinates. -/
def dSVDensityRationalCanonicalPrefixMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    Matrix (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  Matrix.blockDiagonal' fun k : Fin N =>
    Matrix.diagonal fun i : Fin d =>
      if dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true
      then (1 : ℂ) else 0

/-- The finite outcome encoding for DSV density rational canonical prefix spectral. -/
def dSVDensityRationalCanonicalPrefixSpectralOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  toLp 2
    (((dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) ⊗ₖ
      (((dSVUniformDensityBobHistoryCopyBasis
          (N := N) ζ)⁻¹ : Matrix.unitaryGroup
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).mulVec
      (ofLp (dSVDensityRationalPhysicalAcceptedOutcome
        w N ξ ζ)))

/-- The measurement effect for DSV density rational complete stopped optional local. -/
def dSVDensityRationalCompleteStoppedOptionalLocalEffect
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    Option Bool → Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ
  | none => 1
  | some outcome =>
      (dSVDensityRationalCompleteProjectiveBinaryPOVM
        w N ξ).effect outcome

/-- The finite outcome encoding for DSV density rational complete stopped optional. -/
def dSVDensityRationalCompleteStoppedOptionalOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (alice bob : Option Bool) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
       DSVUniformDensityThresholdLocalIndex N d) :=
  toLp 2
    (((dSVDensityRationalCompleteStoppedOptionalLocalEffect
          w N ξ alice) ⊗ₖ
        (dSVDensityRationalCompleteStoppedOptionalLocalEffect
          w N ζ bob).transpose).mulVec
      (ofLp (dSVUniformDensityThresholdSharedState N d)))

/-- The finite schedule for DSV density rational complete stopped optional local. -/
def dSVDensityRationalCompleteStoppedOptionalLocalSchedule
    (L : ℕ) (hit copy : Fin (L + 1)) : Option Bool :=
  if copy.val < L then
    if hit = 0 then some false
    else if copy.val + 1 < hit.val then some false
    else if copy.val + 1 = hit.val then some true
    else none
  else none

end

section

open scoped Kronecker ComplexOrder MatrixOrder

/--
The DSV density rational first accept local spectral mask construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalFirstAcceptLocalSpectralMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (outcome : Bool) :
    Matrix (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  Matrix.blockDiagonal' fun k : Fin N =>
    Matrix.diagonal fun i : Fin d =>
      if dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = outcome
      then (1 : ℂ) else 0

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The DSV density rational first accept actual tensor basis construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalFirstAcceptActualTensorBasis
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (U : Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ :=
  controlledFiniteTensorLocalUnitary
    (fun (_stop : Fin (L + 1)) (_copy : Fin (L + 1)) => U)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The transcript representation for DSV density rational public bucket coherent phase. -/
def dSVDensityRationalPublicBucketCoherentPhaseHistory
    {H : Type*} (B : ℕ)
    (history : EuclideanSpace ℂ (H × H)) :
    EuclideanSpace ℂ ((Fin B × H) × (Fin B × H)) :=
  toLp 2 fun q : (Fin B × H) × (Fin B × H) =>
    ePRState B (q.1.1, q.2.1) *
      history (q.1.2, q.2.2)

/-- The quantum state representing DSV density rational public bucket coherent phase sigma. -/
def dSVDensityRationalPublicBucketCoherentPhaseSigmaState
    {H : Type*} {m : ℕ} (B : ℕ)
    (history : EuclideanSpace ℂ (H × H))
    (work : Fin B → H → H →
      EuclideanSpace ℂ (Fin m × Fin m)) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × H, Fin m) ×
       (Σ _ : Fin B × H, Fin m)) :=
  dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
    (dSVDensityRationalPublicBucketCoherentPhaseHistory
      B history)
    (fun a b => work a.1 a.2 b.2)

/-- The unitary operator implementing DSV density rational public bucket coherent phase local. -/
def dSVDensityRationalPublicBucketCoherentPhaseLocalUnitary
    {H I : Type*} [Fintype H] [DecidableEq H]
     {B D m : ℕ}
    (rank : H → Fin D)
    (bucket : Fin B → Fin D → I)
    (A : Fin B → I → Matrix.unitaryGroup (Fin m) ℂ) :
    Matrix.unitaryGroup (Σ _ : Fin B × H, Fin m) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun q : Fin B × H => A q.1 (bucket q.1 (rank q.2)))

end

section

open scoped BigOperators ComplexOrder MatrixOrder

/--
The DSV density rational public log rank fine label construction used in the quantum parallel-
repetition argument.
-/
def dSVDensityRationalPublicLogRankFineLabel
    {N : ℕ} (Q : ℕ) (r : Fin (N + 1)) : ℕ :=
  Nat.floor ((Q : ℝ) * Real.log ((max 1 r.val : ℕ) : ℝ))

/-- The probability weight for DSV density rational public log rank phase. -/
def dSVDensityRationalPublicLogRankPhaseWeight
    (B : ℕ) (_ : Fin B) : ℝ :=
  1 / (B : ℝ)

/--
The DSV density rational public log rank bucket construction used in the quantum parallel-
repetition argument.
-/
def dSVDensityRationalPublicLogRankBucket
    {N B : ℕ} (Q : ℕ) (phase : Fin B)
    (r : Fin (N + 1)) : Option ℕ :=
  if r.val = 0 then none
  else some
    ((dSVDensityRationalPublicLogRankFineLabel Q r + phase.val) / B)

/-- The nonzero ranks assigned to the given logarithmic bucket and public phase. -/
def dSVDensityRationalPublicLogRankBucketFiber
    {N B : ℕ} (Q : ℕ) (phase : Fin B) (label : Option ℕ) :
    Finset (Fin (N + 1)) :=
  Finset.univ.filter fun r : Fin (N + 1) =>
    r.val ≠ 0 ∧
      dSVDensityRationalPublicLogRankBucket Q phase r = label

/--
The DSV density rational public log rank bucket representative construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalPublicLogRankBucketRepresentative
    {N B : ℕ} (Q : ℕ) (phase : Fin B) (label : Option ℕ) :
    Fin (N + 1) :=
  if present :
    (dSVDensityRationalPublicLogRankBucketFiber
      Q phase label).Nonempty
  then (dSVDensityRationalPublicLogRankBucketFiber
      Q phase label).min' present
  else 0

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The type used to represent DSV density rational public multiscale phase in the exact sampling
construction.
-/
abbrev DSVDensityRationalPublicMultiscalePhase
    (S B : ℕ) :=
  Fin S → Fin B

/--
The type used to represent DSV density rational public multiscale phase index in the exact
sampling construction.
-/
abbrev DSVDensityRationalPublicMultiscalePhaseIndex
    (S B : ℕ) :=
  Fin (Fintype.card
    (DSVDensityRationalPublicMultiscalePhase S B))

/-- The overlap quantity for DSV density rational prefix harmonic spectral. -/
def dSVDensityRationalPrefixHarmonicSpectralOverlap
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : ℝ :=
  spectralAtomOverlap
    (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity ζ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j

/-- The overlap quantity for DSV density rational local spectral pair basis. -/
def dSVDensityRationalLocalSpectralPairBasisOverlap
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : ℂ :=
  unitaryBasisOverlap
    (dSVSoftBobLeftReducedDensity_posSemidef
      ξ).isHermitian.eigenvectorUnitary
    (dSVSoftBobLeftReducedDensity_posSemidef
      ζ).isHermitian.eigenvectorUnitary i j

/-- The transcript representation for DSV density rational local spectral pair. -/
def dSVDensityRationalLocalSpectralPairHistory
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 fun q : Fin d × Fin d =>
    ((‖sharedThresholdResourceRaw (d := Fin d)
      (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
      dSVDensityRationalLocalSpectralPairBasisOverlap
        ξ ζ q.1 q.2

/-- The transposed eigenbasis overlap, repeated on each threshold block. -/
def dSVDensityRationalMixedCanonicalCrossMatrix
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    Matrix (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  (Matrix.blockDiagonal' fun _ : Fin N =>
    (unitaryBasisOverlap
      (dSVSoftBobLeftReducedDensity_posSemidef
        ξ).isHermitian.eigenvectorUnitary
      (dSVSoftBobLeftReducedDensity_posSemidef
        ζ).isHermitian.eigenvectorUnitary :
      Matrix (Fin d) (Fin d) ℂ)).transpose

/-- The source object for DSV density rational mixed canonical raw. -/
def dSVDensityRationalMixedCanonicalRawSource
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  toLp 2
    (Matrix.vec
      (dSVDensityRationalCanonicalPrefixMask w N ζ *
        dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
        dSVDensityRationalCanonicalPrefixMask w N ξ))

/-- Tensor two bipartite vectors while grouping each player's indices together. -/
def dSVDensityRationalPublicLogBilateralPureTensor
    {ι κ : Type*}
    (v : EuclideanSpace ℂ (ι × ι))
    (u : EuclideanSpace ℂ (κ × κ)) :
    EuclideanSpace ℂ ((ι × κ) × (ι × κ)) :=
  toLp 2 fun q : (ι × κ) × (ι × κ) =>
    v (q.1.1, q.2.1) * u (q.1.2, q.2.2)

/--
The type used to represent DSV density rational public log phase history local index in the
exact sampling construction.
-/
abbrev DSVDensityRationalPublicLogPhaseHistoryLocalIndex
    (B N d L : ℕ) :=
  Fin B × DSVUniformDensityThresholdWholeHistoryLocalIndex N d L

/-- The shared history state tensored with the public-phase EPR state. -/
def dSVDensityRationalPublicLogPhasePureSource
    (B N d L : ℕ) :
    EuclideanSpace ℂ
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex B N d L ×
       DSVDensityRationalPublicLogPhaseHistoryLocalIndex B N d L) :=
  dSVDensityRationalPublicLogBilateralPureTensor
    (ePRState B)
    (dSVUniformDensityThresholdWholeHistorySharedState N d L)

/-- Adjoin the harmonic embezzlement state to the public-phase history source. -/
def dSVDensityRationalPublicLogPhaseHarmonicPureSource
    (B N d L m : ℕ) :
    EuclideanSpace ℂ
      ((DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L × Fin m) ×
       (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L × Fin m)) :=
  dSVDensityRationalPublicLogBilateralPureTensor
    (dSVDensityRationalPublicLogPhasePureSource B N d L)
    (embezzlementState m)

/-- The public-phase label paired with the residual whole-history catalyst index. -/
abbrev DSVDensityRationalPublicLogPhaseCatalystIndex
    (B N d L : ℕ) :=
  Fin B × DSVUniformDensityThresholdWholeHistoryCatalystIndex N d L

/-- Separate the target coordinate while retaining the phase in the catalyst index. -/
def dSVDensityRationalPublicLogPhaseTargetSplitEquiv
    (B N d L : ℕ) :
    DSVDensityRationalPublicLogPhaseHistoryLocalIndex B N d L ≃
      (Fin d ×
        DSVDensityRationalPublicLogPhaseCatalystIndex B N d L) where
  toFun q :=
    let actual :=
      dSVUniformDensityThresholdWholeHistoryTargetSplitEquiv
        N d L q.2
    (actual.1, (q.1, actual.2))
  invFun q :=
    (q.2.1,
      (dSVUniformDensityThresholdWholeHistoryTargetSplitEquiv
        N d L).symm (q.1, q.2.2))
  left_inv := by
    rintro ⟨phase, history⟩
    simp only [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨target, phase, catalyst⟩
    simp only [Equiv.apply_symm_apply]

/--
The DSV density rational public log phase residual construction used in the quantum parallel-
repetition argument.
-/
def dSVDensityRationalPublicLogPhaseResidual
    (B N d L m : ℕ) : ℕ :=
  Fintype.card
      (DSVDensityRationalPublicLogPhaseCatalystIndex
        B N d L) * m

/-- The finite equivalence encoding DSV density rational public log phase target first index. -/
def dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
    (B N d L m : ℕ) :
    (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
      B N d L × Fin m) ≃
      Fin (d *
        dSVDensityRationalPublicLogPhaseResidual B N d L m) :=
  (Equiv.prodCongr
    (dSVDensityRationalPublicLogPhaseTargetSplitEquiv B N d L)
    (Equiv.refl (Fin m))).trans
      (dSVRankControlledTargetCatalystIndexEquiv
        (ι := DSVDensityRationalPublicLogPhaseCatalystIndex
          B N d L) d m)

/-- The source object for DSV density rational public log phase target first prepared. -/
def dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
    (B N d L m : ℕ) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicLogPhaseResidual B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicLogPhaseResidual B N d L m)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m)
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m))
    (dSVDensityRationalPublicLogPhaseHarmonicPureSource
      B N d L m)

/--
The type used to represent DSV density rational public multiscale phase history local index in
the exact sampling construction.
-/
abbrev DSVDensityRationalPublicMultiscalePhaseHistoryLocalIndex
    (S B N d L : ℕ) :=
  DSVDensityRationalPublicMultiscalePhaseIndex S B ×
    DSVUniformDensityThresholdWholeHistoryLocalIndex N d L

/--
The DSV density rational public multiscale phase residual construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalPublicMultiscalePhaseResidual
    (S B N d L m : ℕ) : ℕ :=
  dSVDensityRationalPublicLogPhaseResidual
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m

/--
The finite equivalence encoding DSV density rational public multiscale phase target first index.
-/
def dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
    (S B N d L m : ℕ) :
    (DSVDensityRationalPublicMultiscalePhaseHistoryLocalIndex
      S B N d L × Fin m) ≃
      Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) :=
  dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m

/-- The source object for DSV density rational public multiscale phase target first prepared. -/
def dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource
    (S B N d L m : ℕ) :
    EuclideanSpace ℂ
      (Fin (d *
         dSVDensityRationalPublicMultiscalePhaseResidual
           S B N d L m) ×
       Fin (d *
         dSVDensityRationalPublicMultiscalePhaseResidual
           S B N d L m)) :=
  dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

/--
The DSV density rational public log phase actual target first local lift construction used in
the quantum parallel-repetition argument.
-/
def dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
    (B N d L m : ℕ)
    (U : Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ) :
    Matrix.unitaryGroup
      (Fin (d *
        dSVDensityRationalPublicLogPhaseResidual
          B N d L m)) ℂ := by
  classical
  let whole : Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
          B N d L × Fin m) ℂ :=
    ⟨U.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ),
      Matrix.kronecker_mem_unitary U.property
        (Matrix.unitaryGroup (Fin m) ℂ).one_mem⟩
  exact dSVOriginalComputationalReindexedUnitary
    (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
      B N d L m) whole

/-- The unitary operator implementing DSV density rational public log phase physical history. -/
def dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
    (B : ℕ) {N d L : ℕ}
    (U : Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ) :
    Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ := by
  classical
  exact ⟨(1 : Matrix (Fin B) (Fin B) ℂ) ⊗ₖ U.val,
    Matrix.kronecker_mem_unitary
      (Matrix.unitaryGroup (Fin B) ℂ).one_mem U.property⟩

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

attribute [local instance] Classical.propDecidable

/-- The stages whose actual history coordinates satisfy their acceptance predicates. -/
def dSVDensityRationalHeterogeneousActualAcceptSet
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (history : Fin (L + 1) → β) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun j : Fin L =>
    accepted j (history j.castSucc)

/--
The DSV density rational heterogeneous actual first accepted construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousActualFirstAccepted
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (history : Fin (L + 1) → β) : Fin (L + 1) := by
  classical
  let hits := dSVDensityRationalHeterogeneousActualAcceptSet
    accepted history
  exact if nonempty : hits.Nonempty then
    (hits.min' nonempty).succ
  else 0

/-- Swap the zero flag with the first accepted stage, retaining the history. -/
def dSVDensityRationalHeterogeneousActualFirstAcceptEquiv
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop) :
    Equiv.Perm (Σ _ : Fin (L + 1), Fin (L + 1) → β) where
  toFun q :=
    ⟨(Equiv.swap (0 : Fin (L + 1))
      (dSVDensityRationalHeterogeneousActualFirstAccepted
        accepted q.2)) q.1, q.2⟩
  invFun q :=
    ⟨(Equiv.swap (0 : Fin (L + 1))
      (dSVDensityRationalHeterogeneousActualFirstAccepted
        accepted q.2)) q.1, q.2⟩
  left_inv := by
    rintro ⟨flag, history⟩
    simp only [Equiv.swap_apply_self]
  right_inv := by
    rintro ⟨flag, history⟩
    simp only [Equiv.swap_apply_self]

/-- The unitary operator implementing DSV density rational heterogeneous actual first accept. -/
def dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop) :
    Matrix.unitaryGroup (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ :=
  permutationUnitary
    (dSVDensityRationalHeterogeneousActualFirstAcceptEquiv
      accepted)

/--
The DSV density rational heterogeneous actual copy accepted construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousActualCopyAccepted
    {S N d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (j : Fin L)
    (atom : DSVUniformDensityThresholdLocalIndex N d) : Prop :=
  dSVDensityRationalCompletePhysicalStoppingCopyAccepted
    (width (schedule j)) ξ atom

/--
The DSV density rational heterogeneous actual copy condition construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousActualCopyCondition
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (flag : Fin (L + 1)) (i : Fin (L + 1)) (atom : β) : Prop :=
  if active : i.val < L then
    if flag = 0 then
      ¬ accepted ⟨i.val, active⟩ atom
    else if i.val + 1 < flag.val then
      ¬ accepted ⟨i.val, active⟩ atom
    else if i.val + 1 = flag.val then
      accepted ⟨i.val, active⟩ atom
    else True
  else True

/-- The unitary operator implementing DSV density rational heterogeneous actual physical local. -/
def dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop)
    (U : Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ :=
  (dSVDensityRationalFirstAcceptActualTensorBasis
      (L := L) U)⁻¹ *
    dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
      accepted *
    dSVDensityRationalFirstAcceptActualTensorBasis
      (L := L) U

/-- The unitary operator implementing DSV density rational heterogeneous actual alice. -/
def dSVDensityRationalHeterogeneousActualAliceUnitary
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ :=
  dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
    (dSVDensityRationalHeterogeneousActualCopyAccepted
      width schedule ξ)
    (dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ)

/-- The unitary operator implementing DSV density rational heterogeneous actual bob. -/
def dSVDensityRationalHeterogeneousActualBobUnitary
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ζ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ :=
  dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
    (dSVDensityRationalHeterogeneousActualCopyAccepted
      width schedule ζ)
    ((dSVUniformDensityBobHistoryCopyBasis (N := N) ζ)⁻¹)

/-- The quantum state representing DSV density rational heterogeneous actual physical. -/
def dSVDensityRationalHeterogeneousActualPhysicalState
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L ×
       DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) :=
  toLp 2
    ((((dSVDensityRationalHeterogeneousActualAliceUnitary
          N width schedule ξ :
          Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ) ⊗ₖ
        (dSVDensityRationalHeterogeneousActualBobUnitary
          N width schedule ζ :
          Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ)).mulVec
      (ofLp
        (dSVUniformDensityThresholdWholeHistorySharedState
          N d L))))

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder

/-- The finite outcome encoding for DSV density rational heterogeneous physical stage. -/
def dSVDensityRationalHeterogeneousPhysicalStageOutcome
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (k : ℕ) (alice bob : Bool) : ℝ :=
  if active : k < L then
    ‖dSVDensityRationalCompleteProjectiveOutcome
      (width (schedule ⟨k, active⟩)) N ξ ζ alice bob‖ ^ 2
  else if alice = false ∧ bob = false then 1 else 0

/--
The DSV density rational heterogeneous physical stage continue construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousPhysicalStageContinue
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageOutcome
    N width schedule ξ ζ k false false

/--
The DSV density rational heterogeneous physical stage success construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousPhysicalStageSuccess
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageOutcome
    N width schedule ξ ζ k true true

/--
The DSV density rational heterogeneous physical stage asynchronous construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageOutcome
      N width schedule ξ ζ k true false +
    dSVDensityRationalHeterogeneousPhysicalStageOutcome
      N width schedule ξ ζ k false true

/--
The DSV density rational heterogeneous physical survival construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousPhysicalSurvival
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVHeterogeneousRealPrefix
    (dSVDensityRationalHeterogeneousPhysicalStageContinue
      N width schedule ξ ζ) k

/-- The total probability mass of DSV density rational heterogeneous physical stopped success. -/
def dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ k ∈ Finset.range L,
    dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ k *
      dSVDensityRationalHeterogeneousPhysicalStageSuccess
        N width schedule ξ ζ k

/--
The total probability mass of DSV density rational heterogeneous physical stopped asynchronous.
-/
def dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ k ∈ Finset.range L,
    dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ k *
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k

/-- The total probability mass of DSV density rational heterogeneous physical terminal. -/
def dSVDensityRationalHeterogeneousPhysicalTerminalMass
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalSurvival
    N width schedule ξ ζ L

private def dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
      N width schedule ξ ζ k /
    (dSVDensityRationalHeterogeneousPhysicalStageSuccess
        N width schedule ξ ζ k +
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k)

/-- The error rate associated with DSV density rational heterogeneous physical uniform escape. -/
def dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
    (d : ℕ) (W : ℝ) : ℝ :=
  1 / (2 * (W + 1) * (d : ℝ))

end

section

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The probability weight for fair partition. -/
def fairPartitionWeight (α : Type*) [Fintype α] : ℝ :=
  ((2 : ℝ) ^ Fintype.card α)⁻¹

/-- The probability weight for reverse partition. -/
def reversePartitionWeight (s : Finset α) : ℝ :=
  fairPartitionWeight α *
    (2 * (s.card : ℝ) / (Fintype.card α : ℝ))

/-- The probability weight for forward marked partition. -/
def forwardMarkedPartitionWeight (α : Type*) [Fintype α] : ℝ :=
  2 * fairPartitionWeight α / (Fintype.card α : ℝ)

/-- The probability weight for reverse marked partition. -/
def reverseMarkedPartitionWeight (s : Finset α) (i : α) : ℝ :=
  if i ∈ s then reversePartitionWeight s / (s.card : ℝ) else 0

omit [DecidableEq α] in
/--
@isnad1 id=lt.0h1v.s4.3b8c4a30387e from=translated src=- shape=533eefa4 vocab=d869f42c
-/
theorem fairPartitionWeight_pos : 0 < fairPartitionWeight α := by
  unfold fairPartitionWeight
  positivity

omit [DecidableEq α] in
/--
@isnad1 id=le.0h1v.s4.2517bc79efb6 from=translated src=- shape=533eefa4 vocab=381201d5
-/
theorem fairPartitionWeight_nonneg : 0 ≤ fairPartitionWeight α :=
  fairPartitionWeight_pos.le

omit [DecidableEq α] in
/--
@isnad1 id=le.0h2v.s4.b66c769dda12 from=translated src=- shape=38fc717e vocab=b2e2b386
-/
theorem reversePartitionWeight_nonneg (s : Finset α) :
    0 ≤ reversePartitionWeight s := by
  unfold reversePartitionWeight
  exact mul_nonneg fairPartitionWeight_nonneg
    (div_nonneg
      (mul_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le s.card))
      (by exact_mod_cast Nat.zero_le (Fintype.card α)))

omit [DecidableEq α] in
/--
@isnad1 id=eq.0h1v.s4.09046cbf5f20 from=translated src=- shape=bba61b78 vocab=e237a5d3
-/
@[simp] theorem reversePartitionWeight_empty :
    reversePartitionWeight (α := α) ∅ = 0 := by
  simp only [reversePartitionWeight, card_empty, CharP.cast_eq_zero, mul_zero, zero_div]

omit [DecidableEq α] in
/--
@isnad1 id=iff.1h2v.s5.66d9f455c4b0 from=translated src=- shape=2ce58609 vocab=c0486a2a
-/
theorem reversePartitionWeight_pos_iff
    (hα : 0 < Fintype.card α) (s : Finset α) :
    0 < reversePartitionWeight s ↔ s.Nonempty := by
  constructor
  · intro hs
    apply Finset.card_pos.mp
    by_contra hcard
    have hzero : s.card = 0 := Nat.eq_zero_of_not_pos hcard
    simp only [reversePartitionWeight, hzero, CharP.cast_eq_zero, mul_zero, zero_div,
      lt_self_iff_false] at hs
  · intro hs
    unfold reversePartitionWeight
    have hcard : 0 < s.card := Finset.card_pos.mpr hs
    exact mul_pos fairPartitionWeight_pos
      (div_pos
        (mul_pos (by norm_num) (by exact_mod_cast hcard))
        (by exact_mod_cast hα))

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def rightSpectralBornWeight
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
     [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (i : dB) : ℝ :=
  bornTracePairing ρ.matrix F
    (positiveMatrixSpectralAtom G hG i)

section HistoryNormalization

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def fullSubsetHistoryFieldEquiv
    {n : ℕ} (D L : Finset (Fin n)) :
    FullSubsetHistory X Y n D L ≃
      (({i : Fin n // i ∈ D} → X × Y) ×
       ({i : Fin n // i ∈ L} → X) ×
       ({i : Fin n // i ∈ fullHistoryRemaining n D L} → Y)) where
  toFun h :=
    (fun i => (h.aliceConditioned i, h.bobConditioned i),
      h.aliceRevealed, h.bobRemaining)
  invFun t :=
    ⟨fun i => (t.1 i).1,
      fun i => (t.1 i).2,
      t.2.1, t.2.2⟩
  left_inv h := by
    apply FullSubsetHistory.ext <;> rfl
  right_inv t := by
    rcases t with ⟨q, x, y⟩
    simp only [Prod.mk.eta]

end HistoryNormalization

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The full history answer count construction used in the quantum parallel-repetition argument. -/
def fullHistoryAnswerCount
    {A B : Type*} [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) : ℝ :=
  (Fintype.card ({i : Fin n // i ∈ D} → A) : ℝ) *
    (Fintype.card ({i : Fin n // i ∈ D} → B) : ℝ)

/-- The type used to represent full history entropy atom in the exact sampling construction. -/
abbrev FullHistoryEntropyAtom
    (X Y A B : Type*)
    (n : ℕ) (D L : Finset (Fin n)) :=
  FullSubsetHistory X Y n D L ×
    ({i : Fin n // i ∈ D} → A) ×
    ({i : Fin n // i ∈ D} → B)

/-- The probability weight for full history atom counting. -/
def fullHistoryAtomCountingWeight
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n))
    (t : FullHistoryEntropyAtom X Y A B n D L) : ℝ :=
  fullHistoryWeight G t.1 *
    fullHistoryWinIndicator G t.1 t.2.1 t.2.2

/-- The total probability mass of full history atom born. -/
def fullHistoryAtomBornMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (t : FullHistoryEntropyAtom X Y A B n D L) : ℝ :=
  bornTracePairing S.state.matrix
    (fullHistoryAliceFilter G n S D L t.1 t.2.1)
    (fullHistoryBobFilter G n S D L t.1 t.2.2)

end

section

open scoped BigOperators

/-- A transcript in which one additional coordinate is being revealed. -/
@[ext (iff := false)] structure FullCoordinateRevealHistory
    (X Y : Type*)
    (n : ℕ) (D L : Finset (Fin n)) (i : Fin n) where
  /-- Alice's conditioned part of the transcript. -/
  aliceConditioned : {j : Fin n // j ∈ D} → X
  /-- Bob's conditioned part of the transcript. -/
  bobConditioned : {j : Fin n // j ∈ D} → Y
  /-- Alice's already revealed questions. -/
  aliceRevealed : {j : Fin n // j ∈ L} → X
  /-- Bob's questions outside the revealed coordinates. -/
  bobRemaining :
    {j : Fin n // j ∈ fullHistoryRemaining n D (insert i L)} → Y
  deriving Fintype

/--
@isnad1 id=le.0h4v.s5.eed65b1413cc from=translated src=- shape=5af8a8b1 vocab=bca49609
-/
theorem fullHistoryRemaining_insert_subset
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n) :
    fullHistoryRemaining n D (insert i L) ⊆
      fullHistoryRemaining n D L := by
  intro j hj
  simp only [fullHistoryRemaining, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_insert] at hj ⊢
  exact ⟨hj.1, fun h => hj.2 (Or.inr h)⟩

private def fullCoordinateBaseOfOldHistory
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullSubsetHistory X Y n D L) :
    FullCoordinateRevealHistory X Y n D L i where
  aliceConditioned := h.aliceConditioned
  bobConditioned := h.bobConditioned
  aliceRevealed := h.aliceRevealed
  bobRemaining := fun j => h.bobRemaining
    ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩

/-- The transcript representation for full coordinate old. -/
def fullCoordinateOldHistory
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i)
    (y : Y) : FullSubsetHistory X Y n D L := by
  classical
  refine ⟨h.aliceConditioned, h.bobConditioned, h.aliceRevealed,
    fun j => if hj : (j : Fin n) = i then y else
      h.bobRemaining ⟨j, ?_⟩⟩
  have hjD : (j : Fin n) ∉ D :=
    (Finset.mem_sdiff.mp
      (Finset.mem_sdiff.mp j.property).1).2
  have hjL : (j : Fin n) ∉ L :=
    (Finset.mem_sdiff.mp j.property).2
  simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hjD, not_false_eq_true, and_self,
    mem_insert, hj, hjL, or_self]

private def fullCoordinateBaseOfNewHistory
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullSubsetHistory X Y n D (insert i L)) :
    FullCoordinateRevealHistory X Y n D L i where
  aliceConditioned := h.aliceConditioned
  bobConditioned := h.bobConditioned
  aliceRevealed := fun j => h.aliceRevealed
    ⟨j, Finset.mem_insert_of_mem j.property⟩
  bobRemaining := h.bobRemaining

/-- The transcript representation for full coordinate new. -/
def fullCoordinateNewHistory
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i)
    (x : X) : FullSubsetHistory X Y n D (insert i L) := by
  classical
  refine ⟨h.aliceConditioned, h.bobConditioned,
    fun j => if hj : (j : Fin n) = i then x else
      h.aliceRevealed ⟨j, ?_⟩,
    h.bobRemaining⟩
  exact (Finset.mem_insert.mp j.property).resolve_left hj

private def fullCoordinateOldHistoryEquiv
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    FullSubsetHistory X Y n D L ≃
      FullCoordinateRevealHistory X Y n D L i × Y where
  toFun h :=
    (fullCoordinateBaseOfOldHistory D L i h,
      h.bobRemaining
        ⟨i, by simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hiD, not_false_eq_true,
                 and_self, hiL]⟩)
  invFun t := fullCoordinateOldHistory D L i t.1 t.2
  left_inv h := by
    apply FullSubsetHistory.ext
    · rfl
    · rfl
    · rfl
    · funext j
      by_cases hj : (j : Fin n) = i
      · subst i
        simp only [fullCoordinateOldHistory, fullCoordinateBaseOfOldHistory, SetLike.coe_eq_coe,
          Subtype.coe_eta, dite_eq_ite, ↓reduceIte]
      · simp only [fullCoordinateOldHistory, fullCoordinateBaseOfOldHistory, Subtype.coe_eta,
          dite_eq_ite, hj, ↓reduceIte]
  right_inv t := by
    rcases t with ⟨h, y⟩
    apply Prod.ext
    · apply FullCoordinateRevealHistory.ext
      · rfl
      · rfl
      · rfl
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          have hnot : (j : Fin n) ∉ insert i L :=
            (Finset.mem_sdiff.mp j.property).2
          apply hnot
          simp only [he, mem_insert, true_or]
        simp only [fullCoordinateBaseOfOldHistory, fullCoordinateOldHistory, hj]
        split <;> simp_all
    · simp only [fullCoordinateOldHistory, ↓reduceDIte]

private def fullCoordinateNewHistoryEquiv
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiL : i ∉ L) :
    FullSubsetHistory X Y n D (insert i L) ≃
      FullCoordinateRevealHistory X Y n D L i × X where
  toFun h :=
    (fullCoordinateBaseOfNewHistory D L i h,
      h.aliceRevealed ⟨i, Finset.mem_insert_self i L⟩)
  invFun t := fullCoordinateNewHistory D L i t.1 t.2
  left_inv h := by
    apply FullSubsetHistory.ext
    · rfl
    · rfl
    · funext j
      by_cases hj : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i L⟩ :
              {j : Fin n // j ∈ insert i L}) :=
          Subtype.ext hj
        subst j
        simp only [fullCoordinateNewHistory, fullCoordinateBaseOfNewHistory, Subtype.coe_eta,
          dite_eq_ite, ↓reduceIte]
      · simp only [fullCoordinateNewHistory, fullCoordinateBaseOfNewHistory, Subtype.coe_eta,
          dite_eq_ite, hj, ↓reduceIte]
    · rfl
  right_inv t := by
    rcases t with ⟨h, x⟩
    apply Prod.ext
    · apply FullCoordinateRevealHistory.ext
      · rfl
      · rfl
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          exact hiL (he ▸ j.property)
        simp only [fullCoordinateBaseOfNewHistory, fullCoordinateNewHistory, Subtype.coe_eta,
          dite_eq_ite, hj, ↓reduceIte]
      · rfl
    · simp only [fullCoordinateNewHistory, ↓reduceDIte]

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def fullHistoryRemainingCoordinateEquiv
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    {j : Fin n // j ∈ fullHistoryRemaining n D L} ≃
      Option {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} where
  toFun j :=
    if hj : (j : Fin n) = i then none
    else some ⟨j, by
      have hjD : (j : Fin n) ∉ D :=
        (Finset.mem_sdiff.mp
          (Finset.mem_sdiff.mp j.property).1).2
      have hjL : (j : Fin n) ∉ L :=
        (Finset.mem_sdiff.mp j.property).2
      simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hjD, not_false_eq_true, and_self,
        mem_insert, hj, hjL, or_self]⟩
  invFun
    | none => ⟨i, by simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hiD, not_false_eq_true,
                       and_self, hiL]⟩
    | some j =>
      ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩
  left_inv j := by
    apply Subtype.ext
    by_cases hj : (j : Fin n) = i
    · simp only [hj, ↓reduceDIte]
    · simp only [hj, ↓reduceDIte, Subtype.coe_eta]
  right_inv j := by
    cases j with
    | none => simp
    | some j =>
      have hj : (j : Fin n) ≠ i := by
        intro he
        have hnot : (j : Fin n) ∉ insert i L :=
          (Finset.mem_sdiff.mp j.property).2
        apply hnot
        simp only [he, mem_insert, true_or]
      simp only [hj, ↓reduceDIte]

section CoordinateWeights

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The probability weight for full coordinate base. -/
def fullCoordinateBaseWeight
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i) : ℝ :=
  (∏ j : {j : Fin n // j ∈ D},
    G.questionWeight (h.aliceConditioned j) (h.bobConditioned j)) *
  (∏ j : {j : Fin n // j ∈ L},
    G.marginalX (h.aliceRevealed j)) *
  (∏ j : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)},
    G.marginalY (h.bobRemaining j))

end CoordinateWeights

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- Alice's history filter after revealing the selected coordinate's question. -/
def fullCoordinateAliceQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A) (x : X) :
    Matrix S.Alice S.Alice ℂ :=
  fullHistoryAliceFilter G n S D (insert i L)
    (fullCoordinateNewHistory D L i r x) α

/-- Alice's history filter before the new question is revealed. -/
def fullCoordinateAliceMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A) (y : Y) :
    Matrix S.Alice S.Alice ℂ :=
  fullHistoryAliceFilter G n S D L
    (fullCoordinateOldHistory D L i r y) α

/-- Bob's history filter for the selected question and the previously revealed history. -/
def fullCoordinateBobQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (β : {j : Fin n // j ∈ D} → B) (y : Y) :
    Matrix S.Bob S.Bob ℂ :=
  fullHistoryBobFilter G n S D L
    (fullCoordinateOldHistory D L i r y) β

private def fullCoordinateBobMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (β : {j : Fin n // j ∈ D} → B) (x : X) :
    Matrix S.Bob S.Bob ℂ :=
  fullHistoryBobFilter G n S D (insert i L)
    (fullCoordinateNewHistory D L i r x) β

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def fullCoordinateAssembleHiddenAlice
    {X : Type*} {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (x : X)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    {j : Fin n // j ∈ fullHistoryRemaining n D L} → X := by
  classical
  intro j
  by_cases hj : (j : Fin n) = i
  · exact x
  · exact hidden ⟨j, by
      have hjD : (j : Fin n) ∉ D :=
        (Finset.mem_sdiff.mp
          (Finset.mem_sdiff.mp j.property).1).2
      have hjL : (j : Fin n) ∉ L :=
        (Finset.mem_sdiff.mp j.property).2
      simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hjD, not_false_eq_true, and_self,
        mem_insert, hj, hjL, or_self]⟩

private def fullCoordinateHiddenAliceEquiv
    {X : Type*} {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    ({j : Fin n // j ∈ fullHistoryRemaining n D L} → X) ≃
      X × ({j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} → X) where
  toFun hidden :=
    (hidden ⟨i, by simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hiD, not_false_eq_true,
                     and_self, hiL]⟩,
      fun j => hidden
        ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩)
  invFun t := fullCoordinateAssembleHiddenAlice D L i t.1 t.2
  left_inv hidden := by
    funext j
    by_cases hj : (j : Fin n) = i
    · have hjsub :
          j = (⟨i, by simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hiD,
                        not_false_eq_true, and_self, hiL]⟩ :
            {j : Fin n // j ∈ fullHistoryRemaining n D L}) :=
        Subtype.ext hj
      subst j
      simp only [fullCoordinateAssembleHiddenAlice, ↓reduceDIte]
    · simp only [fullCoordinateAssembleHiddenAlice, hj, ↓reduceDIte, Subtype.coe_eta]
  right_inv t := by
    rcases t with ⟨x, hidden⟩
    apply Prod.ext
    · simp only [fullCoordinateAssembleHiddenAlice, ↓reduceDIte]
    · funext j
      have hj : (j : Fin n) ≠ i := by
        intro he
        have hnot : (j : Fin n) ∉ insert i L :=
          (Finset.mem_sdiff.mp j.property).2
        apply hnot
        simp only [he, mem_insert, true_or]
      simp only [fullCoordinateAssembleHiddenAlice, hj, ↓reduceDIte]

private def fullCoordinateAssembleHiddenBob
    {Y : Type*} {n : ℕ}
    (L : Finset (Fin n)) (i : Fin n)
    (y : Y) (hidden : {j : Fin n // j ∈ L} → Y) :
    {j : Fin n // j ∈ insert i L} → Y := by
  classical
  intro j
  by_cases hj : (j : Fin n) = i
  · exact y
  · exact hidden
      ⟨j, (Finset.mem_insert.mp j.property).resolve_left hj⟩

private def fullCoordinateHiddenBobEquiv
    {Y : Type*} {n : ℕ}
    (L : Finset (Fin n)) (i : Fin n) (hiL : i ∉ L) :
    ({j : Fin n // j ∈ insert i L} → Y) ≃
      Y × ({j : Fin n // j ∈ L} → Y) where
  toFun hidden :=
    (hidden ⟨i, Finset.mem_insert_self i L⟩,
      fun j => hidden ⟨j, Finset.mem_insert_of_mem j.property⟩)
  invFun t := fullCoordinateAssembleHiddenBob L i t.1 t.2
  left_inv hidden := by
    funext j
    by_cases hj : (j : Fin n) = i
    · have hjsub :
          j = (⟨i, Finset.mem_insert_self i L⟩ :
            {j : Fin n // j ∈ insert i L}) :=
        Subtype.ext hj
      subst j
      simp only [fullCoordinateAssembleHiddenBob, ↓reduceDIte]
    · simp only [fullCoordinateAssembleHiddenBob, hj, ↓reduceDIte, Subtype.coe_eta]
  right_inv t := by
    rcases t with ⟨y, hidden⟩
    apply Prod.ext
    · simp only [fullCoordinateAssembleHiddenBob, ↓reduceDIte]
    · funext j
      have hj : (j : Fin n) ≠ i := by
        intro he
        exact hiL (he ▸ j.property)
      simp only [fullCoordinateAssembleHiddenBob, hj, ↓reduceDIte, Subtype.coe_eta]

section CoordinateFilters

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end CoordinateFilters

section ConditionalJensen

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The averaged entropy increment between Alice's question and mean filters. -/
def fullCoordinateAliceEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) : ℝ :=
  ∑ y : Y, G.marginalY y *
    bornTracePairing S.state.matrix
      (conditionalAliceAverage G
        (fun x => cfc (fun z : ℝ => z * Real.log z)
          (fullCoordinateAliceQuestionFilter G n S D L i r α x)) y -
        cfc (fun z : ℝ => z * Real.log z)
          (fullCoordinateAliceMeanFilter G n S D L i r α y))
      (fullCoordinateBobQuestionFilter G n S D L i r β y)

end ConditionalJensen

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The indicator function for full coordinate base win. -/
def fullCoordinateBaseWinIndicator
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) : ℝ := by
  classical
  exact if ∀ j : {j : Fin n // j ∈ D},
    G.predicate (r.aliceConditioned j) (r.bobConditioned j)
      (α j) (β j) = true then 1 else 0

/-- The information increment contributed by full coordinate alice total entropy. -/
def fullCoordinateAliceTotalEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n) : ℝ :=
  ∑ r : FullCoordinateRevealHistory X Y n D L i,
  ∑ α : {j : Fin n // j ∈ D} → A,
  ∑ β : {j : Fin n // j ∈ D} → B,
    fullCoordinateBaseWeight G D L i r *
      fullCoordinateBaseWinIndicator G D L i r α β *
      fullCoordinateAliceEntropyIncrement G n S D L i r α β

end

end QuantumParallelRepetition

end
