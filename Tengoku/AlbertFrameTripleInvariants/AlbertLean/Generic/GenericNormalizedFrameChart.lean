import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ChartBridge
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.NormalizedOrbitSection
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.NormalizedRootSwap
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms insert_equations` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms insert_source_fixedSpectrum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms read_insert` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms branchDirection_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reciprocal_involutive` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reciprocal_is_distinct` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# A twenty-parameter family of normalized frames

This construction works over every characteristic-zero
field and uses the accepted `ExplicitFrameChart` and its accepted six source
frame equations.  The parameters are four diagonal entries,
three gauge entries, the twelve off-diagonal entries of the retained moment
matrix, and one determinant root.

The four diagonal moment entries are solved from the two spur/norm systems.
No quotient-domain assertion is used.
-/

noncomputable section

namespace AlbertLean.Generic.GenericNormalizedFrameChart

open Matrix
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Residual.ResidualMatrices
open AlbertLean.Residual.SL4PairAction
open AlbertLean.Residual.NormalizedOrbitSection
open AlbertLean.Generic.ChartBridge

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The parameters of the proposed chart.  The subtype
`i ≠ j` has twelve elements for a `4 x 4` matrix.-/
structure Parameters (K : Type u) where
  (dA0 dA1 dB0 dB1 : K)
  (a b c : K)
  offDiag : (ij : Fin 4 × Fin 4) → ij.1 ≠ ij.2 → K
  Delta : K

def dA2 (p : Parameters K) : K := -p.dA0 - p.dA1
def dB2 (p : Parameters K) : K := -p.dB0 - p.dB1

def spurSumA (p : Parameters K) : K :=
  p.dA0 * p.dA1 + p.dA0 * dA2 p + p.dA1 * dA2 p - p.a + 1

def spurSumB (p : Parameters K) : K :=
  p.dB0 * p.dB1 + p.dB0 * dB2 p + p.dB1 * dB2 p - p.b * p.c + 1

def rawOffDiag (p : Parameters K) (i j : Fin 4) : K :=
  if h : i = j then 0 else p.offDiag (i, j) h

def normWeightedA (p : Parameters K) : K :=
  p.dA0 * p.dA1 * dA2 p - p.dA0 * p.a +
    rawOffDiag p 0 2 + p.a * rawOffDiag p 2 0

def normWeightedB (p : Parameters K) : K :=
  p.dB0 * p.dB1 * dB2 p - p.dB0 * (p.b * p.c) +
    p.b * rawOffDiag p 1 3 + p.c * rawOffDiag p 3 1

/-- The named diagonal pivots.-/
def pivotA (p : Parameters K) : K := p.dA1 - dA2 p
def pivotB (p : Parameters K) : K := p.dB1 - dB2 p

def m00 (p : Parameters K) : K :=
  (normWeightedA p - dA2 p * spurSumA p) / pivotA p
def m22 (p : Parameters K) : K := spurSumA p - m00 p
def m11 (p : Parameters K) : K :=
  (normWeightedB p - dB2 p * spurSumB p) / pivotB p
def m33 (p : Parameters K) : K := spurSumB p - m11 p

def moment (p : Parameters K) : Matrix (Fin 4) (Fin 4) K := fun i j =>
  if h : i = j then ![m00 p, m11 p, m22 p, m33 p] i
  else p.offDiag (i, j) h

/-- The explicitly named principal open used by insertion.-/
structure OpenParameters (K : Type u) [Field K] [CharZero K]
    extends Parameters K where
  pivotA_ne : pivotA toParameters ≠ 0
  pivotB_ne : pivotB toParameters ≠ 0
  Delta_ne : toParameters.Delta ≠ 0
  detMoment_ne : Matrix.det (moment toParameters) ≠ 0
  branch_ne : toParameters.Delta ^ 2 ≠ Matrix.det (moment toParameters)

def residualSection (p : OpenParameters K) : ResidualPair K where
  A := moment p.toParameters * X0Inv p.Delta
  X := X0 p.Delta

theorem residualSection_moment (p : OpenParameters K) :
    AlbertLean.Residual.SL4PairAction.moment (residualSection p) =
      moment p.toParameters := by
  simp only [AlbertLean.Residual.SL4PairAction.moment, residualSection]
  rw [Matrix.mul_assoc, X0Inv_mul_X0 p.Delta p.Delta_ne, Matrix.mul_one]

/-- Insert the twenty parameters into the accepted source chart.-/
def insert (p : OpenParameters K) : ExplicitFrameChart K :=
  chartWithResidualPair
    { diagA := ![p.dA0, p.dA1, dA2 p.toParameters]
      diagB := ![p.dB0, p.dB1, dB2 p.toParameters]
      r1 := 1
      z1 := p.a
      r2 := p.b
      z2 := p.c
      kappa := p.c - p.a * p.b
      s1 := 0
      s2 := 0
      c1 := 0
      c2 := 0 }
    (residualSection p)

@[simp] theorem insert_residualPair (p : OpenParameters K) :
    residualPairOfChart (insert p) = residualSection p := by
  simp [insert]

theorem insert_matrixM (p : OpenParameters K) :
    matrixM (insert p) = moment p.toParameters := by
  rw [matrixM, momentMatrix_eq_AMatrix_mul_XMatrix]
  change AlbertLean.Residual.SL4PairAction.moment
    (residualPairOfChart (insert p)) = moment p.toParameters
  rw [insert_residualPair, residualSection_moment]

theorem insert_orientation (p : OpenParameters K) :
    orientation (insert p) = p.c - p.a * p.b := by
  simp [insert, chartWithResidualPair, orientation, mul_comm]

theorem insert_isKappaLift (p : OpenParameters K) : IsKappaLift (insert p) := by
  simp only [IsKappaLift, insert_orientation]
  rfl

/-- The inserted chart satisfies the six accepted source frame equations.
This is the central equation proof; it uses the actual accepted definitions
through `explicitFrameEquationValues`.-/
theorem insert_equations (p : OpenParameters K) :
    EquationsVanish (explicitFrameEquationValues (insert p)) := by
  simp only [EquationsVanish, explicitFrameEquationValues, insert_matrixM]
  dsimp only [insert, chartWithResidualPair]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [dA2]
  · simp [moment, spurSumA, m22]
  · have h := div_mul_cancel₀
      (normWeightedA p.toParameters - dA2 p.toParameters * spurSumA p.toParameters)
      p.pivotA_ne
    change m00 p.toParameters * pivotA p.toParameters = _ at h
    simp [pivotA, normWeightedA, rawOffDiag] at h
    simp [moment, m22]
    linear_combination -h
  · simp [dB2]
  · simp [moment, spurSumB, m33]
  · have h := div_mul_cancel₀
      (normWeightedB p.toParameters - dB2 p.toParameters * spurSumB p.toParameters)
      p.pivotB_ne
    change m11 p.toParameters * pivotB p.toParameters = _ at h
    simp [pivotB, normWeightedB, rawOffDiag] at h
    simp [moment, m33]
    linear_combination -h

/-- Restatement in the accepted source cubic coordinates.-/
theorem insert_source_fixedSpectrum (p : OpenParameters K) :
    sourceTrace (encoderA (insert p)) = 0 ∧
      sourceSpur (encoderA (insert p)) = -1 ∧
      sourceNorm (encoderA (insert p)) = 0 ∧
      sourceTrace (encoderB (insert p)) = 0 ∧
      sourceSpur (encoderB (insert p)) = -1 ∧
      sourceNorm (encoderB (insert p)) = 0 := by
  exact (equationsVanish_iff_source_fixedSpectrum (insert p)).mp
    (insert_equations p)

/-- Reading every independent scalar after insertion recovers it literally.-/
theorem read_insert (p : OpenParameters K) :
    (insert p).diagA 0 = p.dA0 ∧ (insert p).diagA 1 = p.dA1 ∧
    (insert p).diagB 0 = p.dB0 ∧ (insert p).diagB 1 = p.dB1 ∧
    (insert p).z1 = p.a ∧ (insert p).r2 = p.b ∧ (insert p).z2 = p.c ∧
    (∀ i j, (h : i ≠ j) → matrixM (insert p) i j = p.offDiag (i,j) h) ∧
    Matrix.det (residualPairOfChart (insert p)).X = p.Delta := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro i j h
    rw [insert_matrixM]
    simp [moment, h]
  · rw [insert_residualPair]
    simp [residualSection]

/-- The branch direction is the numerator of `Delta - det(M)/Delta`.-/
theorem branchDirection_ne_zero (p : OpenParameters K) :
    p.Delta - Matrix.det (moment p.toParameters) / p.Delta ≠ 0 := by
  intro h
  apply p.branch_ne
  have hmul := (eq_div_iff p.Delta_ne).mp (sub_eq_zero.mp h)
  simpa [pow_two] using hmul

/-! ## Point-level reciprocal-root specification

These definitions do not yet claim a function-field automorphism.  They pin
the exact normalized-section map which that automorphism must induce.
-/

def normalizedSection (p : OpenParameters K) :
    AlbertLean.Residual.NormalizedRootSwap.NormalizedResidualSection K where
  M := moment p.toParameters
  Delta := p.Delta
  Delta_ne_zero := p.Delta_ne
  detM_ne_zero := p.detMoment_ne

@[simp] theorem normalizedSection_M (p : OpenParameters K) :
    (normalizedSection p).M = moment p.toParameters := rfl

@[simp] theorem normalizedSection_Delta (p : OpenParameters K) :
    (normalizedSection p).Delta = p.Delta := rfl

theorem reciprocal_value (p : OpenParameters K) :
    (AlbertLean.Residual.NormalizedRootSwap.rootSwap
      (normalizedSection p)).Delta =
      Matrix.det (moment p.toParameters) / p.Delta := rfl

theorem reciprocal_M_fixed (p : OpenParameters K) :
    (AlbertLean.Residual.NormalizedRootSwap.rootSwap
      (normalizedSection p)).M = moment p.toParameters := rfl

theorem reciprocal_involutive (p : OpenParameters K) :
    AlbertLean.Residual.NormalizedRootSwap.rootSwap
        (AlbertLean.Residual.NormalizedRootSwap.rootSwap
          (normalizedSection p)) = normalizedSection p := by
  exact AlbertLean.Residual.NormalizedRootSwap.rootSwap_involutive _

theorem reciprocal_is_distinct (p : OpenParameters K) :
    (AlbertLean.Residual.NormalizedRootSwap.rootSwap
      (normalizedSection p)).Delta ≠ p.Delta := by
  intro h
  apply branchDirection_ne_zero p
  exact sub_eq_zero.mpr h.symm

end AlbertLean.Generic.GenericNormalizedFrameChart
