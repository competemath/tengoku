import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.LawfulChart
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualLedgerMomentField
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualPowerMeasurements
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualSourceMeasurements
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.UniformLedgerMeasurements

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms equationValues_reinsert_of_moment_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceLedger_eq_of_power_diagonal_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms power_diagonal_reinsert_of_sameResidualBase` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms companion_equations_and_sourceLedger` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Actual root-swapped companions on an arbitrary characteristic-zero field

This candidate keeps the statement at an actual explicit chart.  It proves
literal equality of the source 54-ledger, rather than equality of generated
fields.  There is no coverage, conclusion, naturality, or invariant-field
premise.
-/

noncomputable section

namespace AlbertLean.Generic.AlbertActualCompanion

open AlbertLean.Generic.ChartBridge
open AlbertLean.Generic.ResidualLedgerPower
open AlbertLean.Generic.ResidualLedgerMomentField
open AlbertLean.Generic.ResidualPowerMeasurements
open AlbertLean.Generic.ResidualSourceMeasurements
open AlbertLean.Generic.UniformLedgerMeasurements
open AlbertLean.Generic.ProductDiagonal
open AlbertLean.Residual.ResidualMatrices
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Residual.ResidualTwoOrbit
open AlbertLean.Residual.SL4PairAction
open AlbertLean.Residual.TrialitySquares
open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Triality.StructuredProduct

variable {K : Type*} [Field K] [CharZero K]

private theorem fin3_mk_zero_eq_zero (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := by
  apply Fin.ext
  rfl

private theorem fin3_mk_one_eq_one (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := by
  apply Fin.ext
  rfl

private theorem fin3_mk_two_eq_two (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := by
  apply Fin.ext
  rfl

private theorem matrixM_eq_moment (x : ExplicitFrameChart K) :
    matrixM x = moment (residualPairOfChart x) := by
  simpa [matrixM, residualPairOfChart, moment] using
    (momentMatrix_eq_AMatrix_mul_XMatrix x.s1 x.s2 x.c1 x.c2)

/-- The existing rational proof is field-polymorphic: only the residual
moment and the retained chart coefficients occur in the six equations.
@isnad1 id=eq.1h3v.s5.5186a090d13e from=translated src=- shape=bd4c978b vocab=eddab8bb
-/
theorem equationValues_reinsert_of_moment_eq
    (x : ExplicitFrameChart K) (Q : ResidualPair K)
    (hQ : moment Q = moment (residualPairOfChart x)) :
    explicitFrameEquationValues (chartWithResidualPair x Q) =
      explicitFrameEquationValues x := by
  have hM : matrixM (chartWithResidualPair x Q) = matrixM x := by
    calc
      matrixM (chartWithResidualPair x Q) =
          moment (residualPairOfChart (chartWithResidualPair x Q)) :=
        matrixM_eq_moment _
      _ = moment Q := by rw [residualPairOfChart_chartWithResidualPair]
      _ = moment (residualPairOfChart x) := hQ
      _ = matrixM x := (matrixM_eq_moment x).symm
  have hdiagA : (chartWithResidualPair x Q).diagA = x.diagA := rfl
  have hdiagB : (chartWithResidualPair x Q).diagB = x.diagB := rfl
  have hr1 : (chartWithResidualPair x Q).r1 = x.r1 := rfl
  have hz1 : (chartWithResidualPair x Q).z1 = x.z1 := rfl
  have hr2 : (chartWithResidualPair x Q).r2 = x.r2 := rfl
  have hz2 : (chartWithResidualPair x Q).z2 = x.z2 := rfl
  apply FrameEquationValues.ext <;>
    simp only [explicitFrameEquationValues, hdiagA, hdiagB,
      hr1, hz1, hr2, hz2, hM]

/-- The fixed tensor change from projectors to powers is invertible.  Thus
equality of the 27 diagonal power products gives literal equality of every
one of the 54 labelled source-ledger cells.
@isnad1 id=eq.1h5v.s8.413e3f1a99b3 from=translated src=- shape=29cc20a5 vocab=4a7bd6ae
-/
theorem sourceLedger_eq_of_power_diagonal_eq (a b a' b' : JCoord K)
    (h : ∀ i p q, diagLinear i (sourceProduct (power a p) (power b q)) =
      diagLinear i (sourceProduct (power a' p) (power b' q))) :
    sourceLedger a b = sourceLedger a' b' := by
  have hraw (i j l : Fin 3) :
      diagonalProduct i (spectralProjector a j) (spectralProjector b l) =
        diagonalProduct i (spectralProjector a' j) (spectralProjector b' l) := by
    rw [projector_eq_weighted_powers a j, projector_eq_weighted_powers b l,
      projector_eq_weighted_powers a' j, projector_eq_weighted_powers b' l]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, diagonalProduct_apply]
    apply Finset.sum_congr rfl
    intro p hp
    apply congrArg (fun z => projectorWeight l p * z)
    apply Finset.sum_congr rfl
    intro q hq
    rw [h i q p]
  have hdiagA (i j : Fin 3) :
      diagLinear i (spectralProjector a j) =
        diagLinear i (spectralProjector a' j) := by
    rw [projector_eq_weighted_powers a j, projector_eq_weighted_powers a' j]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 := h i p 0
    simp only [power, Matrix.cons_val_zero, sourceProduct_one_right] at hp0
    change diagLinear i (power a p) = diagLinear i (power a' p) at hp0
    rw [hp0]
  have hdiagB (i l : Fin 3) :
      diagLinear i (spectralProjector b l) =
        diagLinear i (spectralProjector b' l) := by
    rw [projector_eq_weighted_powers b l, projector_eq_weighted_powers b' l]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro q hq
    have h0q := h i 0 q
    simp only [power, Matrix.cons_val_zero, sourceProduct_one_left] at h0q
    change diagLinear i (power b q) = diagLinear i (power b' q) at h0q
    rw [h0q]
  apply SourceLedger.ext
  · funext i j
    simp only [sourceLedger, diagonal_trace]
    exact hdiagA i j
  · funext j l
    simp only [sourceLedger, traceForm_eq_sum_diagonalProduct]
    rw [hraw 0 j l, hraw 1 j l, hraw 2 j l]
  · funext l i
    simp only [sourceLedger, sourceTraceForm_symmetric, diagonal_trace]
    exact hdiagB i l
  · funext i j l
    simp only [sourceLedger, diagonal_trace, diagonalProduct_apply]
    have hraw' := hraw i j l
    simp only [diagonalProduct_apply] at hraw'
    rw [sourceTraceForm_symmetric (spectralProjector b l) (diagonalUnit i),
      sourceTraceForm_symmetric (spectralProjector b' l) (diagonalUnit i)]
    simp only [diagonal_trace]
    rw [hraw', hdiagA i j, hdiagB i l]
    have hQ : sourceTraceForm (spectralProjector a j) (spectralProjector b l) =
        sourceTraceForm (spectralProjector a' j) (spectralProjector b' l) := by
      rw [traceForm_eq_sum_diagonalProduct,
        traceForm_eq_sum_diagonalProduct,
        hraw 0 j l, hraw 1 j l, hraw 2 j l]
    rw [hQ]

/-! Scalar chart identities used by the finite equality calculation.  These
are the equality versions of the accepted reverse-dictionary measurements. -/

private theorem chart_normS1 (x : ExplicitFrameChart K) :
    nS x.s1 = matrixM x 0 0 := rfl

private theorem chart_normS2 (x : ExplicitFrameChart K) :
    nS x.s2 = matrixM x 1 1 := rfl

private theorem chart_normC1 (x : ExplicitFrameChart K) :
    nC x.c1 = matrixM x 2 2 := rfl

private theorem chart_normC2 (x : ExplicitFrameChart K) :
    nC x.c2 = matrixM x 3 3 := rfl

private theorem chart_normVA (x : ExplicitFrameChart K) :
    nV (vectorA x) = x.r1 * x.z1 := by
  simp [nV, vectorA, Pf, BW]

private theorem chart_normVB (x : ExplicitFrameChart K) :
    nV (vectorB x) = x.r2 * x.z2 := by
  simp [nV, vectorB, Pf, BW]

private theorem chart_gramV (x : ExplicitFrameChart K) :
    BV (vectorA x) (vectorB x) = x.r1 * x.z2 + x.z1 * x.r2 := by
  simp [BV, BW, vectorA, vectorB]

private theorem chart_gramS (x : ExplicitFrameChart K) :
    BS x.s1 x.s2 = matrixM x 0 1 + matrixM x 1 0 := rfl

private theorem chart_gramC (x : ExplicitFrameChart K) :
    BC x.c1 x.c2 = matrixM x 2 3 + matrixM x 3 2 := rfl

private theorem chart_trialityA1C2 (x : ExplicitFrameChart K) :
    triality (vectorA x) x.s1 x.c2 =
      x.r1 * matrixM x 0 3 + x.z1 * matrixM x 3 0 := by
  change triality (planeVector x.r1 x.z1) x.s1 x.c2 = _
  rw [plane_triality]
  rfl

private theorem chart_trialityA2C1 (x : ExplicitFrameChart K) :
    triality (vectorA x) x.s2 x.c1 =
      x.r1 * matrixM x 1 2 + x.z1 * matrixM x 2 1 := by
  change triality (planeVector x.r1 x.z1) x.s2 x.c1 = _
  rw [plane_triality]
  rfl

private theorem chart_trialityA2C2 (x : ExplicitFrameChart K) :
    triality (vectorA x) x.s2 x.c2 =
      x.r1 * matrixM x 1 3 + x.z1 * matrixM x 3 1 := by
  change triality (planeVector x.r1 x.z1) x.s2 x.c2 = _
  rw [plane_triality]
  rfl

private theorem chart_trialityB1C2 (x : ExplicitFrameChart K) :
    triality (vectorB x) x.s1 x.c2 =
      x.r2 * matrixM x 0 3 + x.z2 * matrixM x 3 0 := by
  change triality (planeVector x.r2 x.z2) x.s1 x.c2 = _
  rw [plane_triality]
  rfl

private theorem chart_trialityB2C1 (x : ExplicitFrameChart K) :
    triality (vectorB x) x.s2 x.c1 =
      x.r2 * matrixM x 1 2 + x.z2 * matrixM x 2 1 := by
  change triality (planeVector x.r2 x.z2) x.s2 x.c1 = _
  rw [plane_triality]
  rfl

private theorem chart_trialityB1C1 (x : ExplicitFrameChart K) :
    triality (vectorB x) x.s1 x.c1 =
      x.r2 * matrixM x 0 2 + x.z2 * matrixM x 2 0 := by
  change triality (planeVector x.r2 x.z2) x.s1 x.c1 = _
  rw [plane_triality]
  rfl

private theorem chart_UC (x : ExplicitFrameChart K) :
    BC (sourceMuC (vectorA x) x.s1) (sourceMuC (vectorB x) x.s2) =
      x.r1 * x.z2 * matrixM x 0 1 + x.r2 * x.z1 * matrixM x 1 0 := by
  change BC (sourceMuC (planeVector x.r1 x.z1) x.s1)
    (sourceMuC (planeVector x.r2 x.z2) x.s2) = _
  rw [plane_muC_pairing]
  rfl

private theorem chart_US (x : ExplicitFrameChart K) :
    BS (sourceMuS x.c1 (vectorA x)) (sourceMuS x.c2 (vectorB x)) =
      x.r2 * x.z1 * matrixM x 2 3 + x.r1 * x.z2 * matrixM x 3 2 := by
  change BS (sourceMuS x.c1 (planeVector x.r1 x.z1))
    (sourceMuS x.c2 (planeVector x.r2 x.z2)) = _
  rw [plane_muS_pairing]
  rfl

private theorem chart_UV (x : ExplicitFrameChart K) :
    normalizedUV x.s1 x.s2 x.c1 x.c2 = exteriorQ (matrixM x) -
      (deltaX x.s1 x.s2 x.c1 x.c2 +
        deltaStarA x.s1 x.s2 x.c1 x.c2) := by
  have h := normalizedUV_exterior_identity x.s1 x.s2 x.c1 x.c2
  change normalizedUV x.s1 x.s2 x.c1 x.c2 = exteriorQ (matrixM x) -
    deltaX x.s1 x.s2 x.c1 x.c2 - deltaStarA x.s1 x.s2 x.c1 x.c2 at h
  rw [h]
  ring

/-- Equality counterpart of `chart_power_diagonal_mem`: equal retained gauge
coordinates, moment matrices, and symmetric root sums give all 27 literal
power-product diagonal equalities.-/
private theorem power_diagonal_eq_of_chart_data
    (x y : ExplicitFrameChart K)
    (hda : ∀ i, y.diagA i = x.diagA i)
    (hdb : ∀ i, y.diagB i = x.diagB i)
    (hr1 : y.r1 = x.r1) (hz1 : y.z1 = x.z1)
    (hr2 : y.r2 = x.r2) (hz2 : y.z2 = x.z2)
    (hM : matrixM y = matrixM x)
    (hroot : deltaX y.s1 y.s2 y.c1 y.c2 +
        deltaStarA y.s1 y.s2 y.c1 y.c2 =
      deltaX x.s1 x.s2 x.c1 x.c2 + deltaStarA x.s1 x.s2 x.c1 x.c2) :
    ∀ i p q, diagLinear i
        (sourceProduct (power (encoderA y) p) (power (encoderB y) q)) =
      diagLinear i
        (sourceProduct (power (encoderA x) p) (power (encoderB x) q)) := by
  have hMij (i j : Fin 4) : matrixM y i j = matrixM x i j :=
    congrFun (congrFun hM i) j
  have hnS1 : nS y.s1 = nS x.s1 := by
    rw [chart_normS1 y, chart_normS1 x, hMij 0 0]
  have hnS2 : nS y.s2 = nS x.s2 := by
    rw [chart_normS2 y, chart_normS2 x, hMij 1 1]
  have hnC1 : nC y.c1 = nC x.c1 := by
    rw [chart_normC1 y, chart_normC1 x, hMij 2 2]
  have hnC2 : nC y.c2 = nC x.c2 := by
    rw [chart_normC2 y, chart_normC2 x, hMij 3 3]
  have hnVA : nV (vectorA y) = nV (vectorA x) := by
    rw [chart_normVA y, chart_normVA x, hr1, hz1]
  have hnVB : nV (vectorB y) = nV (vectorB x) := by
    rw [chart_normVB y, chart_normVB x, hr2, hz2]
  have hV : BV (vectorA y) (vectorB y) =
      BV (vectorA x) (vectorB x) := by
    rw [chart_gramV y, chart_gramV x, hr1, hz1, hr2, hz2]
  have hS : BS y.s1 y.s2 = BS x.s1 x.s2 := by
    rw [chart_gramS y, chart_gramS x, hMij 0 1, hMij 1 0]
  have hC : BC y.c1 y.c2 = BC x.c1 x.c2 := by
    rw [chart_gramC y, chart_gramC x, hMij 2 3, hMij 3 2]
  have htA1C2 : triality (vectorA y) y.s1 y.c2 =
      triality (vectorA x) x.s1 x.c2 := by
    rw [chart_trialityA1C2 y, chart_trialityA1C2 x,
      hr1, hz1, hMij 0 3, hMij 3 0]
  have htA2C1 : triality (vectorA y) y.s2 y.c1 =
      triality (vectorA x) x.s2 x.c1 := by
    rw [chart_trialityA2C1 y, chart_trialityA2C1 x,
      hr1, hz1, hMij 1 2, hMij 2 1]
  have htA2C2 : triality (vectorA y) y.s2 y.c2 =
      triality (vectorA x) x.s2 x.c2 := by
    rw [chart_trialityA2C2 y, chart_trialityA2C2 x,
      hr1, hz1, hMij 1 3, hMij 3 1]
  have htB1C2 : triality (vectorB y) y.s1 y.c2 =
      triality (vectorB x) x.s1 x.c2 := by
    rw [chart_trialityB1C2 y, chart_trialityB1C2 x,
      hr2, hz2, hMij 0 3, hMij 3 0]
  have htB2C1 : triality (vectorB y) y.s2 y.c1 =
      triality (vectorB x) x.s2 x.c1 := by
    rw [chart_trialityB2C1 y, chart_trialityB2C1 x,
      hr2, hz2, hMij 1 2, hMij 2 1]
  have htB1C1 : triality (vectorB y) y.s1 y.c1 =
      triality (vectorB x) x.s1 x.c1 := by
    rw [chart_trialityB1C1 y, chart_trialityB1C1 x,
      hr2, hz2, hMij 0 2, hMij 2 0]
  have hUC : BC (sourceMuC (vectorA y) y.s1)
      (sourceMuC (vectorB y) y.s2) =
      BC (sourceMuC (vectorA x) x.s1) (sourceMuC (vectorB x) x.s2) := by
    rw [chart_UC y, chart_UC x, hr1, hz1, hr2, hz2,
      hMij 0 1, hMij 1 0]
  have hUS : BS (sourceMuS y.c1 (vectorA y))
      (sourceMuS y.c2 (vectorB y)) =
      BS (sourceMuS x.c1 (vectorA x)) (sourceMuS x.c2 (vectorB x)) := by
    rw [chart_US y, chart_US x, hr1, hz1, hr2, hz2,
      hMij 2 3, hMij 3 2]
  have hUV : normalizedUV y.s1 y.s2 y.c1 y.c2 =
      normalizedUV x.s1 x.s2 x.c1 x.c2 := by
    rw [chart_UV y, chart_UV x, hM, hroot]
  have hdiagA : ∀ p i,
      diagLinear i (power (encoderA y) p) =
        diagLinear i (power (encoderA x) p) := by
    intro p i
    fin_cases p <;> fin_cases i <;>
      simp only [fin3_mk_zero_eq_zero, fin3_mk_one_eq_one, fin3_mk_two_eq_two] <;>
      simp only [power, encoderA, sourceOne, diagLinear_zero, diagLinear_one,
        diagLinear_two, sourceSquare_d1, sourceSquare_d2, sourceSquare_d3,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] <;>
      simp only [hda, hnS1, hnC1, hnVA]
  have hdiagB : ∀ q i,
      diagLinear i (power (encoderB y) q) =
        diagLinear i (power (encoderB x) q) := by
    intro q i
    fin_cases q <;> fin_cases i <;>
      simp only [fin3_mk_zero_eq_zero, fin3_mk_one_eq_one, fin3_mk_two_eq_two] <;>
      simp only [power, encoderB, sourceOne, diagLinear_zero, diagLinear_one,
        diagLinear_two, sourceSquare_d1, sourceSquare_d2, sourceSquare_d3,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] <;>
      simp only [hdb, hnS2, hnC2, hnVB]
  have hV21 : BV (normalizedMuV y.s1 y.c1) (vectorB y) =
      BV (normalizedMuV x.s1 x.c1) (vectorB x) := by
    rw [muV_triality, muV_triality, htB1C1]
  have hS21 : BS (sourceMuS y.c1 (vectorA y)) y.s2 =
      BS (sourceMuS x.c1 (vectorA x)) x.s2 := by
    rw [muS_triality, muS_triality, htA2C1]
  have hC21 : BC (sourceMuC (vectorA y) y.s1) y.c2 =
      BC (sourceMuC (vectorA x) x.s1) x.c2 := by
    rw [muC_triality, muC_triality, htA1C2]
  have hV12 : BV (vectorA y) (normalizedMuV y.s2 y.c2) =
      BV (vectorA x) (normalizedMuV x.s2 x.c2) := by
    rw [BV_symmetric (vectorA y) (normalizedMuV y.s2 y.c2),
      BV_symmetric (vectorA x) (normalizedMuV x.s2 x.c2),
      muV_triality, muV_triality, htA2C2]
  have hS12 : BS y.s1 (sourceMuS y.c2 (vectorB y)) =
      BS x.s1 (sourceMuS x.c2 (vectorB x)) := by
    rw [BS_symmetric y.s1 (sourceMuS y.c2 (vectorB y)),
      BS_symmetric x.s1 (sourceMuS x.c2 (vectorB x)),
      muS_triality, muS_triality, htB1C2]
  have hC12 : BC y.c1 (sourceMuC (vectorB y) y.s2) =
      BC x.c1 (sourceMuC (vectorB x) x.s2) := by
    rw [BC_symmetric y.c1 (sourceMuC (vectorB y) y.s2),
      BC_symmetric x.c1 (sourceMuC (vectorB x) x.s2),
      muC_triality, muC_triality, htB2C1]
  have hUVraw : BV (normalizedMuV y.s1 y.c1) (normalizedMuV y.s2 y.c2) =
      BV (normalizedMuV x.s1 x.c1) (normalizedMuV x.s2 x.c2) := hUV
  have h11 :
      BV (encoderA y).v (encoderB y).v = BV (encoderA x).v (encoderB x).v ∧
      BS (encoderA y).s (encoderB y).s = BS (encoderA x).s (encoderB x).s ∧
      BC (encoderA y).c (encoderB y).c = BC (encoderA x).c (encoderB x).c := by
    simpa only [encoderA, encoderB] using And.intro hV (And.intro hS hC)
  have h21 :
      BV (sourceSquare (encoderA y)).v (encoderB y).v =
          BV (sourceSquare (encoderA x)).v (encoderB x).v ∧
      BS (sourceSquare (encoderA y)).s (encoderB y).s =
          BS (sourceSquare (encoderA x)).s (encoderB x).s ∧
      BC (sourceSquare (encoderA y)).c (encoderB y).c =
          BC (sourceSquare (encoderA x)).c (encoderB x).c := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [sourceSquare_v, BV_add_left, BV_smul_left, encoderA, encoderB]
      rw [hda 1, hda 2, hV, hV21]
    · simp only [sourceSquare_s, BS_add_left, BS_smul_left, encoderA, encoderB]
      rw [hda 0, hda 2, hS, hS21]
    · simp only [sourceSquare_c, BC_add_left, BC_smul_left, encoderA, encoderB]
      rw [hda 0, hda 1, hC, hC21]
  have h12 :
      BV (encoderA y).v (sourceSquare (encoderB y)).v =
          BV (encoderA x).v (sourceSquare (encoderB x)).v ∧
      BS (encoderA y).s (sourceSquare (encoderB y)).s =
          BS (encoderA x).s (sourceSquare (encoderB x)).s ∧
      BC (encoderA y).c (sourceSquare (encoderB y)).c =
          BC (encoderA x).c (sourceSquare (encoderB x)).c := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [sourceSquare_v, BV_add_right, BV_smul_right, encoderA, encoderB]
      rw [hdb 1, hdb 2, hV, hV12]
    · simp only [sourceSquare_s, BS_add_right, BS_smul_right, encoderA, encoderB]
      rw [hdb 0, hdb 2, hS, hS12]
    · simp only [sourceSquare_c, BC_add_right, BC_smul_right, encoderA, encoderB]
      rw [hdb 0, hdb 1, hC, hC12]
  have h22 :
      BV (sourceSquare (encoderA y)).v (sourceSquare (encoderB y)).v =
          BV (sourceSquare (encoderA x)).v (sourceSquare (encoderB x)).v ∧
      BS (sourceSquare (encoderA y)).s (sourceSquare (encoderB y)).s =
          BS (sourceSquare (encoderA x)).s (sourceSquare (encoderB x)).s ∧
      BC (sourceSquare (encoderA y)).c (sourceSquare (encoderB y)).c =
          BC (sourceSquare (encoderA x)).c (sourceSquare (encoderB x)).c := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [sourceSquare_v, BV_add_left, BV_add_right, BV_smul_left,
        BV_smul_right, encoderA, encoderB]
      simp only [hda, hdb, hV, hV12, hV21, hUVraw]
    · simp only [sourceSquare_s, BS_add_left, BS_add_right, BS_smul_left,
        BS_smul_right, encoderA, encoderB]
      simp only [hda, hdb, hS, hS12, hS21, hUS]
    · simp only [sourceSquare_c, BC_add_left, BC_add_right, BC_smul_left,
        BC_smul_right, encoderA, encoderB]
      simp only [hda, hdb, hC, hC12, hC21, hUC]
  have hsector : ∀ p q,
      BV (power (encoderA y) p).v (power (encoderB y) q).v =
          BV (power (encoderA x) p).v (power (encoderB x) q).v ∧
      BS (power (encoderA y) p).s (power (encoderB y) q).s =
          BS (power (encoderA x) p).s (power (encoderB x) q).s ∧
      BC (power (encoderA y) p).c (power (encoderB y) q).c =
          BC (power (encoderA x) p).c (power (encoderB x) q).c := by
    intro p q
    fin_cases p <;> fin_cases q
    all_goals first
      | exact h11 | exact h12 | exact h21 | exact h22
      | simp [power, sourceOne, BV, BS, BC, BW, evalU]
  intro i p q
  have hs := hsector p q
  fin_cases i
  · simp only [fin3_mk_zero_eq_zero, diagLinear_zero, sourceProduct_d1]
    rw [show (power (encoderA y) p).d1 = (power (encoderA x) p).d1 from hdiagA p 0,
      show (power (encoderB y) q).d1 = (power (encoderB x) q).d1 from hdiagB q 0,
      hs.2.1, hs.2.2]
  · simp only [fin3_mk_one_eq_one, diagLinear_one, sourceProduct_d2]
    rw [show (power (encoderA y) p).d2 = (power (encoderA x) p).d2 from hdiagA p 1,
      show (power (encoderB y) q).d2 = (power (encoderB x) q).d2 from hdiagB q 1,
      hs.2.2, hs.1]
  · simp only [fin3_mk_two_eq_two, diagLinear_two, sourceProduct_d3]
    rw [show (power (encoderA y) p).d3 = (power (encoderA x) p).d3 from hdiagA p 2,
      show (power (encoderB y) q).d3 = (power (encoderB x) q).d3 from hdiagB q 2,
      hs.1, hs.2.1]

/-- Finite chart identity: the 27 power-product diagonals depend only on the
retained chart fields, the residual moment, and the symmetric determinant-root
sum.  The proof deliberately splits the finite indices rather than inferring
point equality from a generated-field equality.
@isnad1 id=eq.1h6v.s8.fed28b7956f3 from=translated src=- shape=75877a05 vocab=5c30ed0b
-/
theorem power_diagonal_reinsert_of_sameResidualBase
    (x : ExplicitFrameChart K) (Q : ResidualPair K)
    (hQ : sameResidualBase (residualPairOfChart x) Q) (i p q : Fin 3) :
    diagLinear i
        (sourceProduct (power (encoderA (chartWithResidualPair x Q)) p)
          (power (encoderB (chartWithResidualPair x Q)) q)) =
      diagLinear i
        (sourceProduct (power (encoderA x) p) (power (encoderB x) q)) := by
  have hM : matrixM (chartWithResidualPair x Q) = matrixM x := by
    rw [matrixM_eq_moment, residualPairOfChart_chartWithResidualPair, matrixM_eq_moment]
    simpa only [baseMoment] using hQ.1
  have hroot :
      deltaX (chartWithResidualPair x Q).s1 (chartWithResidualPair x Q).s2
          (chartWithResidualPair x Q).c1 (chartWithResidualPair x Q).c2 +
        deltaStarA (chartWithResidualPair x Q).s1 (chartWithResidualPair x Q).s2
          (chartWithResidualPair x Q).c1 (chartWithResidualPair x Q).c2 =
      deltaX x.s1 x.s2 x.c1 x.c2 + deltaStarA x.s1 x.s2 x.c1 x.c2 := by
    simp only [deltaX_eq_det_XMatrix, deltaStarA_eq_det_AMatrix]
    change delta (residualPairOfChart (chartWithResidualPair x Q)) +
        deltaStar (residualPairOfChart (chartWithResidualPair x Q)) =
      delta (residualPairOfChart x) + deltaStar (residualPairOfChart x)
    rw [residualPairOfChart_chartWithResidualPair]
    exact hQ.2
  exact power_diagonal_eq_of_chart_data x (chartWithResidualPair x Q)
    (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl hM hroot i p q

def companion (x : ExplicitFrameChart K)
    (hx : ResidualOpen (residualPairOfChart x)) : ExplicitFrameChart K :=
  chartWithResidualPair x
    (rootSwappedRepresentative (residualPairOfChart x) hx)

/-- The actual root-swapped chart preserves both the six raw frame equations
and every literal cell of the source 54-ledger.
@isnad1 id=and.1h2v.s6.21a832f45b48 from=translated src=- shape=582c4d21 vocab=18120e77
-/
theorem companion_equations_and_sourceLedger
    (x : ExplicitFrameChart K)
    (hx : ResidualOpen (residualPairOfChart x)) :
    explicitFrameEquationValues (companion x hx) =
        explicitFrameEquationValues x ∧
      sourceLedger (encoderA (companion x hx)) (encoderB (companion x hx)) =
        sourceLedger (encoderA x) (encoderB x) := by
  let Q := rootSwappedRepresentative (residualPairOfChart x) hx
  have hbase : sameResidualBase (residualPairOfChart x) Q :=
    ⟨by simpa [Q, baseMoment] using
        (rootSwappedRepresentative_baseMoment (residualPairOfChart x) hx),
      by simpa [Q] using
        (rootSwappedRepresentative_baseRootSum (residualPairOfChart x) hx)⟩
  constructor
  · exact equationValues_reinsert_of_moment_eq x Q hbase.1
  · apply sourceLedger_eq_of_power_diagonal_eq
    intro i p q
    exact power_diagonal_reinsert_of_sameResidualBase x Q hbase i p q

end AlbertLean.Generic.AlbertActualCompanion
