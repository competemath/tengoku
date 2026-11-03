import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualLedgerMomentField
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ProjectorSector

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms ledgerField_eq_chartField` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ledgerIn_of_chart_data` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms kappa_mem_of_lift` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Reverse dictionary for the explicit residual chart.

The effective chart field contains the six diagonal coefficients, the four
hyperbolic-plane gauge coefficients, all sixteen entries of `M`, and the
symmetric determinant-root sum.  `kappa` is deliberately not a generator:
it does not occur in either encoder.  Under `IsKappaLift`, it is already in
the gauge field because it equals the polynomial `orientation x`.

There is no coverage, fixed-field, genericity, or common-fixed hypothesis.
-/

noncomputable section
namespace AlbertLean.Generic.ResidualLiteralLedgerDictionary

open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Residual.TrialitySquares
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Generic.ProductDiagonal
open AlbertLean.Generic.ResidualLedgerPower
open AlbertLean.Generic.ResidualPowerMeasurements
open AlbertLean.Generic.ResidualMomentSubfield
open AlbertLean.Generic.ResidualLedgerMomentField
open AlbertLean.Generic.ResidualSourceMeasurements

variable {K : Type*} [Field K] [CharZero K]

/-- Exactly the coefficients which occur in the two chart encoders.-/
def CoefficientsIn (F : Subfield K) (x : ExplicitFrameChart K) : Prop :=
  (∀ i, x.diagA i ∈ F) ∧ (∀ i, x.diagB i ∈ F) ∧
  x.r1 ∈ F ∧ x.z1 ∈ F ∧ x.r2 ∈ F ∧ x.z2 ∈ F

/-- The residual coordinates retained by the literal reverse dictionary.
The two within-sector Gram sums are present because all sixteen `M` entries
are present; in particular this is not the abbreviated paper list.-/
def ResidualDataIn (F : Subfield K) (x : ExplicitFrameChart K) : Prop :=
  (∀ i j, matrixM x i j ∈ F) ∧
  deltaX x.s1 x.s2 x.c1 x.c2 + deltaStarA x.s1 x.s2 x.c1 x.c2 ∈ F

/-- Algebraic heart of the reverse direction.  This is intentionally phrased
at the 27 diagonal power-products, so the already checked projector/centering
dictionary can be reused verbatim.

Proof recipe (all identities are definitional or already checked): split the
27 cases.  The `(1,1)` sector uses the V gauge Gram and the two full S/C Gram
sums `M01+M10`, `M23+M32`.  The `(1,2)` and `(2,1)` sectors use the eight
gauge-weighted cross entries.  The `(2,2)` S/C sectors use the two normalized
adjoint pairings, and its V sector uses
`normalizedUV_exterior_identity`, hence `exteriorQ M - (deltaX+deltaStarA)`.
@isnad1 id=mem.2h6v.s8.886d3bf40312 from=translated src=- shape=6f9f4ecc vocab=4deb2d76
-/
theorem chart_power_diagonal_mem (F : Subfield K) (x : ExplicitFrameChart K)
    (hc : CoefficientsIn F x) (hr : ResidualDataIn F x) :
    ∀ i p q, diagLinear i
      (sourceProduct (power (encoderA x) p) (power (encoderB x) q)) ∈ F := by
  rcases hc with ⟨hda, hdb, hr1, hz1, hr2, hz2⟩
  rcases hr with ⟨hM, hroot⟩
  have hq : exteriorQ (matrixM x) ∈ F := exteriorQ_mem F _ hM
  have huv : normalizedUV x.s1 x.s2 x.c1 x.c2 ∈ F := by
    have heq := normalizedUV_exterior_identity x.s1 x.s2 x.c1 x.c2
    change normalizedUV x.s1 x.s2 x.c1 x.c2 = exteriorQ (matrixM x) -
      deltaX x.s1 x.s2 x.c1 x.c2 - deltaStarA x.s1 x.s2 x.c1 x.c2 at heq
    have hh : exteriorQ (matrixM x) -
        (deltaX x.s1 x.s2 x.c1 x.c2 + deltaStarA x.s1 x.s2 x.c1 x.c2) ∈ F :=
      F.sub_mem hq hroot
    rw [heq]
    convert hh using 1 <;> ring
  have hnS1 : nS x.s1 ∈ F := by
    simpa [matrixM, momentMatrix, nS] using hM 0 0
  have hnS2 : nS x.s2 ∈ F := by
    simpa [matrixM, momentMatrix, nS] using hM 1 1
  have hnC1 : nC x.c1 ∈ F := by
    simpa [matrixM, momentMatrix, nC] using hM 2 2
  have hnC2 : nC x.c2 ∈ F := by
    simpa [matrixM, momentMatrix, nC] using hM 3 3
  have hnV1 : nV (vectorA x) ∈ F := by
    simp [nV, vectorA, Pf, BW]
    exact F.mul_mem hr1 hz1
  have hnV2 : nV (vectorB x) ∈ F := by
    simp [nV, vectorB, Pf, BW]
    exact F.mul_mem hr2 hz2
  have hdiagA : ∀ p, DiagIn F (power (encoderA x) p) := by
    intro p i
    fin_cases p <;> fin_cases i <;>
      simp only [power, encoderA, sourceOne, diagLinear_zero, diagLinear_one,
        diagLinear_two, sourceSquare_d1, sourceSquare_d2, sourceSquare_d3,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        vectorA, nV, nS, nC, BW, Pf, matrixM, momentMatrix] <;>
      aesop (add safe apply [F.add_mem, F.mul_mem, F.pow_mem, F.one_mem,
        F.zero_mem])
  have hdiagB : ∀ q, DiagIn F (power (encoderB x) q) := by
    intro q i
    fin_cases q <;> fin_cases i <;>
      simp only [power, encoderB, sourceOne, diagLinear_zero, diagLinear_one,
        diagLinear_two, sourceSquare_d1, sourceSquare_d2, sourceSquare_d3,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        vectorB, nV, nS, nC, BW, Pf, matrixM, momentMatrix] <;>
      aesop (add safe apply [F.add_mem, F.mul_mem, F.pow_mem, F.one_mem,
        F.zero_mem])
  have hV : BV (vectorA x) (vectorB x) ∈ F := by
    simp [BV, BW, vectorA, vectorB]
    exact F.add_mem (F.mul_mem hr1 hz2) (F.mul_mem hz1 hr2)
  have hS : BS x.s1 x.s2 ∈ F := by
    change matrixM x 0 1 + matrixM x 1 0 ∈ F
    exact F.add_mem (hM 0 1) (hM 1 0)
  have hC : BC x.c1 x.c2 ∈ F := by
    change matrixM x 2 3 + matrixM x 3 2 ∈ F
    exact F.add_mem (hM 2 3) (hM 3 2)
  have htA1C2 : triality (vectorA x) x.s1 x.c2 ∈ F := by
    rw [show vectorA x = planeVector x.r1 x.z1 by rfl, plane_triality]
    change x.r1 * matrixM x 0 3 + x.z1 * matrixM x 3 0 ∈ F
    exact F.add_mem (F.mul_mem hr1 (hM 0 3)) (F.mul_mem hz1 (hM 3 0))
  have htA2C1 : triality (vectorA x) x.s2 x.c1 ∈ F := by
    rw [show vectorA x = planeVector x.r1 x.z1 by rfl, plane_triality]
    change x.r1 * matrixM x 1 2 + x.z1 * matrixM x 2 1 ∈ F
    exact F.add_mem (F.mul_mem hr1 (hM 1 2)) (F.mul_mem hz1 (hM 2 1))
  have htB1C2 : triality (vectorB x) x.s1 x.c2 ∈ F := by
    rw [show vectorB x = planeVector x.r2 x.z2 by rfl, plane_triality]
    change x.r2 * matrixM x 0 3 + x.z2 * matrixM x 3 0 ∈ F
    exact F.add_mem (F.mul_mem hr2 (hM 0 3)) (F.mul_mem hz2 (hM 3 0))
  have htB2C1 : triality (vectorB x) x.s2 x.c1 ∈ F := by
    rw [show vectorB x = planeVector x.r2 x.z2 by rfl, plane_triality]
    change x.r2 * matrixM x 1 2 + x.z2 * matrixM x 2 1 ∈ F
    exact F.add_mem (F.mul_mem hr2 (hM 1 2)) (F.mul_mem hz2 (hM 2 1))
  have htA2C2 : triality (vectorA x) x.s2 x.c2 ∈ F := by
    rw [show vectorA x = planeVector x.r1 x.z1 by rfl, plane_triality]
    change x.r1 * matrixM x 1 3 + x.z1 * matrixM x 3 1 ∈ F
    exact F.add_mem (F.mul_mem hr1 (hM 1 3)) (F.mul_mem hz1 (hM 3 1))
  have htB1C1 : triality (vectorB x) x.s1 x.c1 ∈ F := by
    rw [show vectorB x = planeVector x.r2 x.z2 by rfl, plane_triality]
    change x.r2 * matrixM x 0 2 + x.z2 * matrixM x 2 0 ∈ F
    exact F.add_mem (F.mul_mem hr2 (hM 0 2)) (F.mul_mem hz2 (hM 2 0))
  have hUC : BC (sourceMuC (vectorA x) x.s1)
      (sourceMuC (vectorB x) x.s2) ∈ F := by
    change BC (sourceMuC (planeVector x.r1 x.z1) x.s1)
      (sourceMuC (planeVector x.r2 x.z2) x.s2) ∈ F
    rw [plane_muC_pairing]
    change x.r1 * x.z2 * matrixM x 0 1 + x.r2 * x.z1 * matrixM x 1 0 ∈ F
    exact F.add_mem (F.mul_mem (F.mul_mem hr1 hz2) (hM 0 1))
      (F.mul_mem (F.mul_mem hr2 hz1) (hM 1 0))
  have hUS : BS (sourceMuS x.c1 (vectorA x))
      (sourceMuS x.c2 (vectorB x)) ∈ F := by
    change BS (sourceMuS x.c1 (planeVector x.r1 x.z1))
      (sourceMuS x.c2 (planeVector x.r2 x.z2)) ∈ F
    rw [plane_muS_pairing]
    change x.r2 * x.z1 * matrixM x 2 3 + x.r1 * x.z2 * matrixM x 3 2 ∈ F
    exact F.add_mem (F.mul_mem (F.mul_mem hr2 hz1) (hM 2 3))
      (F.mul_mem (F.mul_mem hr1 hz2) (hM 3 2))
  have hlVa : x.diagA 1 + x.diagA 2 ∈ F := F.add_mem (hda 1) (hda 2)
  have hlSa : x.diagA 0 + x.diagA 2 ∈ F := F.add_mem (hda 0) (hda 2)
  have hlCa : x.diagA 0 + x.diagA 1 ∈ F := F.add_mem (hda 0) (hda 1)
  have hlVb : x.diagB 1 + x.diagB 2 ∈ F := F.add_mem (hdb 1) (hdb 2)
  have hlSb : x.diagB 0 + x.diagB 2 ∈ F := F.add_mem (hdb 0) (hdb 2)
  have hlCb : x.diagB 0 + x.diagB 1 ∈ F := F.add_mem (hdb 0) (hdb 1)
  have ha2b : SectorIn F (sourceSquare (encoderA x)) (encoderB x) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [sourceSquare_v, BV_add_left, BV_smul_left, muV_triality]
      simp only [encoderA, encoderB]
      exact F.add_mem (F.mul_mem hlVa hV) htB1C1
    · rw [sourceSquare_s, BS_add_left, BS_smul_left, muS_triality]
      simp only [encoderA, encoderB]
      exact F.add_mem (F.mul_mem hlSa hS) htA2C1
    · rw [sourceSquare_c, BC_add_left, BC_smul_left, muC_triality]
      simp only [encoderA, encoderB]
      exact F.add_mem (F.mul_mem hlCa hC) htA1C2
  have hab2 : SectorIn F (encoderA x) (sourceSquare (encoderB x)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [sourceSquare_v, BV_add_right, BV_smul_right]
      simp only [encoderA, encoderB]
      rw [
        BV_symmetric (vectorA x) (normalizedMuV x.s2 x.c2), muV_triality]
      exact F.add_mem (F.mul_mem hlVb hV) htA2C2
    · rw [sourceSquare_s, BS_add_right, BS_smul_right]
      simp only [encoderA, encoderB]
      rw [
        BS_symmetric x.s1 (sourceMuS x.c2 (vectorB x)), muS_triality]
      exact F.add_mem (F.mul_mem hlSb hS) htB1C2
    · rw [sourceSquare_c, BC_add_right, BC_smul_right]
      simp only [encoderA, encoderB]
      rw [
        BC_symmetric x.c1 (sourceMuC (vectorB x) x.s2), muC_triality]
      exact F.add_mem (F.mul_mem hlCb hC) htB2C1
  have ha2b2 : SectorIn F (sourceSquare (encoderA x))
      (sourceSquare (encoderB x)) := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [sourceSquare_v, BV_add_left, BV_add_right, BV_smul_left,
        BV_smul_right, normalizedUV, encoderA, encoderB]
      rw [BV_symmetric (vectorA x) (normalizedMuV x.s2 x.c2),
        muV_triality, muV_triality]
      aesop (add safe apply [F.add_mem, F.mul_mem])
    · simp only [sourceSquare_s, BS_add_left, BS_add_right, BS_smul_left,
        BS_smul_right, encoderA, encoderB]
      rw [BS_symmetric x.s1 (sourceMuS x.c2 (vectorB x)),
        muS_triality, muS_triality]
      aesop (add safe apply [F.add_mem, F.mul_mem])
    · simp only [sourceSquare_c, BC_add_left, BC_add_right, BC_smul_left,
        BC_smul_right, encoderA, encoderB]
      rw [BC_symmetric x.c1 (sourceMuC (vectorB x) x.s2),
        muC_triality, muC_triality]
      aesop (add safe apply [F.add_mem, F.mul_mem])
  have hab : SectorIn F (encoderA x) (encoderB x) := ⟨hV, hS, hC⟩
  have hsector : ∀ p q,
      SectorIn F (power (encoderA x) p) (power (encoderB x) q) := by
    intro p q
    fin_cases p <;> fin_cases q
    all_goals first
      | exact hab | exact hab2 | exact ha2b | exact ha2b2
      | simp [SectorIn, power, sourceOne, BV, BS, BC, BW, evalU]
  intro i p q
  have hpair := hsector p q
  fin_cases i <;> simp only [Fin.isValue, Function.comp_apply]
  · change (sourceProduct (power (encoderA x) p) (power (encoderB x) q)).d1 ∈ F
    rw [sourceProduct_d1]
    exact F.add_mem (F.mul_mem (hdiagA p 0) (hdiagB q 0))
      (F.div_mem (F.add_mem hpair.2.1 hpair.2.2) (natCast_mem F 2))
  · change (sourceProduct (power (encoderA x) p) (power (encoderB x) q)).d2 ∈ F
    rw [sourceProduct_d2]
    exact F.add_mem (F.mul_mem (hdiagA p 1) (hdiagB q 1))
      (F.div_mem (F.add_mem hpair.2.2 hpair.1) (natCast_mem F 2))
  · change (sourceProduct (power (encoderA x) p) (power (encoderB x) q)).d3 ∈ F
    rw [sourceProduct_d3]
    exact F.add_mem (F.mul_mem (hdiagA p 2) (hdiagB q 2))
      (F.div_mem (F.add_mem hpair.1 hpair.2.1) (natCast_mem F 2))

/-- All 54 actual source-ledger cells lie in any subfield containing the
effective chart data.  Centering is supplied only by
`ledgerIn_of_power_diagonal_mem`; it is not re-expanded here.
@isnad1 id=ledgerin.2h3v.s5.2b81362e7a41 from=translated src=- shape=3e01808e vocab=ace7144c
-/
theorem ledgerIn_of_chart_data (F : Subfield K) (x : ExplicitFrameChart K)
    (hc : CoefficientsIn F x) (hr : ResidualDataIn F x) :
    LedgerIn F (sourceLedger (encoderA x) (encoderB x)) :=
  ledgerIn_of_power_diagonal_mem F _ _ (chart_power_diagonal_mem F x hc hr)

def chartCells (x : ExplicitFrameChart K) : Set K :=
  Set.range x.diagA ∪ Set.range x.diagB ∪
  Set.range (fun ij : Fin 4 × Fin 4 => matrixM x ij.1 ij.2) ∪
  {deltaX x.s1 x.s2 x.c1 x.c2 + deltaStarA x.s1 x.s2 x.c1 x.c2}

def chartField (base : Subfield K) (x : ExplicitFrameChart K) : Subfield K :=
  Subfield.closure ((base : Set K) ∪ chartCells x)

/-- Exact generated-field equality on the explicit chart.  The forward
containment is the checked inverse `residual_moments_mem_ledgerField`, plus
the diagonal power measurements.  The reverse containment is the theorem
above.  The four gauge coefficients must be in `base`; no orientation-open
or norm equation is concealed.
@isnad1 id=eq.7h3v.s7.07dde92c6904 from=translated src=- shape=878e06a6 vocab=3a02b016
-/
theorem ledgerField_eq_chartField (base : Subfield K) (x : ExplicitFrameChart K)
    (hr1 : x.r1 ∈ base) (hz1 : x.z1 ∈ base)
    (hr2 : x.r2 ∈ base) (hz2 : x.z2 ∈ base)
    (hk : orientation x ≠ 0)
    (hNa : sourceNorm (encoderA x) = 0)
    (hNb : sourceNorm (encoderB x) = 0) :
    ledgerField base (encoderA x) (encoderB x) = chartField base x := by
  let L := ledgerField base (encoderA x) (encoderB x)
  have hInv := residual_moments_mem_ledgerField base x hr1 hz1 hr2 hz2 hk hNa hNb
  have hPow := powers_diag_mem L _ _ (ledgerIn_ledgerField base _ _)
  have hdiagA : ∀ i, x.diagA i ∈ L := by
    intro i
    fin_cases i
    · simpa [L, power, encoderA] using hPow.1 1 0
    · simpa [L, power, encoderA] using hPow.1 1 1
    · simpa [L, power, encoderA] using hPow.1 1 2
  have hdiagB : ∀ i, x.diagB i ∈ L := by
    intro i
    fin_cases i
    · simpa [L, power, encoderB] using hPow.2 1 0
    · simpa [L, power, encoderB] using hPow.2 1 1
    · simpa [L, power, encoderB] using hPow.2 1 2
  apply le_antisymm
  · apply Subfield.closure_le.2
    rintro t (ht | ht)
    · exact Subfield.subset_closure (Or.inl ht)
    · exact (ledgerCells_subset_iff (chartField base x) _ _).2
        (ledgerIn_of_chart_data (chartField base x) x
          ⟨(fun i => Subfield.subset_closure
              (Or.inr (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))))),
           (fun i => Subfield.subset_closure
              (Or.inr (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))),
           Subfield.subset_closure (Or.inl hr1), Subfield.subset_closure (Or.inl hz1),
           Subfield.subset_closure (Or.inl hr2), Subfield.subset_closure (Or.inl hz2)⟩
          ⟨(fun i j => Subfield.subset_closure
              (Or.inr (Or.inl (Or.inr ⟨(i,j), rfl⟩)))),
           Subfield.subset_closure (Or.inr (Or.inr (by rfl)))⟩) ht
  · apply Subfield.closure_le.2
    rintro t (ht | ht)
    · exact Subfield.subset_closure (Or.inl ht)
    · rcases ht with ((ht | ht) | ht) | ht
      · rcases ht with ⟨i, rfl⟩; exact hdiagA i
      · rcases ht with ⟨i, rfl⟩; exact hdiagB i
      · rcases ht with ⟨⟨i,j⟩, rfl⟩; exact hInv.1 i j
      · rcases ht with rfl; exact hInv.2

/--
@isnad1 id=mem.2h3v.s6.4acee3d6b949 from=translated src=- shape=cba6168f vocab=45081257
-/
theorem kappa_mem_of_lift (F : Subfield K) (x : ExplicitFrameChart K)
    (hc : CoefficientsIn F x) (hlift : IsKappaLift x) : x.kappa ∈ F := by
  rcases hc with ⟨_, _, hr1, hz1, hr2, hz2⟩
  rw [← hlift]
  exact F.sub_mem (F.mul_mem hr1 hz2) (F.mul_mem hr2 hz1)

end AlbertLean.Generic.ResidualLiteralLedgerDictionary
