import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericFieldSymmetries
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericMeasurementSymmetry
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.MeasurementLedgerConverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms ledgerIn_nuFixed` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms H_le_nuFixed` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms deck_fixed_of_mem_H` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms tau_fixed_of_mem_H` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms kappa_not_mem_H` (it only prints; the queue checks the axioms of every declaration). -/

/-! Literal-ledger invariance under the concrete field reorientation.
The calculation is at scalar contractions, followed by the measurement
converse; no individual gauge coefficient is assumed invariant. -/

noncomputable section
namespace AlbertLean.Generic.GenericLedgerInvariance

open Matrix
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
open AlbertLean.Generic.ResidualLedgerMomentField
open AlbertLean.Generic.ResidualSourceMeasurements
open AlbertLean.Generic.ResidualOrientationField
open AlbertLean.Generic.GenericDeterminantOpen
open AlbertLean.Generic.GenericFieldChart
open AlbertLean.Generic.GenericLedgerFixedField
open AlbertLean.Generic.GenericOrientationAttachment
open AlbertLean.Generic.GenericReorientationBase
open AlbertLean.Generic.GenericMeasurementSymmetry
open AlbertLean.Generic.GenericFieldSymmetries
open AlbertLean.Generic.MeasurementLedgerConverse
open AlbertLean.Generic.NestedReciprocalField

universe u
variable (k : Type u) [Field k] [CharZero k]

def nuFixed : Subfield (FunctionField k) :=
  (nu k).toRingHom.eqLocusField (RingHom.id _)

def H : Subfield (FunctionField k) :=
  ledgerField (groundBase k) (encoderA (genericChart k)) (encoderB (genericChart k))

private theorem include_fixed {z : Base k} (h : reorient k z = z) :
    includeBase k z ∈ nuFixed k := by
  change nu k (includeBase k z) = includeBase k z
  rw [nu_base, h]

theorem generic_matrix (i j : Fin 4) :
    matrixM (genericChart k) i j = includeBase k (rationalM k i j) := by
  change matrixM (GenericNormalizedFrameChart.insert (genericOpen k)) i j = _
  rw [GenericNormalizedFrameChart.insert_matrixM]
  change GenericNormalizedFrameChart.moment (fieldParameters k) i j = _
  rw [fieldParameters_moment]
  rfl

/-! Rewrite source-coordinate identities on an abstract chart before
instantiating the large generic rational point. -/

section ChartIdentities
variable {K : Type*} [Field K] [CharZero K]

private theorem chart_diagA (F : Subfield K) (x : ExplicitFrameChart K)
    (h : ∀ i, x.diagA i ∈ F) : DiagIn F (encoderA x) := by
  intro i
  fin_cases i <;> exact h _

private theorem chart_diagB (F : Subfield K) (x : ExplicitFrameChart K)
    (h : ∀ i, x.diagB i ∈ F) : DiagIn F (encoderB x) := by
  intro i
  fin_cases i <;> exact h _

private theorem chart_normS1 (x : ExplicitFrameChart K) : nS x.s1 = matrixM x 0 0 := rfl
private theorem chart_normS2 (x : ExplicitFrameChart K) : nS x.s2 = matrixM x 1 1 := rfl
private theorem chart_normC1 (x : ExplicitFrameChart K) : nC x.c1 = matrixM x 2 2 := rfl
private theorem chart_normC2 (x : ExplicitFrameChart K) : nC x.c2 = matrixM x 3 3 := rfl

private theorem chart_normVA (x : ExplicitFrameChart K) : nV (vectorA x) = x.r1 * x.z1 := by
  simp [nV, vectorA, Pf, BW]

private theorem chart_normVB (x : ExplicitFrameChart K) : nV (vectorB x) = x.r2 * x.z2 := by
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
      (deltaX x.s1 x.s2 x.c1 x.c2 + deltaStarA x.s1 x.s2 x.c1 x.c2) := by
  have h := normalizedUV_exterior_identity x.s1 x.s2 x.c1 x.c2
  change normalizedUV x.s1 x.s2 x.c1 x.c2 = exteriorQ (matrixM x) -
    deltaX x.s1 x.s2 x.c1 x.c2 - deltaStarA x.s1 x.s2 x.c1 x.c2 at h
  rw [h]
  ring

private theorem chart_sector21 (F : Subfield K) (x : ExplicitFrameChart K)
    (hd : ∀ i, x.diagA i ∈ F)
    (hV : BV (vectorA x) (vectorB x) ∈ F)
    (hS : BS x.s1 x.s2 ∈ F) (hC : BC x.c1 x.c2 ∈ F)
    (hB11 : triality (vectorB x) x.s1 x.c1 ∈ F)
    (hA21 : triality (vectorA x) x.s2 x.c1 ∈ F)
    (hA12 : triality (vectorA x) x.s1 x.c2 ∈ F) :
    SectorIn F (sourceSquare (encoderA x)) (encoderB x) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sourceSquare_v, BV_add_left, BV_smul_left, muV_triality]
    exact F.add_mem (F.mul_mem (F.add_mem (hd 1) (hd 2)) hV) hB11
  · rw [sourceSquare_s, BS_add_left, BS_smul_left, muS_triality]
    exact F.add_mem (F.mul_mem (F.add_mem (hd 0) (hd 2)) hS) hA21
  · rw [sourceSquare_c, BC_add_left, BC_smul_left, muC_triality]
    exact F.add_mem (F.mul_mem (F.add_mem (hd 0) (hd 1)) hC) hA12

private theorem chart_sector12 (F : Subfield K) (x : ExplicitFrameChart K)
    (hd : ∀ i, x.diagB i ∈ F)
    (hV : BV (vectorA x) (vectorB x) ∈ F)
    (hS : BS x.s1 x.s2 ∈ F) (hC : BC x.c1 x.c2 ∈ F)
    (hA22 : triality (vectorA x) x.s2 x.c2 ∈ F)
    (hB12 : triality (vectorB x) x.s1 x.c2 ∈ F)
    (hB21 : triality (vectorB x) x.s2 x.c1 ∈ F) :
    SectorIn F (encoderA x) (sourceSquare (encoderB x)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sourceSquare_v, BV_add_right, BV_smul_right]
    simp only [encoderA, encoderB]
    rw [BV_symmetric (vectorA x) (normalizedMuV x.s2 x.c2), muV_triality]
    exact F.add_mem (F.mul_mem (F.add_mem (hd 1) (hd 2)) hV) hA22
  · rw [sourceSquare_s, BS_add_right, BS_smul_right]
    simp only [encoderA, encoderB]
    rw [BS_symmetric x.s1 (sourceMuS x.c2 (vectorB x)), muS_triality]
    exact F.add_mem (F.mul_mem (F.add_mem (hd 0) (hd 2)) hS) hB12
  · rw [sourceSquare_c, BC_add_right, BC_smul_right]
    simp only [encoderA, encoderB]
    rw [BC_symmetric x.c1 (sourceMuC (vectorB x) x.s2), muC_triality]
    exact F.add_mem (F.mul_mem (F.add_mem (hd 0) (hd 1)) hC) hB21

end ChartIdentities

/-! Each scalar calculation is checked separately; the final ledger
proof only assembles already proved measurement facts. -/

private theorem diagA_fixed : ∀ i, (genericChart k).diagA i ∈ (nuFixed k) := by
  intro i
  fin_cases i
  · exact include_fixed k (reorient_diag k 0)
  · exact include_fixed k (reorient_diag k 1)
  · change -includeBase k (ι k (diagX k 0)) - includeBase k (ι k (diagX k 1)) ∈ (nuFixed k)
    exact (nuFixed k).sub_mem ((nuFixed k).neg_mem (include_fixed k (reorient_diag k 0)))
      (include_fixed k (reorient_diag k 1))

private theorem diagB_fixed : ∀ i, (genericChart k).diagB i ∈ (nuFixed k) := by
  intro i
  fin_cases i
  · exact include_fixed k (reorient_diag k 2)
  · exact include_fixed k (reorient_diag k 3)
  · change -includeBase k (ι k (diagX k 2)) - includeBase k (ι k (diagX k 3)) ∈ (nuFixed k)
    exact (nuFixed k).sub_mem ((nuFixed k).neg_mem (include_fixed k (reorient_diag k 2)))
      (include_fixed k (reorient_diag k 3))

private theorem matrix_diagonal_fixed (i : Fin 4) : matrixM (genericChart k) i i ∈ (nuFixed k) := by
  rw [generic_matrix]
  exact include_fixed k (reorient_diagonal k i)

private theorem normS1_fixed : nS (genericChart k).s1 ∈ (nuFixed k) := by
  rw [chart_normS1]
  exact matrix_diagonal_fixed k 0

private theorem normS2_fixed : nS (genericChart k).s2 ∈ (nuFixed k) := by
  rw [chart_normS2]
  exact matrix_diagonal_fixed k 1

private theorem normC1_fixed : nC (genericChart k).c1 ∈ (nuFixed k) := by
  rw [chart_normC1]
  exact matrix_diagonal_fixed k 2

private theorem normC2_fixed : nC (genericChart k).c2 ∈ (nuFixed k) := by
  rw [chart_normC2]
  exact matrix_diagonal_fixed k 3

private theorem normV1_fixed : nV (vectorA (genericChart k)) ∈ (nuFixed k) := by
  rw [chart_normVA]
  change 1 * includeBase k (ι k (a k)) ∈ (nuFixed k)
  rw [one_mul]
  exact include_fixed k (reorient_a k)

private theorem normV2_fixed : nV (vectorB (genericChart k)) ∈ (nuFixed k) := by
  rw [chart_normVB]
  change includeBase k (ι k (b k)) * includeBase k (ι k (c k)) ∈ (nuFixed k)
  rw [← map_mul]
  exact include_fixed k (reorient_bc k)

private theorem power_diagA_fixed : ∀ p, DiagIn (nuFixed k) (power (encoderA (genericChart k)) p) :=
  power_diagonals_of_norms (nuFixed k) _ (chart_diagA (nuFixed k) (genericChart k) (diagA_fixed k))
    (normV1_fixed k) (normS1_fixed k) (normC1_fixed k)

private theorem power_diagB_fixed : ∀ p, DiagIn (nuFixed k) (power (encoderB (genericChart k)) p) :=
  power_diagonals_of_norms (nuFixed k) _ (chart_diagB (nuFixed k) (genericChart k) (diagB_fixed k))
    (normV2_fixed k) (normS2_fixed k) (normC2_fixed k)

private theorem gramV_fixed : BV (vectorA (genericChart k)) (vectorB (genericChart k)) ∈ (nuFixed k) := by
  rw [chart_gramV]
  change 1 * includeBase k (ι k (c k)) +
    includeBase k (ι k (a k)) * includeBase k (ι k (b k)) ∈ (nuFixed k)
  rw [one_mul, ← map_mul, ← map_add]
  exact include_fixed k (reorient_vGram k)

private theorem gramS_fixed : BS (genericChart k).s1 (genericChart k).s2 ∈ (nuFixed k) := by
  rw [chart_gramS]
  rw [generic_matrix, generic_matrix, ← map_add]
  exact include_fixed k (reorient_sGram k)

private theorem gramC_fixed : BC (genericChart k).c1 (genericChart k).c2 ∈ (nuFixed k) := by
  rw [chart_gramC]
  rw [generic_matrix, generic_matrix, ← map_add]
  exact include_fixed k (reorient_cGram k)

private theorem crossA_fixed (i j : Fin 4) (hi : i < 2) (hj : ¬ j < 2) :
    (genericChart k).r1 * matrixM (genericChart k) i j + (genericChart k).z1 * matrixM (genericChart k) j i ∈ (nuFixed k) := by
  rw [generic_matrix, generic_matrix]
  change 1 * includeBase k (rationalM k i j) +
    includeBase k (ι k (a k)) * includeBase k (rationalM k j i) ∈ (nuFixed k)
  rw [one_mul, ← map_mul, ← map_add]
  exact include_fixed k (reorient_trialityA k i j hi hj)

private theorem crossB_fixed (i j : Fin 4) (hi : i < 2) (hj : ¬ j < 2) :
    (genericChart k).r2 * matrixM (genericChart k) i j + (genericChart k).z2 * matrixM (genericChart k) j i ∈ (nuFixed k) := by
  rw [generic_matrix, generic_matrix]
  change includeBase k (ι k (b k)) * includeBase k (rationalM k i j) +
    includeBase k (ι k (c k)) * includeBase k (rationalM k j i) ∈ (nuFixed k)
  rw [← map_mul, ← map_mul, ← map_add]
  exact include_fixed k (reorient_trialityB k i j hi hj)

private theorem trialityA1C2_fixed : triality (vectorA (genericChart k)) (genericChart k).s1 (genericChart k).c2 ∈ (nuFixed k) := by
  rw [chart_trialityA1C2]
  exact crossA_fixed k 0 3 (by decide) (by decide)

private theorem trialityA2C1_fixed : triality (vectorA (genericChart k)) (genericChart k).s2 (genericChart k).c1 ∈ (nuFixed k) := by
  rw [chart_trialityA2C1]
  exact crossA_fixed k 1 2 (by decide) (by decide)

private theorem trialityA2C2_fixed : triality (vectorA (genericChart k)) (genericChart k).s2 (genericChart k).c2 ∈ (nuFixed k) := by
  rw [chart_trialityA2C2]
  exact crossA_fixed k 1 3 (by decide) (by decide)

private theorem trialityB1C2_fixed : triality (vectorB (genericChart k)) (genericChart k).s1 (genericChart k).c2 ∈ (nuFixed k) := by
  rw [chart_trialityB1C2]
  exact crossB_fixed k 0 3 (by decide) (by decide)

private theorem trialityB2C1_fixed : triality (vectorB (genericChart k)) (genericChart k).s2 (genericChart k).c1 ∈ (nuFixed k) := by
  rw [chart_trialityB2C1]
  exact crossB_fixed k 1 2 (by decide) (by decide)

private theorem trialityB1C1_fixed : triality (vectorB (genericChart k)) (genericChart k).s1 (genericChart k).c1 ∈ (nuFixed k) := by
  rw [chart_trialityB1C1]
  exact crossB_fixed k 0 2 (by decide) (by decide)

private theorem UC_fixed : BC (sourceMuC (vectorA (genericChart k)) (genericChart k).s1)
    (sourceMuC (vectorB (genericChart k)) (genericChart k).s2) ∈ (nuFixed k) := by
  rw [chart_UC]
  rw [generic_matrix, generic_matrix]
  change 1 * includeBase k (ι k (c k)) * includeBase k (rationalM k 0 1) +
    includeBase k (ι k (b k)) * includeBase k (ι k (a k)) *
      includeBase k (rationalM k 1 0) ∈ (nuFixed k)
  rw [one_mul, mul_comm (includeBase k (ι k (b k))) (includeBase k (ι k (a k))),
    ← map_mul, ← map_mul, ← map_mul, ← map_add]
  exact include_fixed k (reorient_UC k)

private theorem US_fixed : BS (sourceMuS (genericChart k).c1 (vectorA (genericChart k)))
    (sourceMuS (genericChart k).c2 (vectorB (genericChart k))) ∈ (nuFixed k) := by
  rw [chart_US]
  rw [generic_matrix, generic_matrix]
  change includeBase k (ι k (b k)) * includeBase k (ι k (a k)) *
    includeBase k (rationalM k 2 3) + 1 * includeBase k (ι k (c k)) *
      includeBase k (rationalM k 3 2) ∈ (nuFixed k)
  rw [one_mul, mul_comm (includeBase k (ι k (b k))) (includeBase k (ι k (a k)))]
  simpa only [map_add, map_mul] using include_fixed k (reorient_US k)

private theorem UV_fixed : normalizedUV (genericChart k).s1 (genericChart k).s2 (genericChart k).c1 (genericChart k).c2 ∈ (nuFixed k) := by
  rw [chart_UV, rootSum_eq_S]
  apply (nuFixed k).sub_mem
  · have hq : exteriorQ (matrixM (genericChart k)) = includeBase k (exteriorQ (rationalM k)) := by
      simp only [exteriorQ, generic_matrix, map_add, map_sub, map_mul]
    rw [hq]
    exact include_fixed k (reorient_exteriorQ k)
  · change nu k (T (Base k) + includeBase k (Matrix.det (rationalM k)) / T (Base k)) =
      T (Base k) + includeBase k (Matrix.det (rationalM k)) / T (Base k)
    simp only [map_add, map_div₀, nu_T, nu_base, reorient_det_rationalM]

private theorem sector21_fixed :
    SectorIn (nuFixed k) (sourceSquare (encoderA (genericChart k)))
      (encoderB (genericChart k)) :=
  chart_sector21 (nuFixed k) (genericChart k) (diagA_fixed k)
    (gramV_fixed k) (gramS_fixed k) (gramC_fixed k)
    (trialityB1C1_fixed k) (trialityA2C1_fixed k) (trialityA1C2_fixed k)

private theorem sector12_fixed :
    SectorIn (nuFixed k) (encoderA (genericChart k))
      (sourceSquare (encoderB (genericChart k))) :=
  chart_sector12 (nuFixed k) (genericChart k) (diagB_fixed k)
    (gramV_fixed k) (gramS_fixed k) (gramC_fixed k)
    (trialityA2C2_fixed k) (trialityB1C2_fixed k) (trialityB2C1_fixed k)

theorem ledgerIn_nuFixed :
    LedgerIn (nuFixed k) (sourceLedger (encoderA (genericChart k))
      (encoderB (genericChart k))) := by
  exact ledgerIn_of_measurements (nuFixed k)
    (encoderA (genericChart k)) (encoderB (genericChart k))
    (power_diagA_fixed k) (power_diagB_fixed k)
    ⟨gramV_fixed k, gramS_fixed k, gramC_fixed k⟩
    (sector12_fixed k) (sector21_fixed k) (UV_fixed k) (US_fixed k) (UC_fixed k)

theorem H_le_nuFixed : H k ≤ nuFixed k := by
  apply Subfield.closure_le.2
  rintro z (hz | hz)
  · have hg : groundBase k ≤ nuFixed k := by
      apply Subfield.closure_le.2
      rintro _ ⟨c,rfl⟩
      exact nu_constant k c
    exact hg hz
  · exact (ledgerCells_subset_iff (nuFixed k) _ _).2 (ledgerIn_nuFixed k) hz

theorem deck_fixed_of_mem_H {z : FunctionField k} (hz : z ∈ H k) : deck k z = z := by
  have ho : z ∈ orientationLedgerField (groundBase k) (genericChart k) :=
    Subfield.subset_closure (Or.inl hz)
  rw [orientation_eq_invariantField] at ho
  exact (fixed_iff_mem_invariantField (Base k) (Matrix.det (rationalM k))
    (det_rationalM_ne_zero k) z).2 ho

theorem tau_fixed_of_mem_H {z : FunctionField k} (hz : z ∈ H k) : tau k z = z := by
  rw [tau_apply, show nu k z = z from H_le_nuFixed k hz]
  exact deck_fixed_of_mem_H k hz

theorem kappa_not_mem_H : kappa k ∉ H k := by
  intro hk
  have h : -kappa k = kappa k := (nu_kappa k).symm.trans (H_le_nuFixed k hk)
  have hz : (2 : FunctionField k) * kappa k = 0 := by linear_combination -h
  exact kappa_ne_zero k ((mul_eq_zero.mp hz).resolve_left (by norm_num))

end AlbertLean.Generic.GenericLedgerInvariance
