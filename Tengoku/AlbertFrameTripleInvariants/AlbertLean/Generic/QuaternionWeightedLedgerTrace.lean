import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualWeightedSecondProjector
import Tengoku.Seed.LinearAlgebra.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms operatorTrace_matrixAction` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms diagonal_scalar_eq_actual_pair_ledger` (it only prints; the queue checks the axioms of every declaration). -/

/-! Actual pair-ledger trace attachment consumed by Q1. -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.QuaternionRow.ActualFrameCoverage
open AlbertLean.Generic.SymplecticProjectorFrame

universe u
variable {K : Type u} [Field K] [CharZero K]

theorem operatorTrace_matrixAction (A : Mat6 K) :
    LinearMap.trace K (Vec6 K) (matrixAction A) = Matrix.trace A := by
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K Ix6)]
  simp [Matrix.trace, LinearMap.toMatrix_apply', matrixAction, basisVector,
    Pi.single_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]

theorem trace_standardProjector_comp (B : Vec6 K →ₗ[K] Vec6 K) (i : Fin 3) :
    LinearMap.trace K (Vec6 K) ((standardProjector i).comp B) =
      weightedBlock B i i 0 0 + weightedBlock B i i 1 1 := by
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K Ix6)]
  fin_cases i <;>
    simp [Matrix.trace, LinearMap.toMatrix_apply', LinearMap.comp_apply,
      standardProjector, coordinateLabel, weightedBlock, weightedPairIndex,
      basisVector, Pi.single_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]

theorem first_frame_intertwines_weighted_coordinates
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (i : Fin 3) :
    (matrixAction (E i : Mat6 K)).comp (weightedCoordinateLinear E u v) =
      (weightedCoordinateLinear E u v).comp (standardProjector i) := by
  let Q : Fin 3 → Vec6 K →ₗ[K] Vec6 K :=
    fun j => matrixAction (K := K) (E j : Mat6 K)
  have hQi : ∀ j, IsIdempotent (Q j) :=
    fun j => carrier_projector_action_idempotent (E j) (hEidem j)
  have hQsum : Q 0 + Q 1 + Q 2 = LinearMap.id :=
    carrier_frame_action_sum E hEsum
  have hcomp := comp_zero_of_complete_frame Q hQi hQsum
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply]
  change Q i
      ((∑ j, z (Sum.inl j) • Q j u) +
        ∑ j, z (Sum.inr j) • Q j v) =
    (∑ j, (standardProjector i z) (Sum.inl j) • Q j u) +
      ∑ j, (standardProjector i z) (Sum.inr j) • Q j v
  rw [map_add, map_sum, map_sum]
  simp only [map_smul]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j
    · subst j
      rw [idempotent_apply (Q i) (hQi i)]
      simp [standardProjector, coordinateLabel]
    · rw [← LinearMap.comp_apply, hcomp i j hij]
      simp [standardProjector, coordinateLabel, hij, Ne.symm hij]
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j
    · subst j
      rw [idempotent_apply (Q i) (hQi i)]
      simp [standardProjector, coordinateLabel]
    · rw [← LinearMap.comp_apply, hcomp i j hij]
      simp [standardProjector, coordinateLabel, hij, Ne.symm hij]

theorem coordinateConjugate_first_frame
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v)) (hpne : ∀ i, p i ≠ 0) (i : Fin 3) :
    coordinateConjugate
      (weightedCoordinateEquiv E hEidem hEsum u v p hp hpne)
      (matrixAction (E i : Mat6 K)) = standardProjector i := by
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  have hinter := first_frame_intertwines_weighted_coordinates E hEidem hEsum u v i
  have hL : L.toLinearMap = weightedCoordinateLinear E u v := by
    rfl
  change L.symm.toLinearMap.comp
      ((matrixAction (E i : Mat6 K)).comp L.toLinearMap) = standardProjector i
  rw [hL, hinter]
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply]
  rw [← hL]
  exact L.symm_apply_apply _

/-- The scalar on diagonal block `i` is exactly the actual half-trace pair
ledger cell `jordanTrace (E_i F_1)`.-/
theorem diagonal_scalar_eq_actual_pair_ledger
    (E : Fin 3 → Carrier K) (F1 : Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v)) (hpne : ∀ i, p i ≠ 0)
    (i : Fin 3) (q : K)
    (hq : weightedBlock
      (coordinateConjugate (weightedCoordinateEquiv E hEidem hEsum u v p hp hpne)
        (matrixAction (F1 : Mat6 K))) i i = scalar2 q) :
    q = jordanTrace (K := K) ((E i : Mat6 K) * (F1 : Mat6 K)) := by
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  let B := coordinateConjugate L (matrixAction (F1 : Mat6 K))
  have hEi := coordinateConjugate_first_frame E hEidem hEsum u v p hp hpne i
  have hprod : coordinateConjugate L
      (matrixAction ((E i : Mat6 K) * (F1 : Mat6 K))) =
      (standardProjector i).comp B := by
    rw [matrixAction_mul, coordinateConjugate_comp, hEi]
  have htrace : Matrix.trace ((E i : Mat6 K) * (F1 : Mat6 K)) = 2 * q := by
    rw [← operatorTrace_matrixAction, ← LinearMap.trace_conj'
      (matrixAction ((E i : Mat6 K) * (F1 : Mat6 K))) L.symm]
    change LinearMap.trace K (Vec6 K)
      (coordinateConjugate L
        (matrixAction ((E i : Mat6 K) * (F1 : Mat6 K)))) = _
    rw [hprod, trace_standardProjector_comp]
    have h00 := congrFun (congrFun hq 0) 0
    have h11 := congrFun (congrFun hq 1) 1
    simp [scalar2, Matrix.smul_apply, Matrix.one_apply] at h00 h11
    linear_combination h00 + h11
  rw [jordanTrace, htrace]
  field_simp

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
