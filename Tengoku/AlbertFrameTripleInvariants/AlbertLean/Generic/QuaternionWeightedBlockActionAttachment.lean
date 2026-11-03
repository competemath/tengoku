import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualWeightedSecondProjector
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedCommonPlaneAut
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionBlockEigenbasis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms linear_eq_of_weightedBlock_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms weightedBlock_commonPlane_conjugate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms commonPlane_conjugates_operator_of_blocks` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.ActualFrameCoverage
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.QuaternionRow.BlockEigenbasis
variable {K : Type*} [Field K] [CharZero K]

/-- All `3×3` literal two-plane blocks determine the linear operator.
@isnad1 id=eq.1h3v.s8.0f11e369c4ad from=translated src=- shape=d11e65cd vocab=4878ed54
-/
theorem linear_eq_of_weightedBlock_eq (A B : Vec6 K →ₗ[K] Vec6 K)
    (h : ∀ i j, weightedBlock A i j = weightedBlock B i j) : A = B := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, b, hx⟩ := standard_spans (K := K) x
  rw [hx]
  simp only [map_add, map_sum, map_smul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> congr 1
  · funext q
    rcases q with i | i
    · have hij := congrFun (congrFun (h i j) 0) 0
      simpa [weightedBlock, weightedPairIndex, standardE] using hij
    · have hij := congrFun (congrFun (h i j) 1) 0
      simpa [weightedBlock, weightedPairIndex, standardE] using hij
  · funext q
    rcases q with i | i
    · have hij := congrFun (congrFun (h i j) 0) 1
      simpa [weightedBlock, weightedPairIndex, standardF] using hij
    · have hij := congrFun (congrFun (h i j) 1) 1
      simpa [weightedBlock, weightedPairIndex, standardF] using hij

private theorem commonPlaneMap_basis
    (T : Mat2 K) (j : Fin 3) (s : Fin 2) :
    commonPlaneMap T (basisVector (weightedPairIndex j s)) =
      T 0 s • basisVector (Sum.inl j) +
        T 1 s • basisVector (Sum.inr j) := by
  classical
  funext q
  rcases q with q | q <;> fin_cases s <;>
    simp [commonPlaneMap, weightedPairIndex, basisVector, Pi.single_apply] <;> ring

/-- Applying the same `2×2` coordinate change on all three source and target
planes conjugates each literal block by those two matrices.
@isnad1 id=eq.0h6v.s9.bb8ad5ea5db9 from=translated src=- shape=441ada2a vocab=932332b7
-/
theorem weightedBlock_commonPlane_conjugate
    (R T : Mat2 K) (B : Vec6 K →ₗ[K] Vec6 K) (i j : Fin 3) :
    weightedBlock ((commonPlaneMap R).comp (B.comp (commonPlaneMap T))) i j =
      R * weightedBlock B i j * T := by
  ext r s
  change (commonPlaneMap R)
      (B (commonPlaneMap T (basisVector (weightedPairIndex j s))))
      (weightedPairIndex i r) =
    (R * weightedBlock B i j * T) r s
  rw [commonPlaneMap_basis T j s]
  simp only [map_add, map_smul]
  fin_cases r <;> fin_cases s <;>
    simp [weightedBlock, weightedPairIndex, commonPlaneMap,
      Matrix.mul_apply, Fin.sum_univ_two, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul] <;> ring

/-- The orientation needed by Q1: if `B=T*C*S`, then conjugating the source
operator by `S` forward and `T` backward yields the target operator.
@isnad1 id=eq.3h5v.s10.1ed3ed0c60ed from=translated src=- shape=5059e98a vocab=932332b7
-/
theorem commonPlane_conjugates_operator_of_blocks
    (B C : Vec6 K →ₗ[K] Vec6 K) (T S : Mat2 K)
    (hTS : T * S = 1) (hST : S * T = 1)
    (hblocks : ∀ i j, weightedBlock B i j =
      T * weightedBlock C i j * S) :
    (commonPlaneMap S).comp (B.comp (commonPlaneMap T)) = C := by
  apply linear_eq_of_weightedBlock_eq
  intro i j
  rw [weightedBlock_commonPlane_conjugate, hblocks]
  calc
    S * (T * weightedBlock C i j * S) * T =
        (S * T) * weightedBlock C i j * (S * T) := by
          simp only [Matrix.mul_assoc]
    _ = weightedBlock C i j := by rw [hST]; simp

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
