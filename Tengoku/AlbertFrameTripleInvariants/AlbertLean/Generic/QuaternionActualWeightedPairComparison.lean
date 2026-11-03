import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualWeightedPairData
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualWeightedPivotEquation
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualWeightedPairSpectralConsumer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_actual_same_ledger_pair_block_conjugator` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge
open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.QuaternionRow.BlockEigenbasis
variable {K : Type*} [Field K] [CharZero K]

/-- Actual two-pair Q1 comparison through the rational nonscalar pivot.  No
block equation is assumed: all of them come from the actual frames.-/
theorem exists_actual_same_ledger_pair_block_conjugator
    (E F E' F' : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (hFidem : ∀ i, (F i : Mat6 K) * F i = F i)
    (hFsum : (F 0 : Mat6 K) + F 1 + F 2 = 1)
    (hEidem' : ∀ i, (E' i : Mat6 K) * E' i = E' i)
    (hEsum' : (E' 0 : Mat6 K) + E' 1 + E' 2 = 1)
    (hFidem' : ∀ i, (F' i : Mat6 K) * F' i = F' i)
    (hFsum' : (F' 0 : Mat6 K) + F' 1 + F' 2 = 1)
    (u v u' v' : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v))
    (hp' : ∀ i, p i = (omega (K := K)) (matrixAction (E' i : Mat6 K) u')
      (matrixAction (E' i : Mat6 K) v')) (hpne : ∀ i, p i ≠ 0)
    (hFu : ∀ i, matrixAction (F 0 : Mat6 K) (matrixAction (E i : Mat6 K) u) = p i • u)
    (hFv : ∀ i, matrixAction (F 0 : Mat6 K) (matrixAction (E i : Mat6 K) v) = p i • v)
    (hFu' : ∀ i, matrixAction (F' 0 : Mat6 K) (matrixAction (E' i : Mat6 K) u') = p i • u')
    (hFv' : ∀ i, matrixAction (F' 0 : Mat6 K) (matrixAction (E' i : Mat6 K) v') = p i • v')
    (hledger : ∀ i, jordanTrace (K := K) ((E i : Mat6 K) * (F 1 : Mat6 K)) =
      jordanTrace (K := K) ((E' i : Mat6 K) * (F' 1 : Mat6 K)))
    (hp12 : p 1 + p 2 ≠ 0)
    (hdisc : let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
      let B := fun i j => weightedBlock (coordinateConjugate L
        (matrixAction (F 1 : Mat6 K))) i j
      trace2 (B 0 1) ^ 2 - 4 * determinant (B 0 1) ≠ 0) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    let L' := weightedCoordinateEquiv E' hEidem' hEsum' u' v' p hp' hpne
    let B := fun i j => weightedBlock (coordinateConjugate L (matrixAction (F 1 : Mat6 K))) i j
    let C := fun i j => weightedBlock (coordinateConjugate L' (matrixAction (F' 1 : Mat6 K))) i j
    ∃ T S : Mat2 K, T * S = 1 ∧ S * T = 1 ∧ ∀ i j, B i j = T * C i j * S := by
  dsimp only at hdisc ⊢
  obtain ⟨q, hdB, hdC, hrB, hcB, hrC, hcC, hsB, hsC⟩ :=
    actual_same_ledger_weighted_pair_data E F E' F' hEidem hEsum hFidem hFsum
      hEidem' hEsum' hFidem' hFsum' u v u' v' p hp hp' hpne
      hFu hFv hFu' hFv' hledger
  dsimp only at hdB hdC hrB hcB hrC hcC hsB hsC
  have hiB := actual_weighted_pivot_idempotent E (F 1) hEidem hEsum
    u v p hp hpne (hFidem 1)
  have hiC := actual_weighted_pivot_idempotent E' (F' 1) hEidem' hEsum'
    u' v' p hp' hpne (hFidem' 1)
  dsimp only at hiB hiC
  exact exists_pair_conjugator_of_actual_weighted_data _ _ p q hpne hp12
    hdB hdC hrB hcB hrC hcC hsB hsC hiB hiC hdisc

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
