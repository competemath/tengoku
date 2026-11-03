import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedLedgerTrace
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionNonscalarBlockNormalizer
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedCommonPlaneAut

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms actual_same_ledger_weighted_pair_data` (it only prints; the queue checks the axioms of every declaration). -/

/-! Actual two-frame input packaged into the weighted block identities. -/
noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.QuaternionRow.WeightedBlockEquations
open AlbertLean.Generic.QuaternionRow.NonscalarBlockNormalizer

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Two actual complete projector pairs with the same pair ledger produce
weighted block arrays with the same literal diagonal scalars, together with
all row, weighted-column, and weighted-adjoint identities.  Thus the later
nonscalar pivot normalizer receives facts derived from actual frames rather
than assumed block equations.-/
theorem actual_same_ledger_weighted_pair_data
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
    (hFu : ∀ i, matrixAction (F 0 : Mat6 K)
      (matrixAction (E i : Mat6 K) u) = p i • u)
    (hFv : ∀ i, matrixAction (F 0 : Mat6 K)
      (matrixAction (E i : Mat6 K) v) = p i • v)
    (hFu' : ∀ i, matrixAction (F' 0 : Mat6 K)
      (matrixAction (E' i : Mat6 K) u') = p i • u')
    (hFv' : ∀ i, matrixAction (F' 0 : Mat6 K)
      (matrixAction (E' i : Mat6 K) v') = p i • v')
    (hledger : ∀ i,
      jordanTrace (K := K) ((E i : Mat6 K) * (F 1 : Mat6 K)) =
      jordanTrace (K := K) ((E' i : Mat6 K) * (F' 1 : Mat6 K))) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    let L' := weightedCoordinateEquiv E' hEidem' hEsum' u' v' p hp' hpne
    let B := fun i j => weightedBlock
      (coordinateConjugate L (matrixAction (F 1 : Mat6 K))) i j
    let C := fun i j => weightedBlock
      (coordinateConjugate L' (matrixAction (F' 1 : Mat6 K))) i j
    ∃ q : Fin 3 → K,
      (∀ i, B i i = scalar2 (q i)) ∧
      (∀ i, C i i = scalar2 (q i)) ∧
      (∀ i, B i 0 + B i 1 + B i 2 = 0) ∧
      (∀ j, p 0 • B 0 j + p 1 • B 1 j + p 2 • B 2 j = 0) ∧
      (∀ i, C i 0 + C i 1 + C i 2 = 0) ∧
      (∀ j, p 0 • C 0 j + p 1 • C 1 j + p 2 • C 2 j = 0) ∧
      (∀ i j, p i • B i j = p j • adj2 (B j i)) ∧
      (∀ i j, p i • C i j = p j • adj2 (C j i)) := by
  dsimp only
  let LB := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  let LC := weightedCoordinateEquiv E' hEidem' hEsum' u' v' p hp' hpne
  let BB := coordinateConjugate LB (matrixAction (F 1 : Mat6 K))
  let CC := coordinateConjugate LC (matrixAction (F' 1 : Mat6 K))
  have hzB := actual_second_projector_weighted_zero_compositions
    E F hEidem hEsum hFidem hFsum u v p hp hpne hFu hFv
  have hzC := actual_second_projector_weighted_zero_compositions
    E' F' hEidem' hEsum' hFidem' hFsum' u' v' p hp' hpne hFu' hFv'
  dsimp only at hzB hzC
  obtain ⟨hrB, hcB⟩ := weighted_block_zero_sums BB p (hpne 0) hzB.1 hzB.2
  obtain ⟨hrC, hcC⟩ := weighted_block_zero_sums CC p (hpne 0) hzC.1 hzC.2
  have hdB := actual_weighted_diagonal_scalar
    E (F 1) hEidem hEsum u v p hp hpne
  have hdC := actual_weighted_diagonal_scalar
    E' (F' 1) hEidem' hEsum' u' v' p hp' hpne
  dsimp only at hdB hdC
  choose q hqB using hdB
  choose q' hqC using hdC
  have hqq : q = q' := by
    funext i
    have hB := diagonal_scalar_eq_actual_pair_ledger
      E (F 1) hEidem hEsum u v p hp hpne i (q i) (hqB i)
    have hC := diagonal_scalar_eq_actual_pair_ledger
      E' (F' 1) hEidem' hEsum' u' v' p hp' hpne i (q' i) (hqC i)
    calc
      q i = jordanTrace (K := K) ((E i : Mat6 K) * (F 1 : Mat6 K)) := hB
      _ = jordanTrace (K := K) ((E' i : Mat6 K) * (F' 1 : Mat6 K)) := hledger i
      _ = q' i := hC.symm
  subst q'
  refine ⟨q, hqB, hqC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    ext r s
    simpa [Fin.sum_univ_three] using hrB i r s
  · intro j
    ext r s
    simpa [Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] using hcB j r s
  · intro i
    ext r s
    simpa [Fin.sum_univ_three] using hrC i r s
  · intro j
    ext r s
    simpa [Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] using hcC j r s
  · exact actual_weighted_block_adjoint E (F 1) hEidem hEsum u v p hp hpne
  · exact actual_weighted_block_adjoint E' (F' 1) hEidem' hEsum' u' v' p hp' hpne

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
