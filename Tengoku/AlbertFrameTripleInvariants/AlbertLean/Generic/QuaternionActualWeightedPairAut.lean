import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualWeightedPairComparison
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedCoordinateTransport
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedFirstProjectorMatrix

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_actual_same_ledger_pair_jordanAut` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge

open AlbertLean.Generic.QuaternionRow.BlockEigenbasis
open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge

variable {K : Type*} [Field K] [CharZero K]

/-- Actual Q1 pair comparison: equality of the displayed pair ledger on the
weighted nonscalar-pivot open produces one genuine Jordan automorphism taking
all three labelled projectors of each frame to their primed counterparts.
@isnad1 id=ex.17h11v.s14.de8eacceadf0 from=translated src=- shape=401117d6 vocab=0163d893
-/
theorem exists_actual_same_ledger_pair_jordanAut
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
    ∃ g : ScalarJordanAut.Aut (K := K),
      (∀ i, g.linear (E i) = E' i) ∧ (∀ i, g.linear (F i) = F' i) := by
  obtain ⟨T, S, hTS, hST, hblocks⟩ :=
    exists_actual_same_ledger_pair_block_conjugator E F E' F'
      hEidem hEsum hFidem hFsum hEidem' hEsum' hFidem' hFsum'
      u v u' v' p hp hp' hpne hFu hFv hFu' hFv' hledger hp12 hdisc
  have hdet : det2 S ≠ 0 := by
    change determinant S ≠ 0
    have hdetprod : determinant S * determinant T = 1 := by
      rw [determinant_eq_det, determinant_eq_det, ← Matrix.det_mul, hST,
        Matrix.det_one]
    intro hzero
    rw [hzero, zero_mul] at hdetprod
    exact zero_ne_one hdetprod
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  let L' := weightedCoordinateEquiv E' hEidem' hEsum' u' v' p hp' hpne
  let B := coordinateConjugate L (matrixAction (F 1 : Mat6 K))
  let C := coordinateConjugate L' (matrixAction (F' 1 : Mat6 K))
  let g := commonPlaneJordanAut E E' hEidem hEsum hEidem' hEsum'
    u v u' v' p hp hp' hpne S T hST hTS hdet
  have hmap_of_coordinate_conjugacy (P Q : Carrier K)
      (hcoord : (commonPlaneMap S).comp
        ((coordinateConjugate L (matrixAction (P : Mat6 K))).comp
          (commonPlaneMap T)) =
        coordinateConjugate L' (matrixAction (Q : Mat6 K))) :
      g.linear P = Q := by
    dsimp only [g]
    apply commonPlaneJordanAut_maps_of_action E E' hEidem hEsum
      hEidem' hEsum' u v u' v' p hp hp' hpne S T hST hTS hdet P Q
    simpa only [commonPlaneForward, commonPlaneBackward, L, L'] using
      coordinate_transport L L' (matrixAction (P : Mat6 K))
        (matrixAction (Q : Mat6 K)) S T hcoord
  have hEcoord (i : Fin 3) :
      (commonPlaneMap S).comp
        ((coordinateConjugate L (matrixAction (E i : Mat6 K))).comp
          (commonPlaneMap T)) =
        coordinateConjugate L' (matrixAction (E' i : Mat6 K)) := by
    rw [coordinateConjugate_first_frame E hEidem hEsum u v p hp hpne i,
      coordinateConjugate_first_frame E' hEidem' hEsum' u' v' p hp' hpne i,
      ← LinearMap.comp_assoc, commonPlaneMap_comm_standardProjector S i,
      LinearMap.comp_assoc, commonPlaneMap_comp S T hST]
    simp
  have hF0coord :
      (commonPlaneMap S).comp
        ((coordinateConjugate L (matrixAction (F 0 : Mat6 K))).comp
          (commonPlaneMap T)) =
        coordinateConjugate L' (matrixAction (F' 0 : Mat6 K)) := by
    rw [coordinateConjugate_first_projector E (F 0) hEidem hEsum
        u v p hp hpne hFu hFv,
      coordinateConjugate_first_projector E' (F' 0) hEidem' hEsum'
        u' v' p hp' hpne hFu' hFv',
      ← LinearMap.comp_assoc, commonPlaneMap_comm_weightedFirst S p,
      LinearMap.comp_assoc, commonPlaneMap_comp S T hST]
    simp
  have hF1coord :
      (commonPlaneMap S).comp
        ((coordinateConjugate L (matrixAction (F 1 : Mat6 K))).comp
          (commonPlaneMap T)) =
        coordinateConjugate L' (matrixAction (F' 1 : Mat6 K)) := by
    exact commonPlane_conjugates_operator_of_blocks B C T S hTS hST
      (by intro i j; exact hblocks i j)
  have hgE : ∀ i, g.linear (E i) = E' i := fun i =>
    hmap_of_coordinate_conjugacy (E i) (E' i) (hEcoord i)
  have hgF0 : g.linear (F 0) = F' 0 :=
    hmap_of_coordinate_conjugacy (F 0) (F' 0) hF0coord
  have hgF1 : g.linear (F 1) = F' 1 :=
    hmap_of_coordinate_conjugacy (F 1) (F' 1) hF1coord
  have hFsumCarrier : F 0 + F 1 + F 2 = (SelfAdjointCarrier.one : Carrier K) := by
    apply Subtype.ext
    exact hFsum
  have hFsumCarrier' : F' 0 + F' 1 + F' 2 = (SelfAdjointCarrier.one : Carrier K) := by
    apply Subtype.ext
    exact hFsum'
  have hgF2 : g.linear (F 2) = F' 2 := by
    have hsum := congrArg g.linear hFsumCarrier
    simp only [map_add, g.map_one, hgF0, hgF1] at hsum
    exact add_left_cancel (hsum.trans hFsumCarrier'.symm)
  refine ⟨g, hgE, ?_⟩
  intro i
  fin_cases i
  · exact hgF0
  · exact hgF1
  · exact hgF2

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
