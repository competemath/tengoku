import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualWeightedPairAut

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms commonPlaneForwardBackward_matrix_laws` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_actual_same_ledger_pair_jordanAut_provenance` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.BlockEigenbasis
open AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge
open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.QuaternionRow.WordMatrixConnection

variable {K : Type*} [Field K] [CharZero K]

/-- The concrete matrices underlying the common-plane automorphism retain
both inverse laws and the similitude multiplier of the forward plane matrix.
The orientation agrees with `commonPlaneJordanAut_apply_coe`: `S` is forward
and `T` is backward.
@isnad1 id=other.9h10v.s12.64458240d5a9 from=translated src=- shape=af4eb29b vocab=a79fa7a2
-/
theorem commonPlaneForwardBackward_matrix_laws
    (E E' : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (hEidem' : ∀ i, (E' i : Mat6 K) * E' i = E' i)
    (hEsum' : (E' 0 : Mat6 K) + E' 1 + E' 2 = 1)
    (u v u' v' : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K))
      (matrixAction (E i : Mat6 K) u) (matrixAction (E i : Mat6 K) v))
    (hp' : ∀ i, p i = (omega (K := K))
      (matrixAction (E' i : Mat6 K) u') (matrixAction (E' i : Mat6 K) v'))
    (hpne : ∀ i, p i ≠ 0)
    (S T : Mat2 K) (hST : S * T = 1) (hTS : T * S = 1) :
    let A := matrixOfLinear
      (commonPlaneForward E E' hEidem hEsum hEidem' hEsum'
        u v u' v' p hp hp' hpne S)
    let B := matrixOfLinear
      (commonPlaneBackward E E' hEidem hEsum hEidem' hEsum'
        u v u' v' p hp hp' hpne T)
    A * B = 1 ∧ B * A = 1 ∧
      A.transpose * symplecticJ * A = det2 S • symplecticJ := by
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  let L' := weightedCoordinateEquiv E' hEidem' hEsum' u' v' p hp' hpne
  let forward := commonPlaneForward E E' hEidem hEsum hEidem' hEsum'
    u v u' v' p hp hp' hpne S
  let backward := commonPlaneBackward E E' hEidem hEsum hEidem' hEsum'
    u v u' v' p hp hp' hpne T
  let A := matrixOfLinear forward
  let B := matrixOfLinear backward
  have hforwardBackward : forward.comp backward = LinearMap.id := by
    apply LinearMap.ext
    intro x
    have hc := LinearMap.congr_fun (commonPlaneMap_comp S T hST) (L'.symm x)
    change L' (commonPlaneMap S
      (L.symm (L (commonPlaneMap T (L'.symm x))))) = x
    rw [L.symm_apply_apply]
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hc
    rw [hc, L'.apply_symm_apply]
  have hbackwardForward : backward.comp forward = LinearMap.id := by
    apply LinearMap.ext
    intro x
    have hc := LinearMap.congr_fun (commonPlaneMap_comp T S hTS) (L.symm x)
    change L (commonPlaneMap T
      (L'.symm (L' (commonPlaneMap S (L.symm x))))) = x
    rw [L'.symm_apply_apply]
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hc
    rw [hc, L.apply_symm_apply]
  have hAB : A * B = 1 := by
    apply matrixAction_injective
    rw [matrixAction_mul, matrixAction_matrixOfLinear,
      matrixAction_matrixOfLinear, hforwardBackward, matrixAction_one]
  have hBA : B * A = 1 := by
    apply matrixAction_injective
    rw [matrixAction_mul, matrixAction_matrixOfLinear,
      matrixAction_matrixOfLinear, hbackwardForward, matrixAction_one]
  have hpres (x y : Vec6 K) :
      (omega (K := K)) (forward x) (forward y) =
        det2 S * (omega (K := K)) x y := by
    change (omega (K := K)) (L' (commonPlaneMap S (L.symm x)))
      (L' (commonPlaneMap S (L.symm y))) = _
    have hL' (z : Vec6 K) :
        L' z = weightedCoordinateLinear E' u' v' z := rfl
    have hL (z : Vec6 K) :
        L z = weightedCoordinateLinear E u v z := rfl
    rw [hL', hL', weightedCoordinate_form E' hEidem' hEsum' u' v' p hp',
      commonPlaneMap_form,
      ← weightedCoordinate_form E hEidem hEsum u v p hp,
      ← hL, ← hL, L.apply_symm_apply, L.apply_symm_apply]
  have hform : A.transpose * symplecticJ * A = det2 S • symplecticJ := by
    ext i j
    rw [symplectic_product_entry]
    rw [← matrixAction_basisVector A i, ← matrixAction_basisVector A j,
      matrixAction_matrixOfLinear, hpres, omega_basisVector]
    rfl
  change A * B = 1 ∧ B * A = 1 ∧
    A.transpose * symplecticJ * A = det2 S • symplecticJ
  exact ⟨hAB, hBA, hform⟩

/-- Actual Q1 pair comparison retaining the concrete GSp matrices underlying
the constructed Jordan automorphism.  The hypotheses use the same selected
vectors and the same single left-pivot discriminant as the existing endpoint.
@isnad1 id=ex.17h11v.s14.51c23feb1787 from=translated src=- shape=b92352b7 vocab=f424b03e
-/
theorem exists_actual_same_ledger_pair_jordanAut_provenance
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
    ∃ (g : ScalarJordanAut.Aut (K := K)) (A B : Mat6 K) (nu : K),
      A * B = 1 ∧ B * A = 1 ∧ nu ≠ 0 ∧
      A.transpose * symplecticJ * A = nu • symplecticJ ∧
      (∀ X : Carrier K,
        ((g.linear X : Carrier K) : Mat6 K) = A * (X : Mat6 K) * B) ∧
      (∀ i, g.linear (E i) = E' i) ∧
      (∀ i, g.linear (F i) = F' i) := by
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
  let A : Mat6 K := matrixOfLinear
    (commonPlaneForward E E' hEidem hEsum hEidem' hEsum'
      u v u' v' p hp hp' hpne S)
  let Ainv : Mat6 K := matrixOfLinear
    (commonPlaneBackward E E' hEidem hEsum hEidem' hEsum'
      u v u' v' p hp hp' hpne T)
  have hmatrix := commonPlaneForwardBackward_matrix_laws
    E E' hEidem hEsum hEidem' hEsum' u v u' v' p hp hp' hpne
    S T hST hTS
  dsimp only at hmatrix
  have hAAinv : A * Ainv = 1 := by
    simpa only [A, Ainv] using hmatrix.1
  have hAinvA : Ainv * A = 1 := by
    simpa only [A, Ainv] using hmatrix.2.1
  have hAform : A.transpose * symplecticJ * A = det2 S • symplecticJ := by
    simpa only [A] using hmatrix.2.2
  have hgCarrier (X : Carrier K) :
      ((g.linear X : Carrier K) : Mat6 K) = A * (X : Mat6 K) * Ainv := by
    simpa only [g, A, Ainv] using
      (commonPlaneJordanAut_apply_coe E E' hEidem hEsum hEidem' hEsum'
        u v u' v' p hp hp' hpne S T hST hTS hdet X)
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
  have hgF : ∀ i, g.linear (F i) = F' i := by
    intro i
    fin_cases i
    · exact hgF0
    · exact hgF1
    · exact hgF2
  exact ⟨g, A, Ainv, det2 S, hAAinv, hAinvA, hdet, hAform,
    hgCarrier, hgE, hgF⟩

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
