import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualWeightedPairAut
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedProjectorCompression

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_actual_first_projector_ledger_coordinates` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_actual_same_pair_ledger_jordanAut` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.ActualFrameCoverage
open AlbertLean.Generic.QuaternionRow.BlockEigenbasis
open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge

variable {K : Type*} [Field K] [CharZero K]

/-- The normalized compression weights supplied by an actual pair are the
literal half-trace overlap cells.  No nonvanishing assumption is used in this
identification: the auxiliary coordinate system is the complete `F`-frame
basis and has constant weight one.-/
theorem exists_actual_first_projector_ledger_coordinates
    (E F : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEtrace : ∀ i, jordanTrace (K := K) (E i : Mat6 K) = 1)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (hFidem : ∀ i, (F i : Mat6 K) * F i = F i)
    (hFtrace : ∀ i, jordanTrace (K := K) (F i : Mat6 K) = 1)
    (hFsum : (F 0 : Mat6 K) + F 1 + F 2 = 1) :
    ∃ u v : Vec6 K,
      let p : Fin 3 → K := fun i =>
        jordanTrace (K := K) ((E i : Mat6 K) * (F 0 : Mat6 K))
      (∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
        (matrixAction (E i : Mat6 K) v)) ∧
      (∀ i, matrixAction (F 0 : Mat6 K)
        (matrixAction (E i : Mat6 K) u) = p i • u) ∧
      (∀ i, matrixAction (F 0 : Mat6 K)
        (matrixAction (E i : Mat6 K) v) = p i • v) := by
  obtain ⟨fu, fv, hfyp, hFfu, hFfv, hspan⟩ :=
    exists_spanning_carrier_frame_eigenbasis F hFidem hFtrace hFsum
  let u : Vec6 K := fu 0
  let v : Vec6 K := fv 0
  have hFu0 : matrixAction (F 0 : Mat6 K) u = u := by
    simpa [u] using hFfu 0 0
  have hFv0 : matrixAction (F 0 : Mat6 K) v = v := by
    simpa [v] using hFfv 0 0
  have huv : (omega (K := K)) u v = 1 := by
    simpa [u, v] using hfyp.pair 0
  have hspan0 : ∀ x, matrixAction (F 0 : Mat6 K) x = x →
      ∃ a b : K, x = a • u + b • v := by
    intro x hx
    obtain ⟨a, b, hab⟩ := hspan x
    refine ⟨a 0, b 0, ?_⟩
    rw [← hx, hab]
    simp only [map_add, map_sum, map_smul, hFfu, hFfv]
    simp [u, v, Fin.sum_univ_succ]
  let U : Vec6 K := ∑ j, fu j
  let V : Vec6 K := ∑ j, fv j
  have hFU (i : Fin 3) : matrixAction (F i : Mat6 K) U = fu i := by
    fin_cases i <;> simp [U, hFfu, Fin.sum_univ_succ]
  have hFV (i : Fin 3) : matrixAction (F i : Mat6 K) V = fv i := by
    fin_cases i <;> simp [V, hFfv, Fin.sum_univ_succ]
  let oneWeight : Fin 3 → K := fun _ => 1
  have honeWeight : ∀ i, oneWeight i =
      (omega (K := K)) (matrixAction (F i : Mat6 K) U)
        (matrixAction (F i : Mat6 K) V) := by
    intro i
    rw [hFU, hFV]
    simpa [oneWeight] using (hfyp.pair i).symm
  have honeWeight_ne : ∀ i, oneWeight i ≠ 0 := by
    intro i
    simp [oneWeight]
  let L := weightedCoordinateEquiv F hFidem hFsum U V oneWeight
    honeWeight honeWeight_ne
  have hLleft : L (basisVector (Sum.inl (0 : Fin 3))) = u := by
    change weightedCoordinateLinear F U V
      (basisVector (Sum.inl (0 : Fin 3))) = u
    rw [weightedCoordinateLinear_basis_left, hFU]
  have hLright : matrixAction (F 0 : Mat6 K) V = v := by
    exact hFV 0
  have hover (i : Fin 3) :
      (omega (K := K)) (matrixAction (E i : Mat6 K) u)
          (matrixAction (E i : Mat6 K) v) =
        (omega (K := K)) (matrixAction (E i : Mat6 K) u) v := by
    calc
      _ = (omega (K := K))
          (matrixAction (E i : Mat6 K)
            (matrixAction (E i : Mat6 K) u)) v :=
        (carrier_action_selfAdjoint (E i)
          (matrixAction (E i : Mat6 K) u) v).symm
      _ = _ := by
        rw [SymplecticProjectorFrame.idempotent_apply
          (matrixAction (E i : Mat6 K))
          (carrier_projector_action_idempotent (E i) (hEidem i))]
  have hweight (i : Fin 3) :
      (omega (K := K)) (matrixAction (E i : Mat6 K) u)
          (matrixAction (E i : Mat6 K) v) =
        jordanTrace (K := K) ((E i : Mat6 K) * (F 0 : Mat6 K)) := by
    obtain ⟨q, hq⟩ := actual_weighted_diagonal_scalar F (E i) hFidem hFsum
      U V oneWeight honeWeight honeWeight_ne 0
    let z := coordinateConjugate L (matrixAction (E i : Mat6 K))
      (basisVector (Sum.inl (0 : Fin 3)))
    have h00 := congrFun (congrFun hq 0) 0
    have hz0 : z (Sum.inl (0 : Fin 3)) = q := by
      simpa [z, weightedBlock, weightedPairIndex, scalar2,
        Matrix.one_apply] using h00
    have hLz : weightedCoordinateLinear F U V z =
        matrixAction (E i : Mat6 K) u := by
      change L z = matrixAction (E i : Mat6 K) u
      simp [z, coordinateConjugate, hLleft]
    have hextract := (weighted_pairing_extract F hFidem hFsum U V
      oneWeight honeWeight z 0).1
    have hqover :
        (omega (K := K)) (matrixAction (E i : Mat6 K) u) v = q := by
      rw [hLz, hLright, hz0] at hextract
      simpa [oneWeight] using hextract
    have hqtrace := diagonal_scalar_eq_actual_pair_ledger F (E i)
      hFidem hFsum U V oneWeight honeWeight honeWeight_ne 0 q hq
    rw [hover, hqover, hqtrace]
    simp only [jordanTrace]
    rw [Matrix.trace_mul_comm]
  have hscalar (i : Fin 3) :=
    scalar_compression_on_hyperbolic_image (omega (K := K))
      (matrixAction (F 0 : Mat6 K)) (matrixAction (E i : Mat6 K))
      (carrier_projector_action_idempotent (F 0) (hFidem 0))
      (carrier_action_selfAdjoint (F 0)) (carrier_action_selfAdjoint (E i))
      u v hFu0 hFv0 huv omega_alternating hspan0
  refine ⟨u, v, ?_⟩
  dsimp only
  refine ⟨fun i => (hweight i).symm, ?_, ?_⟩
  · intro i
    rw [← hweight i, hover i]
    exact (hscalar i).1
  · intro i
    rw [← hweight i, hover i]
    exact (hscalar i).2

/-- Actual trace-one frame pairs with a common literal overlap table are in
one genuine Jordan-automorphism orbit on the stated nonzero and nonscalar
open.  The weighted basis and every compression identity are constructed from
the frame laws.-/
theorem exists_actual_same_pair_ledger_jordanAut
    (E F E' F' : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEtrace : ∀ i, jordanTrace (K := K) (E i : Mat6 K) = 1)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (hFidem : ∀ i, (F i : Mat6 K) * F i = F i)
    (hFtrace : ∀ i, jordanTrace (K := K) (F i : Mat6 K) = 1)
    (hFsum : (F 0 : Mat6 K) + F 1 + F 2 = 1)
    (hEidem' : ∀ i, (E' i : Mat6 K) * E' i = E' i)
    (hEtrace' : ∀ i, jordanTrace (K := K) (E' i : Mat6 K) = 1)
    (hEsum' : (E' 0 : Mat6 K) + E' 1 + E' 2 = 1)
    (hFidem' : ∀ i, (F' i : Mat6 K) * F' i = F' i)
    (hFtrace' : ∀ i, jordanTrace (K := K) (F' i : Mat6 K) = 1)
    (hFsum' : (F' 0 : Mat6 K) + F' 1 + F' 2 = 1)
    (hledger : ∀ i j,
      jordanTrace (K := K) ((E i : Mat6 K) * (F j : Mat6 K)) =
        jordanTrace (K := K) ((E' i : Mat6 K) * (F' j : Mat6 K)))
    (hpne : ∀ i,
      jordanTrace (K := K) ((E i : Mat6 K) * (F 0 : Mat6 K)) ≠ 0)
    (hp12 :
      jordanTrace (K := K) ((E 1 : Mat6 K) * (F 0 : Mat6 K)) +
        jordanTrace (K := K) ((E 2 : Mat6 K) * (F 0 : Mat6 K)) ≠ 0)
    (hdisc : ∀ (u v : Vec6 K)
      (hp : ∀ i,
        jordanTrace (K := K) ((E i : Mat6 K) * (F 0 : Mat6 K)) =
          (omega (K := K)) (matrixAction (E i : Mat6 K) u)
            (matrixAction (E i : Mat6 K) v)),
      let p : Fin 3 → K := fun i =>
        jordanTrace (K := K) ((E i : Mat6 K) * (F 0 : Mat6 K))
      let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
      let B := fun i j => weightedBlock (coordinateConjugate L
        (matrixAction (F 1 : Mat6 K))) i j
      trace2 (B 0 1) ^ 2 - 4 * determinant (B 0 1) ≠ 0) :
    ∃ g : ScalarJordanAut.Aut (K := K),
      (∀ i, g.linear (E i) = E' i) ∧ (∀ i, g.linear (F i) = F' i) := by
  obtain ⟨u, v, hp, hFu, hFv⟩ :=
    exists_actual_first_projector_ledger_coordinates E F hEidem hEtrace
      hEsum hFidem hFtrace hFsum
  obtain ⟨u', v', hpRaw', hFuRaw', hFvRaw'⟩ :=
    exists_actual_first_projector_ledger_coordinates E' F' hEidem' hEtrace'
      hEsum' hFidem' hFtrace' hFsum'
  let p : Fin 3 → K := fun i =>
    jordanTrace (K := K) ((E i : Mat6 K) * (F 0 : Mat6 K))
  have hp' : ∀ i, p i =
      (omega (K := K)) (matrixAction (E' i : Mat6 K) u')
        (matrixAction (E' i : Mat6 K) v') := by
    intro i
    change jordanTrace (K := K) ((E i : Mat6 K) * (F 0 : Mat6 K)) = _
    rw [hledger i 0]
    exact hpRaw' i
  have hFu' : ∀ i, matrixAction (F' 0 : Mat6 K)
      (matrixAction (E' i : Mat6 K) u') = p i • u' := by
    intro i
    change _ = jordanTrace (K := K) ((E i : Mat6 K) * (F 0 : Mat6 K)) • u'
    rw [hledger i 0]
    exact hFuRaw' i
  have hFv' : ∀ i, matrixAction (F' 0 : Mat6 K)
      (matrixAction (E' i : Mat6 K) v') = p i • v' := by
    intro i
    change _ = jordanTrace (K := K) ((E i : Mat6 K) * (F 0 : Mat6 K)) • v'
    rw [hledger i 0]
    exact hFvRaw' i
  apply exists_actual_same_ledger_pair_jordanAut E F E' F'
    hEidem hEsum hFidem hFsum hEidem' hEsum' hFidem' hFsum'
    u v u' v' p hp hp' hpne hFu hFv hFu' hFv'
  · exact fun i => hledger i 1
  · exact hp12
  · exact hdisc u v hp

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
