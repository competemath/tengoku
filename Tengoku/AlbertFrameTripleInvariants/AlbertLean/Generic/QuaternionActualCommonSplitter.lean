import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionCommonSplitBasis
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedPlaneCommutation
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedLedgerTrace
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowProbeTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_actual_common_splitter` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms actual_common_splitter_of_cyclic_vector` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.CommonSplitBasis

open BlockEigenbasis NonscalarBlockNormalizer WeightedBlockEquations WeightedProjectorGauge
open ScalarFibre GroupedBridge SelfAdjointCarrier SymplecticMatrixBridge WordMatrixConnection
open ActualFrameCoverage AlbertLean.Generic.SymplecticTransvection
open AlbertLean.Generic.FourRowProbeTrace

variable {K : Type*} [Field K] [CharZero K]

private theorem planeScale_basis_left (t : Fin 3 → K) (j : Fin 3) :
    planeScale t (basisVector (Sum.inl j)) = basisVector (Sum.inl j) := by
  funext a
  rcases a with i | i <;> simp [planeScale, basisVector, Pi.single_apply]

private theorem planeScale_basis_right (t : Fin 3 → K) (j : Fin 3) :
    planeScale t (basisVector (Sum.inr j)) = t j • basisVector (Sum.inr j) := by
  funext a
  rcases a with i | i
  · simp [planeScale, basisVector, Pi.single_apply]
  · by_cases h : i = j
    · subst i; simp [planeScale, basisVector, Pi.single_apply]
    · simp [planeScale, basisVector, Pi.single_apply, h]

private theorem weightedBlock_scaled_mixed
    (C : Vec6 K →ₗ[K] Vec6 K) (t s : Fin 3 → K) (i j : Fin 3) :
    weightedBlock ((planeScale t).comp (C.comp (planeScale s))) i j 0 1 =
        s j * weightedBlock C i j 0 1 ∧
    weightedBlock ((planeScale t).comp (C.comp (planeScale s))) i j 1 0 =
        t i * weightedBlock C i j 1 0 := by
  constructor
  · change planeScale t (C (planeScale s (basisVector (Sum.inr j)))) (Sum.inl i) = _
    rw [planeScale_basis_right, map_smul]
    rfl
  · change planeScale t (C (planeScale s (basisVector (Sum.inl j)))) (Sum.inr i) = _
    rw [planeScale_basis_left]
    rfl

private theorem matrixOfLinear_matrixAction (P : Mat6 K) :
    matrixOfLinear (matrixAction P) = P := by
  apply matrixAction_injective
  rw [matrixAction_matrixOfLinear]

private theorem hat_zero_matrix : hat (0 : Vec3 K) = (0 : Mat3 K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hat]

private theorem unhat_zero_matrix : unhat (0 : Mat3 K) = (0 : Vec3 K) := by
  funext i
  fin_cases i <;> simp [unhat]

/-- Read the transformed actual matrix through its literal weighted blocks.-/
private theorem split_matrix_mixed
    (L : Vec6 K ≃ₗ[K] Vec6 K) (p : Fin 3 → K) (H S : Mat2 K)
    (P : Mat6 K)
    (h : ∀ i j,
      (S * weightedBlock (coordinateConjugate L (matrixAction P)) i j * H) 0 1 = 0 ∧
      (S * weightedBlock (coordinateConjugate L (matrixAction P)) i j * H) 1 0 = 0) :
    let Q := matrixOfLinear (splitForward L p H)
    let N := matrixOfLinear (splitBackward L p S)
    topRight (N * P * Q) = 0 ∧ bottomLeft (N * P * Q) = 0 := by
  let C := (commonPlaneMap S).comp
    ((coordinateConjugate L (matrixAction P)).comp (commonPlaneMap H))
  have hc : ∀ i j, weightedBlock C i j 0 1 = 0 ∧ weightedBlock C i j 1 0 = 0 := by
    intro i j
    simpa only [C, weightedBlock_commonPlane_conjugate] using h i j
  let A := (planeScale p).comp (C.comp (planeScale (fun i => (p i)⁻¹)))
  have ha : matrixAction
      (matrixOfLinear (splitBackward L p S) * P *
        matrixOfLinear (splitForward L p H)) = A := by
    rw [matrixAction_mul, matrixAction_mul, matrixAction_matrixOfLinear,
      matrixAction_matrixOfLinear]
    apply LinearMap.ext
    intro x
    rfl
  have hm (i j : Fin 3) := weightedBlock_scaled_mixed C p (fun i => (p i)⁻¹) i j
  constructor
  · ext i j
    have hz : weightedBlock A i j 0 1 = 0 := by
      rw [(hm i j).1, (hc i j).1, mul_zero]
    change (matrixOfLinear (splitBackward L p S) * P *
      matrixOfLinear (splitForward L p H)) (Sum.inl i) (Sum.inr j) = 0
    rw [← matrixOfLinear_matrixAction
      (matrixOfLinear (splitBackward L p S) * P *
        matrixOfLinear (splitForward L p H)), ha]
    exact hz
  · ext i j
    have hz : weightedBlock A i j 1 0 = 0 := by
      rw [(hm i j).2, (hc i j).2, mul_zero]
    change (matrixOfLinear (splitBackward L p S) * P *
      matrixOfLinear (splitForward L p H)) (Sum.inr i) (Sum.inl j) = 0
    rw [← matrixOfLinear_matrixAction
      (matrixOfLinear (splitBackward L p S) * P *
        matrixOfLinear (splitForward L p H)), ha]
    exact hz

private theorem split_matrix_grouped
    (L : Vec6 K ≃ₗ[K] Vec6 K) (p : Fin 3 → K) (H S : Mat2 K)
    (P : Carrier K)
    (h : ∀ i j,
      (S * weightedBlock (coordinateConjugate L (matrixAction (P : Mat6 K))) i j * H) 0 1 = 0 ∧
      (S * weightedBlock (coordinateConjugate L (matrixAction (P : Mat6 K))) i j * H) 1 0 = 0)
    (hMN : matrixOfLinear (splitBackward L p S) * matrixOfLinear (splitForward L p H) = 1)
    (hN : (matrixOfLinear (splitBackward L p S)).transpose * symplecticJ *
      matrixOfLinear (splitBackward L p S) = symplecticJ) :
    let Q := matrixOfLinear (splitForward L p H)
    let N := matrixOfLinear (splitBackward L p S)
    N * (P : Mat6 K) * Q = grouped (topLeft (N * (P : Mat6 K) * Q)) 0 0 := by
  obtain ⟨hu, hv⟩ := split_matrix_mixed L p H S (P : Mat6 K) h
  have hmem := SimilitudeConjugation.conjugate_mem
    (matrixOfLinear (splitBackward L p S)) (matrixOfLinear (splitForward L p H))
    (1 : K) hMN (by simpa using hN) P
  have hg := grouped_extract _ hmem
  rw [hu, hv] at hg
  simpa only [unhat_zero_matrix] using hg.symm

private theorem planeScale_comm_standardProjector (t : Fin 3 → K) (i : Fin 3) :
    (planeScale t).comp (standardProjector i) =
      (standardProjector i).comp (planeScale t) := by
  apply LinearMap.ext
  intro x
  funext a
  rcases a with j | j <;> by_cases h : j = i <;>
    simp [planeScale, standardProjector, coordinateLabel, h]

private theorem standardProjector_matrix (i : Fin 3) :
    matrixOfLinear (standardProjector (K := K) i) = grouped (diagonalUnit i) 0 0 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [matrixOfLinear, standardProjector, coordinateLabel, basisVector,
      Pi.single_apply, grouped, diagonalUnit, hat_zero_matrix] <;>
    split_ifs <;> simp_all

/-- One actual weighted pair, one ordered discriminant root, one symplectic
basis. All six labelled first/second-frame projectors are split by this same
basis. No eigenbasis, split-frame, or conjugacy premise appears.
@isnad1 id=ex.9h8v.s13.a553783be762 from=translated src=- shape=2259b4ef vocab=102e8144
-/
theorem exists_actual_common_splitter
    (E F : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (hFidem : ∀ i, (F i : Mat6 K) * F i = F i)
    (hFsum : (F 0 : Mat6 K) + F 1 + F 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (SymplecticMatrixBridge.omega (K := K))
      (matrixAction (E i : Mat6 K) u) (matrixAction (E i : Mat6 K) v))
    (hpne : ∀ i, p i ≠ 0)
    (hFu : ∀ i, matrixAction (F 0 : Mat6 K) (matrixAction (E i : Mat6 K) u) = p i • u)
    (hFv : ∀ i, matrixAction (F 0 : Mat6 K) (matrixAction (E i : Mat6 K) v) = p i • v)
    (sigma : K) (hs : sigma ≠ 0)
    (hroot : let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
      let X := weightedBlock (coordinateConjugate L (matrixAction (F 1 : Mat6 K))) 0 1
      sigma ^ 2 = trace2 X ^ 2 - 4 * determinant X) :
    ∃ Q N : Mat6 K, ∃ f : Fin 3 → Mat3 K,
      Q * N = 1 ∧ N * Q = 1 ∧ Q.transpose * symplecticJ * Q = symplecticJ ∧
      (∀ i, N * (E i : Mat6 K) * Q = grouped (diagonalUnit i) 0 0) ∧
      (∀ j, N * (F j : Mat6 K) * Q = grouped (f j) 0 0) := by
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  let A := coordinateConjugate L (matrixAction (F 1 : Mat6 K))
  let B := fun i j => weightedBlock A i j
  have hz := actual_second_projector_weighted_zero_compositions
    E F hEidem hEsum hFidem hFsum u v p hp hpne hFu hFv
  dsimp only at hz
  obtain ⟨hr0, hc0⟩ := weighted_block_zero_sums A p (hpne 0) hz.1 hz.2
  have hd0 := actual_weighted_diagonal_scalar
    E (F 1) hEidem hEsum u v p hp hpne
  dsimp only at hd0
  choose q0 hq0 using hd0
  have hqledger (i : Fin 3) :
      q0 i = ProjectorBlockBridge.jordanTrace (K := K)
        ((E i : Mat6 K) * (F 1 : Mat6 K)) :=
    diagonal_scalar_eq_actual_pair_ledger
      E (F 1) hEidem hEsum u v p hp hpne i (q0 i) (hq0 i)
  let q : Fin 3 → K := fun i =>
    ProjectorBlockBridge.jordanTrace (K := K)
      ((E i : Mat6 K) * (F 1 : Mat6 K))
  have hd : ∀ i, B i i = scalar2 (q i) := by
    intro i
    change weightedBlock A i i = scalar2 (q i)
    simpa only [A, L, q, hqledger] using hq0 i
  have hr : ∀ i, B i 0 + B i 1 + B i 2 = 0 := by
    intro i
    ext r s
    simpa [B, Fin.sum_univ_three] using hr0 i r s
  have hc : ∀ j, p 0 • B 0 j + p 1 • B 1 j + p 2 • B 2 j = 0 := by
    intro j
    ext r s
    simpa [B, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] using hc0 j r s
  obtain ⟨H, S, hH, hHS, hSH, hX⟩ := exists_ordered_sl2_split (B 0 1) sigma hs hroot
  have hdiag : ∀ i j, (S * B i j * H) 0 1 = 0 ∧ (S * B i j * H) 1 0 = 0 :=
    all_blocks_diagonal B p q (hpne 1) (hpne 2) hd hr hc H S hSH sigma hX
  let Q := matrixOfLinear (splitForward L p H)
  let N := matrixOfLinear (splitBackward L p S)
  obtain ⟨hQN', hNQ'⟩ := split_inverse L p hpne H S hHS hSH
  have hQN : Q * N = 1 := by
    apply matrixAction_injective
    rw [matrixAction_mul, matrixAction_matrixOfLinear, matrixAction_matrixOfLinear,
      hQN', matrixAction_one]
  have hNQ : N * Q = 1 := by
    apply matrixAction_injective
    rw [matrixAction_mul, matrixAction_matrixOfLinear, matrixAction_matrixOfLinear,
      hNQ', matrixAction_one]
  have hQ : Q.transpose * symplecticJ * Q = symplecticJ :=
    splitForward_symplectic E hEidem hEsum u v p hp hpne H hH
  have hN : N.transpose * symplecticJ * N = symplecticJ := by
    simpa using SimilitudeConjugation.inverse_form Q N (1 : K) hQN
      one_ne_zero (by simpa using hQ)
  have hE (i : Fin 3) : N * (E i : Mat6 K) * Q = grouped (diagonalUnit i) 0 0 := by
    have hecoord := coordinateConjugate_first_frame E hEidem hEsum u v p hp hpne i
    have ha : matrixAction (N * (E i : Mat6 K) * Q) = standardProjector i := by
      rw [matrixAction_mul, matrixAction_mul, matrixAction_matrixOfLinear,
        matrixAction_matrixOfLinear]
      change (planeScale p).comp
        (((commonPlaneMap S).comp
          ((coordinateConjugate L (matrixAction (E i : Mat6 K))).comp
            (commonPlaneMap H))).comp (planeScale (fun i => (p i)⁻¹))) = _
      have hcommon : (commonPlaneMap S).comp
          ((coordinateConjugate L (matrixAction (E i : Mat6 K))).comp
            (commonPlaneMap H)) = standardProjector i := by
        rw [hecoord, ← LinearMap.comp_assoc,
          commonPlaneMap_comm_standardProjector S i, LinearMap.comp_assoc,
          commonPlaneMap_comp S H hSH, LinearMap.comp_id]
      rw [hcommon, ← LinearMap.comp_assoc, planeScale_comm_standardProjector p i,
        LinearMap.comp_assoc,
        planeScale_comp p (fun i => (p i)⁻¹) (fun i => mul_inv_cancel₀ (hpne i)),
        LinearMap.comp_id]
    rw [← matrixOfLinear_matrixAction (N * (E i : Mat6 K) * Q), ha,
      standardProjector_matrix]
  have hF1 : N * (F 1 : Mat6 K) * Q =
      grouped (topLeft (N * (F 1 : Mat6 K) * Q)) 0 0 :=
    split_matrix_grouped L p H S (F 1) hdiag hNQ hN
  have hF0 : N * (F 0 : Mat6 K) * Q =
      grouped (topLeft (N * (F 0 : Mat6 K) * Q)) 0 0 := by
    apply split_matrix_grouped L p H S (F 0) _ hNQ hN
    intro i j
    rw [coordinateConjugate_first_projector E (F 0) hEidem hEsum
      u v p hp hpne hFu hFv]
    have hb : weightedBlock (weightedFirstAction p) i j = p j • (1 : Mat2 K) := by
      ext r s
      fin_cases r <;> fin_cases s <;>
        simp [weightedBlock, weightedPairIndex, weightedFirstAction, basisVector,
          Pi.single_apply, Matrix.one_apply]
    rw [hb, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hSH]
    simp
  let f : Fin 3 → Mat3 K := fun j => topLeft (N * (F j : Mat6 K) * Q)
  have hF2 : N * (F 2 : Mat6 K) * Q = grouped (f 2) 0 0 := by
    have hsum : N * (F 0 : Mat6 K) * Q + N * (F 1 : Mat6 K) * Q +
        N * (F 2 : Mat6 K) * Q = 1 := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.add_mul,
        ← Matrix.mul_add, hFsum, Matrix.mul_one, hNQ]
    have hz : topRight (N * (F 2 : Mat6 K) * Q) = 0 ∧
        bottomLeft (N * (F 2 : Mat6 K) * Q) = 0 := by
      constructor <;> ext i j
      · change (N * (F 2 : Mat6 K) * Q) (Sum.inl i) (Sum.inr j) = 0
        have h := congrFun (congrFun hsum (Sum.inl i)) (Sum.inr j)
        rw [hF0, hF1] at h
        simpa [grouped, hat_zero_matrix, Matrix.one_apply] using h
      · change (N * (F 2 : Mat6 K) * Q) (Sum.inr i) (Sum.inl j) = 0
        have h := congrFun (congrFun hsum (Sum.inr i)) (Sum.inl j)
        rw [hF0, hF1] at h
        simpa [grouped, hat_zero_matrix, Matrix.one_apply] using h
    have hmem := SimilitudeConjugation.conjugate_mem N Q (1 : K) hNQ
      (by simpa using hN) (F 2)
    have hg := grouped_extract _ hmem
    rw [hz.1, hz.2] at hg
    simpa only [unhat_zero_matrix, f] using hg.symm
  refine ⟨Q, N, f, hQN, hNQ, hQ, hE, ?_⟩
  intro j
  fin_cases j
  · exact hF0
  · exact hF1
  · exact hF2

private theorem actual_common_splitter_of_ordered_split
    (E F : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (hFidem : ∀ i, (F i : Mat6 K) * F i = F i)
    (hFsum : (F 0 : Mat6 K) + F 1 + F 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (SymplecticMatrixBridge.omega (K := K))
      (matrixAction (E i : Mat6 K) u) (matrixAction (E i : Mat6 K) v))
    (hpne : ∀ i, p i ≠ 0)
    (hFu : ∀ i, matrixAction (F 0 : Mat6 K) (matrixAction (E i : Mat6 K) u) = p i • u)
    (hFv : ∀ i, matrixAction (F 0 : Mat6 K) (matrixAction (E i : Mat6 K) v) = p i • v)
    (H S : Mat2 K) (hH : determinant H = 1)
    (hHS : H * S = 1) (hSH : S * H = 1) (sigma : K)
    (hX : let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
      let X := weightedBlock (coordinateConjugate L (matrixAction (F 1 : Mat6 K))) 0 1
      S * X * H = eigenvalues X sigma) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    let Q := matrixOfLinear (splitForward L p H)
    let N := matrixOfLinear (splitBackward L p S)
    ∃ f : Fin 3 → Mat3 K,
      Q * N = 1 ∧ N * Q = 1 ∧ Q.transpose * symplecticJ * Q = symplecticJ ∧
      (∀ i, N * (E i : Mat6 K) * Q = grouped (diagonalUnit i) 0 0) ∧
      (∀ j, N * (F j : Mat6 K) * Q = grouped (f j) 0 0) := by
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  let A := coordinateConjugate L (matrixAction (F 1 : Mat6 K))
  let B := fun i j => weightedBlock A i j
  have hz := actual_second_projector_weighted_zero_compositions
    E F hEidem hEsum hFidem hFsum u v p hp hpne hFu hFv
  dsimp only at hz
  obtain ⟨hr0, hc0⟩ := weighted_block_zero_sums A p (hpne 0) hz.1 hz.2
  have hd0 := actual_weighted_diagonal_scalar
    E (F 1) hEidem hEsum u v p hp hpne
  dsimp only at hd0
  choose q0 hq0 using hd0
  have hqledger (i : Fin 3) :
      q0 i = ProjectorBlockBridge.jordanTrace (K := K)
        ((E i : Mat6 K) * (F 1 : Mat6 K)) :=
    diagonal_scalar_eq_actual_pair_ledger
      E (F 1) hEidem hEsum u v p hp hpne i (q0 i) (hq0 i)
  let q : Fin 3 → K := fun i =>
    ProjectorBlockBridge.jordanTrace (K := K)
      ((E i : Mat6 K) * (F 1 : Mat6 K))
  have hd : ∀ i, B i i = scalar2 (q i) := by
    intro i
    change weightedBlock A i i = scalar2 (q i)
    simpa only [A, L, q, hqledger] using hq0 i
  have hr : ∀ i, B i 0 + B i 1 + B i 2 = 0 := by
    intro i
    ext r s
    simpa [B, Fin.sum_univ_three] using hr0 i r s
  have hc : ∀ j, p 0 • B 0 j + p 1 • B 1 j + p 2 • B 2 j = 0 := by
    intro j
    ext r s
    simpa [B, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] using hc0 j r s
  have hdiag : ∀ i j, (S * B i j * H) 0 1 = 0 ∧ (S * B i j * H) 1 0 = 0 :=
    all_blocks_diagonal B p q (hpne 1) (hpne 2) hd hr hc H S hSH sigma hX
  let Q := matrixOfLinear (splitForward L p H)
  let N := matrixOfLinear (splitBackward L p S)
  obtain ⟨hQN', hNQ'⟩ := split_inverse L p hpne H S hHS hSH
  have hQN : Q * N = 1 := by
    apply matrixAction_injective
    rw [matrixAction_mul, matrixAction_matrixOfLinear, matrixAction_matrixOfLinear,
      hQN', matrixAction_one]
  have hNQ : N * Q = 1 := by
    apply matrixAction_injective
    rw [matrixAction_mul, matrixAction_matrixOfLinear, matrixAction_matrixOfLinear,
      hNQ', matrixAction_one]
  have hQ : Q.transpose * symplecticJ * Q = symplecticJ :=
    splitForward_symplectic E hEidem hEsum u v p hp hpne H hH
  have hN : N.transpose * symplecticJ * N = symplecticJ := by
    simpa using SimilitudeConjugation.inverse_form Q N (1 : K) hQN
      one_ne_zero (by simpa using hQ)
  have hE (i : Fin 3) : N * (E i : Mat6 K) * Q = grouped (diagonalUnit i) 0 0 := by
    have hecoord := coordinateConjugate_first_frame E hEidem hEsum u v p hp hpne i
    have ha : matrixAction (N * (E i : Mat6 K) * Q) = standardProjector i := by
      rw [matrixAction_mul, matrixAction_mul, matrixAction_matrixOfLinear,
        matrixAction_matrixOfLinear]
      change (planeScale p).comp
        (((commonPlaneMap S).comp
          ((coordinateConjugate L (matrixAction (E i : Mat6 K))).comp
            (commonPlaneMap H))).comp (planeScale (fun i => (p i)⁻¹))) = _
      have hcommon : (commonPlaneMap S).comp
          ((coordinateConjugate L (matrixAction (E i : Mat6 K))).comp
            (commonPlaneMap H)) = standardProjector i := by
        rw [hecoord, ← LinearMap.comp_assoc,
          commonPlaneMap_comm_standardProjector S i, LinearMap.comp_assoc,
          commonPlaneMap_comp S H hSH, LinearMap.comp_id]
      rw [hcommon, ← LinearMap.comp_assoc, planeScale_comm_standardProjector p i,
        LinearMap.comp_assoc,
        planeScale_comp p (fun i => (p i)⁻¹) (fun i => mul_inv_cancel₀ (hpne i)),
        LinearMap.comp_id]
    rw [← matrixOfLinear_matrixAction (N * (E i : Mat6 K) * Q), ha,
      standardProjector_matrix]
  have hF1 : N * (F 1 : Mat6 K) * Q =
      grouped (topLeft (N * (F 1 : Mat6 K) * Q)) 0 0 :=
    split_matrix_grouped L p H S (F 1) hdiag hNQ hN
  have hF0 : N * (F 0 : Mat6 K) * Q =
      grouped (topLeft (N * (F 0 : Mat6 K) * Q)) 0 0 := by
    apply split_matrix_grouped L p H S (F 0) _ hNQ hN
    intro i j
    rw [coordinateConjugate_first_projector E (F 0) hEidem hEsum
      u v p hp hpne hFu hFv]
    have hb : weightedBlock (weightedFirstAction p) i j = p j • (1 : Mat2 K) := by
      ext r s
      fin_cases r <;> fin_cases s <;>
        simp [weightedBlock, weightedPairIndex, weightedFirstAction, basisVector,
          Pi.single_apply, Matrix.one_apply]
    rw [hb, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hSH]
    simp
  let f : Fin 3 → Mat3 K := fun j => topLeft (N * (F j : Mat6 K) * Q)
  have hF2 : N * (F 2 : Mat6 K) * Q = grouped (f 2) 0 0 := by
    have hsum : N * (F 0 : Mat6 K) * Q + N * (F 1 : Mat6 K) * Q +
        N * (F 2 : Mat6 K) * Q = 1 := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.add_mul,
        ← Matrix.mul_add, hFsum, Matrix.mul_one, hNQ]
    have hz : topRight (N * (F 2 : Mat6 K) * Q) = 0 ∧
        bottomLeft (N * (F 2 : Mat6 K) * Q) = 0 := by
      constructor <;> ext i j
      · change (N * (F 2 : Mat6 K) * Q) (Sum.inl i) (Sum.inr j) = 0
        have h := congrFun (congrFun hsum (Sum.inl i)) (Sum.inr j)
        rw [hF0, hF1] at h
        simpa [grouped, hat_zero_matrix, Matrix.one_apply] using h
      · change (N * (F 2 : Mat6 K) * Q) (Sum.inr i) (Sum.inl j) = 0
        have h := congrFun (congrFun hsum (Sum.inr i)) (Sum.inl j)
        rw [hF0, hF1] at h
        simpa [grouped, hat_zero_matrix, Matrix.one_apply] using h
    have hmem := SimilitudeConjugation.conjugate_mem N Q (1 : K) hNQ
      (by simpa using hN) (F 2)
    have hg := grouped_extract _ hmem
    rw [hz.1, hz.2] at hg
    simpa only [unhat_zero_matrix, f] using hg.symm
  refine ⟨f, hQN, hNQ, hQ, hE, ?_⟩
  intro j
  fin_cases j
  · exact hF0
  · exact hF1
  · exact hF2

/-- A supplied cyclic vector constructs the ordered basis used by the actual
splitter. Its cyclic determinant is the only extra open condition.
@isnad1 id=other.9h10v.s13.6fdf851ec596 from=translated src=- shape=31d524ed vocab=d267fdee
-/
theorem actual_common_splitter_of_cyclic_vector
    (E F : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (hFidem : ∀ i, (F i : Mat6 K) * F i = F i)
    (hFsum : (F 0 : Mat6 K) + F 1 + F 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (SymplecticMatrixBridge.omega (K := K))
      (matrixAction (E i : Mat6 K) u) (matrixAction (E i : Mat6 K) v))
    (hpne : ∀ i, p i ≠ 0)
    (hFu : ∀ i, matrixAction (F 0 : Mat6 K) (matrixAction (E i : Mat6 K) u) = p i • u)
    (hFv : ∀ i, matrixAction (F 0 : Mat6 K) (matrixAction (E i : Mat6 K) v) = p i • v)
    (w : Vec2 K) (sigma : K) (hs : sigma ≠ 0)
    (hroot : let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
      let X := weightedBlock (coordinateConjugate L (matrixAction (F 1 : Mat6 K))) 0 1
      sigma ^ 2 = trace2 X ^ 2 - 4 * determinant X)
    (hw : let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
      let X := weightedBlock (coordinateConjugate L (matrixAction (F 1 : Mat6 K))) 0 1
      cyclicDet X w ≠ 0) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    let X := weightedBlock (coordinateConjugate L (matrixAction (F 1 : Mat6 K))) 0 1
    let H := cyclicSplitBasis X sigma w
    let S := inverseSL H
    let Q := matrixOfLinear (splitForward L p H)
    let N := matrixOfLinear (splitBackward L p S)
    ∃ f : Fin 3 → Mat3 K,
      Q * N = 1 ∧ N * Q = 1 ∧ Q.transpose * symplecticJ * Q = symplecticJ ∧
      (∀ i, N * (E i : Mat6 K) * Q = grouped (diagonalUnit i) 0 0) ∧
      (∀ j, N * (F j : Mat6 K) * Q = grouped (f j) 0 0) := by
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  let X := weightedBlock (coordinateConjugate L (matrixAction (F 1 : Mat6 K))) 0 1
  let H := cyclicSplitBasis X sigma w
  let S := inverseSL H
  have hH : determinant H = 1 := cyclicSplitBasis_det X sigma w hs hw
  have hHS : H * S = 1 := mul_inverseSL H hH
  have hSH : S * H = 1 := inverseSL_mul H hH
  have hX : S * X * H = eigenvalues X sigma := by
    rw [Matrix.mul_assoc, cyclicSplitBasis_intertwines X sigma w hroot,
      ← Matrix.mul_assoc, hSH, Matrix.one_mul]
  exact actual_common_splitter_of_ordered_split
    E F hEidem hEsum hFidem hFsum u v p hp hpne hFu hFv
    H S hH hHS hSH sigma hX

end AlbertLean.Generic.QuaternionRow.CommonSplitBasis
