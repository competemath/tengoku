import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedFirstProjectorMatrix

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms coordinateConjugate_first_projector` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms actual_second_projector_weighted_zero_compositions` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms weighted_block_zero_sums` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms actual_weighted_block_adjoint` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms actual_weighted_diagonal_scalar` (it only prints; the queue checks the axioms of every declaration). -/

/-! Actual second-projector identities consumed by Q1's weighted block algebra. -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.SymplecticProjectorFrame
open AlbertLean.Generic.SymplecticTransvection

universe u
variable {K : Type u} [Field K] [CharZero K]

def coordinateConjugate (L : Vec6 K ≃ₗ[K] Vec6 K) (T : Vec6 K →ₗ[K] Vec6 K) :
    Vec6 K →ₗ[K] Vec6 K := L.symm.toLinearMap.comp (T.comp L.toLinearMap)

def weightedPairIndex (i : Fin 3) : Fin 2 → Ix6
  | 0 => Sum.inl i
  | 1 => Sum.inr i

def weightedBlock (B : Vec6 K →ₗ[K] Vec6 K) (i j : Fin 3) :
    Matrix (Fin 2) (Fin 2) K := fun r s =>
  B (basisVector (weightedPairIndex j s)) (weightedPairIndex i r)

def adj2 (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  ![![A 1 1, -A 0 1], ![-A 1 0, A 0 0]]

def scalar2 (q : K) : Matrix (Fin 2) (Fin 2) K := q • 1

/--
@isnad1 id=eq.0h4v.s9.927f3aef38a6 from=translated src=- shape=da28f280 vocab=5c6c7379
-/
theorem coordinateConjugate_comp
    (L : Vec6 K ≃ₗ[K] Vec6 K) (A B : Vec6 K →ₗ[K] Vec6 K) :
    coordinateConjugate L (A.comp B) =
      (coordinateConjugate L A).comp (coordinateConjugate L B) := by
  apply LinearMap.ext
  intro x
  simp [coordinateConjugate, LinearMap.comp_apply]

/--
@isnad1 id=eq.0h2v.s9.5323c8fec6fd from=translated src=- shape=48989f0e vocab=db5319dc
-/
theorem coordinateConjugate_zero
    (L : Vec6 K ≃ₗ[K] Vec6 K) :
    coordinateConjugate L (0 : Vec6 K →ₗ[K] Vec6 K) = 0 := by
  apply LinearMap.ext
  intro x
  simp [coordinateConjugate]

/--
@isnad1 id=eq.6h6v.s12.16e1940e937d from=translated src=- shape=bc48679b vocab=a3d5704a
-/
theorem coordinateConjugate_first_projector
    (E : Fin 3 → Carrier K) (F0 : Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v)) (hpne : ∀ i, p i ≠ 0)
    (hFu : ∀ i, matrixAction (F0 : Mat6 K)
      (matrixAction (E i : Mat6 K) u) = p i • u)
    (hFv : ∀ i, matrixAction (F0 : Mat6 K)
      (matrixAction (E i : Mat6 K) v) = p i • v) :
    coordinateConjugate
      (weightedCoordinateEquiv E hEidem hEsum u v p hp hpne)
      (matrixAction (F0 : Mat6 K)) = weightedFirstAction p := by
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  have hinter := first_projector_intertwines_weighted_coordinates
    E F0 hEsum u v p hFu hFv
  apply LinearMap.ext
  intro x
  change L.symm (matrixAction (F0 : Mat6 K) (L x)) = weightedFirstAction p x
  have hx := LinearMap.congr_fun hinter x
  change matrixAction (F0 : Mat6 K) (L x) = L (weightedFirstAction p x) at hx
  rw [hx, L.symm_apply_apply]

/-- The two zero-composition equations are derived from the actual `F` frame
before any block algebra is invoked.
@isnad1 id=other.8h6v.s13.71bd190ca77a from=translated src=- shape=050de6e9 vocab=807210ed
-/
theorem actual_second_projector_weighted_zero_compositions
    (E F : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (hFidem : ∀ i, (F i : Mat6 K) * F i = F i)
    (hFsum : (F 0 : Mat6 K) + F 1 + F 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v)) (hpne : ∀ i, p i ≠ 0)
    (hFu : ∀ i, matrixAction (F 0 : Mat6 K)
      (matrixAction (E i : Mat6 K) u) = p i • u)
    (hFv : ∀ i, matrixAction (F 0 : Mat6 K)
      (matrixAction (E i : Mat6 K) v) = p i • v) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    let B := coordinateConjugate L (matrixAction (F 1 : Mat6 K))
    B.comp (weightedFirstAction p) = 0 ∧
      (weightedFirstAction p).comp B = 0 := by
  let Q : Fin 3 → Vec6 K →ₗ[K] Vec6 K :=
    fun i => matrixAction (K := K) (F i : Mat6 K)
  have hQi : ∀ i, IsIdempotent (Q i) :=
    fun i => carrier_projector_action_idempotent (F i) (hFidem i)
  have hQsum : Q 0 + Q 1 + Q 2 = LinearMap.id :=
    carrier_frame_action_sum F hFsum
  have h10 := comp_zero_of_complete_frame Q hQi hQsum 1 0 (by decide)
  have h01 := comp_zero_of_complete_frame Q hQi hQsum 0 1 (by decide)
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  have hP := coordinateConjugate_first_projector E (F 0) hEidem hEsum
    u v p hp hpne hFu hFv
  dsimp only
  constructor
  · rw [← hP, ← coordinateConjugate_comp, h10,
      coordinateConjugate_zero]
  · rw [← hP, ← coordinateConjugate_comp, h01,
      coordinateConjugate_zero]

/-- The action-level zero products give the row and weighted-column block
relations used by `QuaternionWeightedBlockEquations`.
@isnad1 id=and.3h3v.s10.9a9a8a2c346c from=translated src=- shape=e7da50e1 vocab=0b0aff30
-/
theorem weighted_block_zero_sums
    (B : Vec6 K →ₗ[K] Vec6 K) (p : Fin 3 → K) (hp0 : p 0 ≠ 0)
    (hrow : B.comp (weightedFirstAction p) = 0)
    (hcol : (weightedFirstAction p).comp B = 0) :
    (∀ i r s, ∑ j, weightedBlock B i j r s = 0) ∧
      (∀ j r s, ∑ i, p i * weightedBlock B i j r s = 0) := by
  have hfirst (s : Fin 2) :
      weightedFirstAction p (basisVector (weightedPairIndex 0 s)) =
        p 0 • ∑ j : Fin 3, basisVector (weightedPairIndex j s) := by
    funext q
    fin_cases s <;> rcases q with q | q <;> fin_cases q <;>
      simp [weightedFirstAction, weightedPairIndex, basisVector,
        Pi.single_apply, Fin.sum_univ_succ]
  constructor
  · intro i r s
    have h := congrFun (LinearMap.congr_fun hrow
      (basisVector (weightedPairIndex 0 s))) (weightedPairIndex i r)
    rw [LinearMap.comp_apply, hfirst, map_smul, map_sum] at h
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
    fin_cases r <;> fin_cases s
    all_goals
      simp [LinearMap.comp_apply, weightedFirstAction, weightedBlock,
        weightedPairIndex, basisVector, Pi.single_apply,
        Fin.sum_univ_succ] at h ⊢
      exact h.resolve_left hp0
  · intro j r s
    have h := congrFun (LinearMap.congr_fun hcol
      (basisVector (weightedPairIndex j s))) (weightedPairIndex 0 r)
    fin_cases r <;> fin_cases s
    all_goals
      simpa [LinearMap.comp_apply, weightedFirstAction, weightedBlock,
        weightedPairIndex, basisVector, Pi.single_apply,
        Fin.sum_univ_succ] using h

/--
@isnad1 id=eq.0h5v.s9.cb3aae2cac8c from=translated src=- shape=9471e622 vocab=2dc89f89
-/
theorem weightedCoordinateLinear_basis_left
    (E : Fin 3 → Carrier K) (u v : Vec6 K) (i : Fin 3) :
    weightedCoordinateLinear E u v (basisVector (Sum.inl i)) =
      matrixAction (E i : Mat6 K) u := by
  funext q
  fin_cases i <;> rcases q with q | q <;> fin_cases q <;>
    simp [weightedCoordinateLinear, basisVector, Pi.single_apply,
      Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h5v.s9.09398722cc5d from=translated src=- shape=a28f256c vocab=3b3fff4b
-/
theorem weightedCoordinateLinear_basis_right
    (E : Fin 3 → Carrier K) (u v : Vec6 K) (i : Fin 3) :
    weightedCoordinateLinear E u v (basisVector (Sum.inr i)) =
      matrixAction (E i : Mat6 K) v := by
  funext q
  fin_cases i <;> rcases q with q | q <;> fin_cases q <;>
    simp [weightedCoordinateLinear, basisVector, Pi.single_apply,
      Fin.sum_univ_succ]

/-- Pairing with the two vectors of plane `i` extracts the two weighted
coordinates.
@isnad1 id=and.3h7v.s12.fce7e4a691b7 from=translated src=- shape=7b11d0b0 vocab=fe3995d1
-/
theorem weighted_pairing_extract
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v)) (z : Vec6 K) (i : Fin 3) :
    (omega (K := K)) (weightedCoordinateLinear E u v z)
        (matrixAction (E i : Mat6 K) v) = z (Sum.inl i) * p i ∧
      (omega (K := K)) (weightedCoordinateLinear E u v z)
        (matrixAction (E i : Mat6 K) u) = -(z (Sum.inr i) * p i) := by
  obtain ⟨huv, huu, hvv⟩ := weighted_pairings E hEidem hEsum u v p hp
  have hrev (j : Fin 3) :
      (omega (K := K)) (matrixAction (E j : Mat6 K) v)
        (matrixAction (E i : Mat6 K) u) =
        if j = i then -(p j) else 0 := by
    by_cases hji : j = i
    · subst i
      rw [ite_eq_left rfl]
      exact skew_of_alternating (omega (K := K)) omega_alternating _ _ |>.trans
        (by rw [← hp j])
    · rw [ite_eq_right hji]
      exact carrier_frame_images_orthogonal E hEidem hEsum hji v u
  constructor
  · simp [weightedCoordinateLinear, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, huv, hvv]
  · simp [weightedCoordinateLinear, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, huu, hrev]

/--
@isnad1 id=and.3h7v.s12.18f63d580cc4 from=translated src=- shape=dcde8d35 vocab=fe3995d1
-/
theorem weighted_pairing_extract_reverse
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v)) (z : Vec6 K) (i : Fin 3) :
    (omega (K := K)) (matrixAction (E i : Mat6 K) u)
        (weightedCoordinateLinear E u v z) = z (Sum.inr i) * p i ∧
      (omega (K := K)) (matrixAction (E i : Mat6 K) v)
        (weightedCoordinateLinear E u v z) = -(z (Sum.inl i) * p i) := by
  obtain ⟨h1, h2⟩ := weighted_pairing_extract E hEidem hEsum u v p hp z i
  constructor
  · rw [skew_of_alternating (omega (K := K)) omega_alternating]
    linear_combination -h2
  · rw [skew_of_alternating (omega (K := K)) omega_alternating]
    linear_combination -h1

/-- Actual self-adjointness of `F1`, transported through the weighted
coordinate equivalence, gives the correctly oriented block adjoint law.
@isnad1 id=other.4h6v.s11.7f0e1c8b8ed8 from=translated src=- shape=11f7158e vocab=6380bb5c
-/
theorem actual_weighted_block_adjoint
    (E : Fin 3 → Carrier K) (F1 : Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v)) (hpne : ∀ i, p i ≠ 0) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    let B := coordinateConjugate L (matrixAction (F1 : Mat6 K))
    ∀ i j, p i • weightedBlock B i j = p j • adj2 (weightedBlock B j i) := by
  dsimp only
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  let B := coordinateConjugate L (matrixAction (F1 : Mat6 K))
  have hinter (z : Vec6 K) :
      weightedCoordinateLinear E u v (B z) =
        matrixAction (F1 : Mat6 K) (weightedCoordinateLinear E u v z) := by
    change L (B z) = matrixAction (F1 : Mat6 K) (L z)
    simp [B, coordinateConjugate]
  intro i j
  ext r s
  fin_cases r <;> fin_cases s
  · have hs := carrier_action_selfAdjoint F1
      (weightedCoordinateLinear E u v (basisVector (weightedPairIndex j 0)))
      (weightedCoordinateLinear E u v (basisVector (weightedPairIndex i 1)))
    rw [← hinter, ← hinter] at hs
    simp only [weightedPairIndex, weightedCoordinateLinear_basis_left,
      weightedCoordinateLinear_basis_right] at hs
    have hl := (weighted_pairing_extract E hEidem hEsum u v p hp
      (B (basisVector (weightedPairIndex j 0))) i).1
    have hr := (weighted_pairing_extract_reverse E hEidem hEsum u v p hp
      (B (basisVector (weightedPairIndex i 1))) j).1
    simp only [weightedPairIndex] at hl hr
    rw [hl, hr] at hs
    change p i * B (basisVector (weightedPairIndex j 0)) (weightedPairIndex i 0) =
      p j * B (basisVector (weightedPairIndex i 1)) (weightedPairIndex j 1)
    simp only [weightedPairIndex]
    linear_combination hs
  · have hs := carrier_action_selfAdjoint F1
      (weightedCoordinateLinear E u v (basisVector (weightedPairIndex j 1)))
      (weightedCoordinateLinear E u v (basisVector (weightedPairIndex i 1)))
    rw [← hinter, ← hinter] at hs
    simp only [weightedPairIndex, weightedCoordinateLinear_basis_left,
      weightedCoordinateLinear_basis_right] at hs
    have hl := (weighted_pairing_extract E hEidem hEsum u v p hp
      (B (basisVector (weightedPairIndex j 1))) i).1
    have hr := (weighted_pairing_extract_reverse E hEidem hEsum u v p hp
      (B (basisVector (weightedPairIndex i 1))) j).2
    simp only [weightedPairIndex] at hl hr
    rw [hl, hr] at hs
    change p i * B (basisVector (weightedPairIndex j 1)) (weightedPairIndex i 0) =
      p j * (-B (basisVector (weightedPairIndex i 1)) (weightedPairIndex j 0))
    simp only [weightedPairIndex]
    linear_combination hs
  · have hs := carrier_action_selfAdjoint F1
      (weightedCoordinateLinear E u v (basisVector (weightedPairIndex j 0)))
      (weightedCoordinateLinear E u v (basisVector (weightedPairIndex i 0)))
    rw [← hinter, ← hinter] at hs
    simp only [weightedPairIndex, weightedCoordinateLinear_basis_left,
      weightedCoordinateLinear_basis_right] at hs
    have hl := (weighted_pairing_extract E hEidem hEsum u v p hp
      (B (basisVector (weightedPairIndex j 0))) i).2
    have hr := (weighted_pairing_extract_reverse E hEidem hEsum u v p hp
      (B (basisVector (weightedPairIndex i 0))) j).1
    simp only [weightedPairIndex] at hl hr
    rw [hl, hr] at hs
    change p i * B (basisVector (weightedPairIndex j 0)) (weightedPairIndex i 1) =
      p j * (-B (basisVector (weightedPairIndex i 0)) (weightedPairIndex j 1))
    simp only [weightedPairIndex]
    linear_combination -hs
  · have hs := carrier_action_selfAdjoint F1
      (weightedCoordinateLinear E u v (basisVector (weightedPairIndex j 1)))
      (weightedCoordinateLinear E u v (basisVector (weightedPairIndex i 0)))
    rw [← hinter, ← hinter] at hs
    simp only [weightedPairIndex, weightedCoordinateLinear_basis_left,
      weightedCoordinateLinear_basis_right] at hs
    have hl := (weighted_pairing_extract E hEidem hEsum u v p hp
      (B (basisVector (weightedPairIndex j 1))) i).2
    have hr := (weighted_pairing_extract_reverse E hEidem hEsum u v p hp
      (B (basisVector (weightedPairIndex i 0))) j).2
    simp only [weightedPairIndex] at hl hr
    rw [hl, hr] at hs
    change p i * B (basisVector (weightedPairIndex j 1)) (weightedPairIndex i 1) =
      p j * B (basisVector (weightedPairIndex i 0)) (weightedPairIndex j 0)
    simp only [weightedPairIndex]
    linear_combination -hs

/--
@isnad1 id=other.4h6v.s11.ca6ca14bb233 from=translated src=- shape=52261417 vocab=25a6099f
-/
theorem actual_weighted_diagonal_scalar
    (E : Fin 3 → Carrier K) (F1 : Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v)) (hpne : ∀ i, p i ≠ 0) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    let B := coordinateConjugate L (matrixAction (F1 : Mat6 K))
    ∀ i, ∃ q : K, weightedBlock B i i = scalar2 q := by
  dsimp only
  intro i
  have h := actual_weighted_block_adjoint E F1 hEidem hEsum u v p hp hpne i i
  have hself : weightedBlock
      (coordinateConjugate (weightedCoordinateEquiv E hEidem hEsum u v p hp hpne)
        (matrixAction (F1 : Mat6 K))) i i =
      adj2 (weightedBlock
        (coordinateConjugate (weightedCoordinateEquiv E hEidem hEsum u v p hp hpne)
          (matrixAction (F1 : Mat6 K))) i i) :=
    (smul_right_injective _ (hpne i)) h
  refine ⟨weightedBlock
    (coordinateConjugate (weightedCoordinateEquiv E hEidem hEsum u v p hp hpne)
      (matrixAction (F1 : Mat6 K))) i i 0 0, ?_⟩
  ext r s
  fin_cases r <;> fin_cases s
  · simp [scalar2, Matrix.smul_apply, Matrix.one_apply]
  · have hrs := congrFun (congrFun hself 0) 1
    simp [adj2, scalar2, Matrix.smul_apply, Matrix.one_apply] at hrs ⊢
    linear_combination (1 / 2 : K) * hrs
  · have hrs := congrFun (congrFun hself 1) 0
    simp [adj2, scalar2, Matrix.smul_apply, Matrix.one_apply] at hrs ⊢
    linear_combination (1 / 2 : K) * hrs
  · have hrs := congrFun (congrFun hself 1) 1
    simpa [adj2, scalar2, Matrix.smul_apply, Matrix.one_apply] using hrs

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
