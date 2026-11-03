import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualWeightedSecondProjector
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedBlockSpectralData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms linear_apply_eq_sum_basis` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms weightedBlock_comp` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms actual_weighted_block_idempotent` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms actual_weighted_pivot_idempotent` (it only prints; the queue checks the axioms of every declaration). -/

/-! The actual idempotence-to-block-product attachment for Q1. -/
noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.QuaternionRow.ActualFrameCoverage

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Expansion of a linear map on the literal grouped coordinate basis.
@isnad1 id=eq.0h3v.s10.78ffb94f68a8 from=translated src=- shape=152d9ca2 vocab=d19fc7aa
-/
theorem linear_apply_eq_sum_basis (A : Vec6 K →ₗ[K] Vec6 K) (x : Vec6 K) :
    A x = (∑ i, x (Sum.inl i) • A (basisVector (Sum.inl i))) +
      ∑ i, x (Sum.inr i) • A (basisVector (Sum.inr i)) := by
  obtain ⟨a, b, hx⟩ := standard_spans (K := K) x
  have ha : a = fun i => x (Sum.inl i) := by
    funext i
    have hi := congrFun hx (Sum.inl i)
    fin_cases i <;>
      simpa [standardE, standardF, basisVector, Pi.single_apply,
        Fin.sum_univ_succ] using hi.symm
  have hb : b = fun i => x (Sum.inr i) := by
    funext i
    have hi := congrFun hx (Sum.inr i)
    fin_cases i <;>
      simpa [standardE, standardF, basisVector, Pi.single_apply,
        Fin.sum_univ_succ] using hi.symm
  subst a
  subst b
  calc
    A x = A ((∑ i, x (Sum.inl i) • standardE i) +
        ∑ i, x (Sum.inr i) • standardF i) := congrArg A hx
    _ = _ := by simp only [map_add, map_sum, map_smul, standardE, standardF]

/-- Composition is ordinary `3×3` block multiplication with `2×2` entries
in the exact grouped `(inl i,inr i)` plane convention.
@isnad1 id=eq.0h5v.s9.48786e5e8890 from=translated src=- shape=d4d2a627 vocab=eccb8719
-/
theorem weightedBlock_comp (A B : Vec6 K →ₗ[K] Vec6 K) (i l : Fin 3) :
    weightedBlock (A.comp B) i l =
      ∑ j, weightedBlock A i j * weightedBlock B j l := by
  ext r s
  have h := congrFun (linear_apply_eq_sum_basis A
    (B (basisVector (weightedPairIndex l s)))) (weightedPairIndex i r)
  fin_cases r <;> fin_cases s <;>
    simp [weightedBlock, weightedPairIndex, LinearMap.comp_apply,
      Finset.sum_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      Finset.sum_add_distrib,
      LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul] at h ⊢ <;> linear_combination h

/-- Actual projector idempotence supplies every block row-column product
identity after transport to weighted coordinates.
@isnad1 id=other.5h6v.s12.417070091c36 from=translated src=- shape=b29106d7 vocab=b2edbbf1
-/
theorem actual_weighted_block_idempotent
    (E : Fin 3 → Carrier K) (F1 : Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v)) (hpne : ∀ i, p i ≠ 0)
    (hFidem : (F1 : Mat6 K) * F1 = F1) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    let B := coordinateConjugate L (matrixAction (F1 : Mat6 K))
    ∀ i l, (∑ j, weightedBlock B i j * weightedBlock B j l) =
      weightedBlock B i l := by
  dsimp only
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  let B := coordinateConjugate L (matrixAction (F1 : Mat6 K))
  have hact : (matrixAction (F1 : Mat6 K)).comp
      (matrixAction (F1 : Mat6 K)) = matrixAction (F1 : Mat6 K) := by
    rw [← matrixAction_mul]
    exact congrArg (matrixAction (K := K)) hFidem
  have hB : B.comp B = B := by
    rw [← coordinateConjugate_comp, hact]
  intro i l
  rw [← weightedBlock_comp B B i l, hB]

/-- The exact pivot equation expected by `pivot_determinant_relation`.
@isnad1 id=other.5h6v.s12.5bd35f93a693 from=translated src=- shape=4c4a84f2 vocab=447eeb27
-/
theorem actual_weighted_pivot_idempotent
    (E : Fin 3 → Carrier K) (F1 : Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v)) (hpne : ∀ i, p i ≠ 0)
    (hFidem : (F1 : Mat6 K) * F1 = F1) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    let B := fun i j => weightedBlock
      (coordinateConjugate L (matrixAction (F1 : Mat6 K))) i j
    B 0 0 * B 0 0 + B 0 1 * B 1 0 + B 0 2 * B 2 0 = B 0 0 := by
  dsimp only
  have h := actual_weighted_block_idempotent E F1 hEidem hEsum
    u v p hp hpne hFidem 0 0
  simpa [Fin.sum_univ_three] using h

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
