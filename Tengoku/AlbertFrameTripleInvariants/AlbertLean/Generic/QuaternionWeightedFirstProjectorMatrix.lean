import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedCoordinateInjectivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms weightedFirstAction` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrixAction_weightedFirstMatrix` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms first_projector_intertwines_weighted_coordinates` (it only prints; the queue checks the axioms of every declaration). -/

/-! Literal weighted first-projector matrix consumed by Q1. -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The matrix action having every two-by-two block in column `j` equal to
`p_j I`, in the literal grouped coordinate order.-/
def weightedFirstAction (p : Fin 3 → K) : Vec6 K →ₗ[K] Vec6 K where
  toFun z
    | Sum.inl _ => ∑ j, p j * z (Sum.inl j)
    | Sum.inr _ => ∑ j, p j * z (Sum.inr j)
  map_add' := by
    intro x y
    funext q
    rcases q with i | i <;>
      simp only [Pi.add_apply, Finset.mul_sum, mul_add,
        Finset.sum_add_distrib]
  map_smul' := by
    intro t x
    funext q
    rcases q with i | i <;>
      simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    all_goals
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The same operator as a literal grouped `6×6` matrix.  Its diagonal-kind
entries in block column `j` are `p_j` and its mixed-kind entries are zero.-/
def weightedFirstMatrix (p : Fin 3 → K) : Mat6 K
  | Sum.inl _, Sum.inl j => p j
  | Sum.inr _, Sum.inr j => p j
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0

/--
@isnad1 id=eq.0h2v.s7.68f46dfe01e3 from=translated src=- shape=43f5e8e6 vocab=e8471c2e
-/
theorem matrixAction_weightedFirstMatrix (p : Fin 3 → K) :
    matrixAction (weightedFirstMatrix p) = weightedFirstAction p := by
  apply LinearMap.ext
  intro z
  funext q
  rcases q with i | i <;>
    simp [matrixAction, weightedFirstMatrix, weightedFirstAction,
      Fintype.sum_sum_type]

/-- Actual compression identities force the first projector to have literal
weighted block columns `p_j I` under the genuine weighted coordinate map.
@isnad1 id=eq.3h6v.s11.f81a6c97e363 from=translated src=- shape=135218be vocab=d44a8b77
-/
theorem first_projector_intertwines_weighted_coordinates
    (E : Fin 3 → Carrier K) (F0 : Carrier K)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hFu : ∀ i, matrixAction (F0 : Mat6 K)
      (matrixAction (E i : Mat6 K) u) = p i • u)
    (hFv : ∀ i, matrixAction (F0 : Mat6 K)
      (matrixAction (E i : Mat6 K) v) = p i • v) :
    (matrixAction (F0 : Mat6 K)).comp (weightedCoordinateLinear E u v) =
      (weightedCoordinateLinear E u v).comp (weightedFirstAction p) := by
  have hsumAction :
      matrixAction (E 0 : Mat6 K) + matrixAction (E 1 : Mat6 K) +
        matrixAction (E 2 : Mat6 K) = LinearMap.id :=
    carrier_frame_action_sum E hEsum
  have hu : u = ∑ i, matrixAction (E i : Mat6 K) u := by
    have h := LinearMap.congr_fun hsumAction u
    simpa only [LinearMap.add_apply, LinearMap.id_apply,
      Fin.sum_univ_three, add_assoc] using h.symm
  have hv : v = ∑ i, matrixAction (E i : Mat6 K) v := by
    have h := LinearMap.congr_fun hsumAction v
    simpa only [LinearMap.add_apply, LinearMap.id_apply,
      Fin.sum_univ_three, add_assoc] using h.symm
  apply LinearMap.ext
  intro z
  change matrixAction (F0 : Mat6 K)
      ((∑ i, z (Sum.inl i) • matrixAction (E i : Mat6 K) u) +
        ∑ i, z (Sum.inr i) • matrixAction (E i : Mat6 K) v) =
    (∑ i, (∑ j, p j * z (Sum.inl j)) • matrixAction (E i : Mat6 K) u) +
      ∑ i, (∑ j, p j * z (Sum.inr j)) • matrixAction (E i : Mat6 K) v
  simp only [map_add, map_sum, map_smul, hFu, hFv]
  simp only [smul_smul]
  apply congrArg₂ (· + ·)
  · calc
      (∑ i, (z (Sum.inl i) * p i) • u) =
          (∑ i, p i * z (Sum.inl i)) • u := by
            rw [← Finset.sum_smul]
            simp only [mul_comm]
      _ = ∑ i, (∑ j, p j * z (Sum.inl j)) •
          matrixAction (E i : Mat6 K) u := by
            conv_lhs => rw [hu]
            rw [Finset.smul_sum]
  · calc
      (∑ i, (z (Sum.inr i) * p i) • v) =
          (∑ i, p i * z (Sum.inr i)) • v := by
            rw [← Finset.sum_smul]
            simp only [mul_comm]
      _ = ∑ i, (∑ j, p j * z (Sum.inr j)) •
          matrixAction (E i : Mat6 K) v := by
            conv_lhs => rw [hv]
            rw [Finset.smul_sum]

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
