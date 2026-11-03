import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedPlaneCommutation
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedCommonPlaneAut

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms commonPlaneJordanAut_apply_coe` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms commonPlaneJordanAut_maps_of_action` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.BlockEigenbasis
open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.QuaternionRow.WordMatrixConnection
variable {K : Type*} [Field K] [CharZero K]

/-- The forward and backward vector maps used internally by the common-plane
Jordan automorphism, exposed without changing that constructor.-/
def commonPlaneForward
    (E E' : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (hEidem' : ∀ i, (E' i : Mat6 K) * E' i = E' i)
    (hEsum' : (E' 0 : Mat6 K) + E' 1 + E' 2 = 1)
    (u v u' v' : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u) (matrixAction (E i : Mat6 K) v))
    (hp' : ∀ i, p i = (omega (K := K)) (matrixAction (E' i : Mat6 K) u') (matrixAction (E' i : Mat6 K) v'))
    (hpne : ∀ i, p i ≠ 0) (S : Mat2 K) : Vec6 K →ₗ[K] Vec6 K :=
  (weightedCoordinateEquiv E' hEidem' hEsum' u' v' p hp' hpne).toLinearMap.comp
    ((commonPlaneMap S).comp
      (weightedCoordinateEquiv E hEidem hEsum u v p hp hpne).symm.toLinearMap)

def commonPlaneBackward
    (E E' : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (hEidem' : ∀ i, (E' i : Mat6 K) * E' i = E' i)
    (hEsum' : (E' 0 : Mat6 K) + E' 1 + E' 2 = 1)
    (u v u' v' : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u) (matrixAction (E i : Mat6 K) v))
    (hp' : ∀ i, p i = (omega (K := K)) (matrixAction (E' i : Mat6 K) u') (matrixAction (E' i : Mat6 K) v'))
    (hpne : ∀ i, p i ≠ 0) (T : Mat2 K) : Vec6 K →ₗ[K] Vec6 K :=
  (weightedCoordinateEquiv E hEidem hEsum u v p hp hpne).toLinearMap.comp
    ((commonPlaneMap T).comp
      (weightedCoordinateEquiv E' hEidem' hEsum' u' v' p hp' hpne).symm.toLinearMap)

/-- Application formula for the genuine automorphism.  Its first plane
matrix is the forward one; Q1 therefore passes `S,T` in this order.
@isnad1 id=eq.10h11v.s13.bd7d45323e19 from=translated src=- shape=9fc98a79 vocab=d3aa09d0
-/
theorem commonPlaneJordanAut_apply_coe
    (E E' : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i) (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (hEidem' : ∀ i, (E' i : Mat6 K) * E' i = E' i) (hEsum' : (E' 0 : Mat6 K) + E' 1 + E' 2 = 1)
    (u v u' v' : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u) (matrixAction (E i : Mat6 K) v))
    (hp' : ∀ i, p i = (omega (K := K)) (matrixAction (E' i : Mat6 K) u') (matrixAction (E' i : Mat6 K) v'))
    (hpne : ∀ i, p i ≠ 0) (S T : Mat2 K) (hST : S*T=1) (hTS : T*S=1)
    (hdet : det2 S ≠ 0) (P : Carrier K) :
    (((commonPlaneJordanAut E E' hEidem hEsum hEidem' hEsum' u v u' v' p
      hp hp' hpne S T hST hTS hdet).linear P : Carrier K) : Mat6 K) =
      matrixOfLinear (commonPlaneForward E E' hEidem hEsum hEidem' hEsum'
        u v u' v' p hp hp' hpne S) * (P : Mat6 K) *
      matrixOfLinear (commonPlaneBackward E E' hEidem hEsum hEidem' hEsum'
        u v u' v' p hp hp' hpne T) := by
  rfl

/-- A full vector-action conjugacy proves equality of actual carrier points.
@isnad1 id=eq.11h12v.s13.b9695c337ffe from=translated src=- shape=cd2ff715 vocab=2ab1d835
-/
theorem commonPlaneJordanAut_maps_of_action
    (E E' : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i) (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (hEidem' : ∀ i, (E' i : Mat6 K) * E' i = E' i) (hEsum' : (E' 0 : Mat6 K) + E' 1 + E' 2 = 1)
    (u v u' v' : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u) (matrixAction (E i : Mat6 K) v))
    (hp' : ∀ i, p i = (omega (K := K)) (matrixAction (E' i : Mat6 K) u') (matrixAction (E' i : Mat6 K) v'))
    (hpne : ∀ i, p i ≠ 0) (S T : Mat2 K) (hST : S*T=1) (hTS : T*S=1)
    (hdet : det2 S ≠ 0) (P Q : Carrier K)
    (haction : (commonPlaneForward E E' hEidem hEsum hEidem' hEsum'
        u v u' v' p hp hp' hpne S).comp ((matrixAction (P : Mat6 K)).comp
      (commonPlaneBackward E E' hEidem hEsum hEidem' hEsum'
        u v u' v' p hp hp' hpne T)) = matrixAction (Q : Mat6 K)) :
    (commonPlaneJordanAut E E' hEidem hEsum hEidem' hEsum' u v u' v' p
      hp hp' hpne S T hST hTS hdet).linear P = Q := by
  apply Subtype.ext
  rw [commonPlaneJordanAut_apply_coe]
  apply matrixAction_injective
  rw [matrixAction_mul, matrixAction_mul, matrixAction_matrixOfLinear,
    matrixAction_matrixOfLinear]
  exact haction

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
