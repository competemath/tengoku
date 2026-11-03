import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedCoordinateInjectivity
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionSimilitudeConjugation
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWordMatrixConnection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms commonPlaneJordanAut` (it only prints; the queue checks the axioms of every declaration). -/

/-! Root-free common-plane similitudes consumed by Q1's pair normalizer. -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.QuaternionRow.WordMatrixConnection
open AlbertLean.Generic.QuaternionRow.SimilitudeConjugation
open AlbertLean.Generic.SymplecticTransvection

universe u
variable {K : Type u} [Field K] [CharZero K]

def weightedOmega (p : Fin 3 → K) (x y : Vec6 K) : K :=
  ∑ i, p i * (x (Sum.inl i) * y (Sum.inr i) -
    x (Sum.inr i) * y (Sum.inl i))

theorem weightedCoordinate_form
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v)) (x y : Vec6 K) :
    (omega (K := K)) (weightedCoordinateLinear E u v x)
      (weightedCoordinateLinear E u v y) = weightedOmega p x y := by
  obtain ⟨huv, huu, hvv⟩ := weighted_pairings E hEidem hEsum u v p hp
  have hrev (i j : Fin 3) :
      (omega (K := K)) (matrixAction (E i : Mat6 K) v)
        (matrixAction (E j : Mat6 K) u) =
        if i = j then -(p i) else 0 := by
    rw [skew_of_alternating (omega (K := K)) omega_alternating]
    by_cases hij : i = j
    · subst j
      simp [huv]
    · simp [huv, hij, Ne.symm hij]
  simp [weightedCoordinateLinear, weightedOmega, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, huv, huu, hvv, hrev]
  rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The same `2×2` map on each of the three literal planes.-/
def commonPlaneMap (T : Matrix (Fin 2) (Fin 2) K) : Vec6 K →ₗ[K] Vec6 K where
  toFun x
    | Sum.inl i => T 0 0 * x (Sum.inl i) + T 0 1 * x (Sum.inr i)
    | Sum.inr i => T 1 0 * x (Sum.inl i) + T 1 1 * x (Sum.inr i)
  map_add' := by intro x y; funext q; rcases q with i | i <;> simp <;> ring
  map_smul' := by intro t x; funext q; rcases q with i | i <;> simp <;> ring

def det2 (T : Matrix (Fin 2) (Fin 2) K) : K :=
  T 0 0 * T 1 1 - T 0 1 * T 1 0

theorem commonPlaneMap_form (p : Fin 3 → K)
    (T : Matrix (Fin 2) (Fin 2) K) (x y : Vec6 K) :
    weightedOmega p (commonPlaneMap T x) (commonPlaneMap T y) =
      det2 T * weightedOmega p x y := by
  simp only [weightedOmega, commonPlaneMap, det2]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change p i *
      ((T 0 0 * x (Sum.inl i) + T 0 1 * x (Sum.inr i)) *
          (T 1 0 * y (Sum.inl i) + T 1 1 * y (Sum.inr i)) -
        (T 1 0 * x (Sum.inl i) + T 1 1 * x (Sum.inr i)) *
          (T 0 0 * y (Sum.inl i) + T 0 1 * y (Sum.inr i))) = _
  ring

theorem commonPlaneMap_comp (T S : Matrix (Fin 2) (Fin 2) K)
    (hTS : T * S = 1) :
    (commonPlaneMap T).comp (commonPlaneMap S) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext q
  rcases q with i | i
  ·
    have h00 := congrFun (congrFun hTS 0) 0
    have h01 := congrFun (congrFun hTS 0) 1
    have h10 := congrFun (congrFun hTS 1) 0
    have h11 := congrFun (congrFun hTS 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
      commonPlaneMap, LinearMap.comp_apply] at h00 h01 h10 h11 ⊢
    linear_combination x (Sum.inl i) * h00 + x (Sum.inr i) * h01
  ·
    have h00 := congrFun (congrFun hTS 0) 0
    have h01 := congrFun (congrFun hTS 0) 1
    have h10 := congrFun (congrFun hTS 1) 0
    have h11 := congrFun (congrFun hTS 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
      commonPlaneMap, LinearMap.comp_apply] at h00 h01 h10 h11 ⊢
    linear_combination x (Sum.inl i) * h10 + x (Sum.inr i) * h11

/-- Two actual weighted coordinate systems with the same weights and one
common invertible `2×2` change produce a genuine carrier Jordan automorphism.
No square root of its determinant is chosen.-/
def commonPlaneJordanAut
    (E E' : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (hEidem' : ∀ i, (E' i : Mat6 K) * E' i = E' i)
    (hEsum' : (E' 0 : Mat6 K) + E' 1 + E' 2 = 1)
    (u v u' v' : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v))
    (hp' : ∀ i, p i = (omega (K := K)) (matrixAction (E' i : Mat6 K) u')
      (matrixAction (E' i : Mat6 K) v')) (hpne : ∀ i, p i ≠ 0)
    (T S : Matrix (Fin 2) (Fin 2) K) (hTS : T * S = 1) (hST : S * T = 1)
    (hdet : det2 T ≠ 0) : ScalarJordanAut.Aut (K := K) := by
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  let L' := weightedCoordinateEquiv E' hEidem' hEsum' u' v' p hp' hpne
  let A : Vec6 K →ₗ[K] Vec6 K :=
    L'.toLinearMap.comp ((commonPlaneMap T).comp L.symm.toLinearMap)
  let C : Vec6 K →ₗ[K] Vec6 K :=
    L.toLinearMap.comp ((commonPlaneMap S).comp L'.symm.toLinearMap)
  let M := matrixOfLinear A
  let N := matrixOfLinear C
  have hAC : A.comp C = LinearMap.id := by
    apply LinearMap.ext
    intro x
    have hc := LinearMap.congr_fun (commonPlaneMap_comp T S hTS) (L'.symm x)
    change L' (commonPlaneMap T (L.symm (L (commonPlaneMap S (L'.symm x))))) = x
    rw [L.symm_apply_apply]
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hc
    rw [hc, L'.apply_symm_apply]
  have hCA : C.comp A = LinearMap.id := by
    apply LinearMap.ext
    intro x
    have hc := LinearMap.congr_fun (commonPlaneMap_comp S T hST) (L.symm x)
    change L (commonPlaneMap S (L'.symm (L' (commonPlaneMap T (L.symm x))))) = x
    rw [L'.symm_apply_apply]
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hc
    rw [hc, L.apply_symm_apply]
  have hMN : M * N = 1 := by
    apply matrixAction_injective
    rw [matrixAction_mul, matrixAction_matrixOfLinear,
      matrixAction_matrixOfLinear, hAC, matrixAction_one]
  have hNM : N * M = 1 := by
    apply matrixAction_injective
    rw [matrixAction_mul, matrixAction_matrixOfLinear,
      matrixAction_matrixOfLinear, hCA, matrixAction_one]
  have hpres (x y : Vec6 K) :
      (omega (K := K)) (A x) (A y) = det2 T * (omega (K := K)) x y := by
    change (omega (K := K)) (L' (commonPlaneMap T (L.symm x)))
      (L' (commonPlaneMap T (L.symm y))) = _
    have hL' (z : Vec6 K) :
        L' z = weightedCoordinateLinear E' u' v' z := rfl
    have hL (z : Vec6 K) :
        L z = weightedCoordinateLinear E u v z := rfl
    rw [hL', hL', weightedCoordinate_form E' hEidem' hEsum' u' v' p hp',
      commonPlaneMap_form,
      ← weightedCoordinate_form E hEidem hEsum u v p hp,
      ← hL, ← hL, L.apply_symm_apply, L.apply_symm_apply]
  have hform : M.transpose * symplecticJ * M = det2 T • symplecticJ := by
    ext i j
    rw [symplectic_product_entry]
    rw [← matrixAction_basisVector M i, ← matrixAction_basisVector M j,
      matrixAction_matrixOfLinear, hpres, omega_basisVector]
    rfl
  exact SimilitudeConjugation.jordanAut M N (det2 T) hMN hNM hdet hform

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
