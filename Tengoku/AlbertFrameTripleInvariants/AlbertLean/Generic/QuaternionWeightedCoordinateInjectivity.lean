import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedProjectorCompression

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms carrier_frame_images_orthogonal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms weighted_pairings` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms weighted_coordinates_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms weightedCoordinateLinear_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms weightedCoordinateEquiv` (it only prints; the queue checks the axioms of every declaration). -/

/-! Injective weighted coordinates consumed by Q1's block dictionary. -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.SymplecticProjectorFrame
open AlbertLean.Generic.SymplecticTransvection

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Different images of an actual complete carrier frame are symplectically
orthogonal.
@isnad1 id=eq.3h6v.s11.235291171e56 from=translated src=- shape=bdf9763a vocab=dad71a8c
-/
theorem carrier_frame_images_orthogonal
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    {i j : Fin 3} (hij : i ≠ j) (x y : Vec6 K) :
    (omega (K := K)) (matrixAction (E i : Mat6 K) x)
      (matrixAction (E j : Mat6 K) y) = 0 := by
  let Q : Fin 3 → Vec6 K →ₗ[K] Vec6 K :=
    fun r => matrixAction (K := K) (E r : Mat6 K)
  have hQi : ∀ r, IsIdempotent (Q r) :=
    fun r => carrier_projector_action_idempotent (E r) (hEidem r)
  have hQsum : Q 0 + Q 1 + Q 2 = LinearMap.id :=
    carrier_frame_action_sum E hEsum
  have hcomp := comp_zero_of_complete_frame Q hQi hQsum i j hij
  exact different_images_orthogonal (omega (K := K)) (Q i) (Q j)
    (carrier_action_selfAdjoint (E i)) hcomp x y

/-- The six transported vectors have diagonal weighted Gram matrix.
@isnad1 id=and.3h5v.s12.1f964c2f7e16 from=translated src=- shape=738c5d84 vocab=06f6407c
-/
theorem weighted_pairings
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v)) :
    (∀ i j, (omega (K := K)) (matrixAction (E i : Mat6 K) u)
        (matrixAction (E j : Mat6 K) v) = if i = j then p i else 0) ∧
    (∀ i j, (omega (K := K)) (matrixAction (E i : Mat6 K) u)
        (matrixAction (E j : Mat6 K) u) = 0) ∧
    (∀ i j, (omega (K := K)) (matrixAction (E i : Mat6 K) v)
        (matrixAction (E j : Mat6 K) v) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      simp [hp i]
    · rw [ite_eq_right hij]
      exact carrier_frame_images_orthogonal E hEidem hEsum hij u v
  · intro i j
    by_cases hij : i = j
    · subst j
      exact omega_alternating (K := K) _
    · exact carrier_frame_images_orthogonal E hEidem hEsum hij u u
  · intro i j
    by_cases hij : i = j
    · subst j
      exact omega_alternating (K := K) _
    · exact carrier_frame_images_orthogonal E hEidem hEsum hij v v

/-- On the nonzero-overlap open, the weighted coordinate expression has
unique coefficients.  Since both source and target have the literal six
coordinates, this is the injective half of the desired coordinate isomorphism.
@isnad1 id=and.5h7v.s12.097e697a715e from=translated src=- shape=9f7101ba vocab=ce614bf1
-/
theorem weighted_coordinates_injective
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v))
    (hpne : ∀ i, p i ≠ 0) (a b : Fin 3 → K)
    (hz : (∑ i, a i • matrixAction (E i : Mat6 K) u) +
      ∑ i, b i • matrixAction (E i : Mat6 K) v = 0) :
    a = 0 ∧ b = 0 := by
  classical
  obtain ⟨huv, huu, hvv⟩ := weighted_pairings E hEidem hEsum u v p hp
  have ha (j : Fin 3) : a j = 0 := by
    have h := congrArg (fun z => (omega (K := K)) z
      (matrixAction (E j : Mat6 K) v)) hz
    simp only [map_add, map_sum, map_smul, map_zero, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, huv, hvv] at h
    simp [hpne j] at h
    exact h
  have hb (j : Fin 3) : b j = 0 := by
    have h := congrArg (fun z => (omega (K := K)) z
      (matrixAction (E j : Mat6 K) u)) hz
    have hrev (i : Fin 3) :
        (omega (K := K)) (matrixAction (E i : Mat6 K) v)
          (matrixAction (E j : Mat6 K) u) =
          if i = j then -(p i) else 0 := by
      by_cases hij : i = j
      · subst j
        have hz' := omega_alternating (K := K)
          (matrixAction (E i : Mat6 K) u + matrixAction (E i : Mat6 K) v)
        simp only [map_add, LinearMap.add_apply, omega_alternating] at hz'
        rw [ite_eq_left rfl]
        linear_combination hz' + hp i
      · rw [ite_eq_right hij]
        exact carrier_frame_images_orthogonal E hEidem hEsum hij v u
    simp only [map_add, map_sum, map_smul, map_zero, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, huu, hrev] at h
    simp [hpne j] at h
    exact h
  exact ⟨funext ha, funext hb⟩

/-- The literal six-column map whose columns are `E_i u,E_i v` in the
unchanged grouped ordering.-/
def weightedCoordinateLinear (E : Fin 3 → Carrier K) (u v : Vec6 K) :
    Vec6 K →ₗ[K] Vec6 K where
  toFun z := (∑ i, z (Sum.inl i) • matrixAction (E i : Mat6 K) u) +
    ∑ i, z (Sum.inr i) • matrixAction (E i : Mat6 K) v
  map_add' := by
    intro x y
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' := by
    intro t x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, smul_add,
      Finset.smul_sum, smul_smul]

/--
@isnad1 id=injectiv.4h5v.s11.fbccce80d886 from=translated src=- shape=c40dab4d vocab=86f4f07d
-/
theorem weightedCoordinateLinear_injective
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v))
    (hpne : ∀ i, p i ≠ 0) :
    Function.Injective (weightedCoordinateLinear E u v) := by
  intro x y hxy
  have hz : weightedCoordinateLinear E u v (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hcoeff := weighted_coordinates_injective E hEidem hEsum u v p hp hpne
    (fun i => (x - y) (Sum.inl i)) (fun i => (x - y) (Sum.inr i))
    (by exact hz)
  rcases hcoeff with ⟨hl, hr⟩
  funext q
  rcases q with i | i
  · have hi := congrFun hl i
    simpa only [Pi.zero_apply, Pi.sub_apply, sub_eq_zero] using hi
  · have hi := congrFun hr i
    simpa only [Pi.zero_apply, Pi.sub_apply, sub_eq_zero] using hi

/-- On the nonzero-overlap open the literal weighted coordinate map is a
genuine linear equivalence.-/
noncomputable def weightedCoordinateEquiv
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v))
    (hpne : ∀ i, p i ≠ 0) : Vec6 K ≃ₗ[K] Vec6 K :=
  LinearEquiv.ofBijective (weightedCoordinateLinear E u v)
    ⟨weightedCoordinateLinear_injective E hEidem hEsum u v p hp hpne,
      LinearMap.injective_iff_surjective.mp
        (weightedCoordinateLinear_injective E hEidem hEsum u v p hp hpne)⟩

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
