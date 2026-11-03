import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticProjectorFrame
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticThreePairCoverage
import Tengoku.Seed.Tactic.NoncommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms first_two_comp_zero_of_sum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms comp_zero_of_complete_frame` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_image_hyperbolic_pair` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_hyperbolicTriple_of_complete_frame` (it only prints; the queue checks the axioms of every declaration). -/

/-! Actual nonzero projector frames supply hyperbolic data without rank,
trace, finite-dimensional spectral theory, or root extraction. -/
noncomputable section
namespace AlbertLean.Generic.SymplecticProjectorFrame

open SymplecticTransvection
universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

theorem first_two_comp_zero_of_sum (A B C : V →ₗ[K] V)
    (hA : IsIdempotent A) (hB : IsIdempotent B) (hC : IsIdempotent C)
    (hsum : A + B + C = LinearMap.id) : A.comp B = 0 ∧ B.comp A = 0 := by
  have hAA : A * A = A := hA
  have hBB : B * B = B := hB
  have hCC : C * C = C := hC
  have hpair : A + B = 1 - C := (eq_sub_iff_add_eq).2 hsum
  have hpairIdem : (A + B) * (A + B) = A + B := by
    rw [hpair]
    noncomm_ring [hCC]
  have hexpand : (A + B) * (A + B) = (A + B) + (A * B + B * A) := by
    noncomm_ring [hAA, hBB]
  have hz : (A + B) + (A * B + B * A) = (A + B) + 0 := by
    rw [← hexpand, hpairIdem, add_zero]
  have hanti : IsJordanOrthogonal A B := add_left_cancel hz
  exact ⟨comp_eq_zero_of_jordan_orthogonal A B hA hB hanti,
    reverse_comp_eq_zero_of_jordan_orthogonal A B hA hB hanti⟩

theorem comp_zero_of_complete_frame (P : Fin 3 → V →ₗ[K] V)
    (hidem : ∀ i, IsIdempotent (P i))
    (hsum : P 0 + P 1 + P 2 = LinearMap.id) :
    ∀ i j, i ≠ j → (P i).comp (P j) = 0 := by
  have h01 := first_two_comp_zero_of_sum (P 0) (P 1) (P 2)
    (hidem 0) (hidem 1) (hidem 2) hsum
  have h02 := first_two_comp_zero_of_sum (P 0) (P 2) (P 1)
    (hidem 0) (hidem 2) (hidem 1) (by simpa only [add_right_comm] using hsum)
  have h12 := first_two_comp_zero_of_sum (P 1) (P 2) (P 0)
    (hidem 1) (hidem 2) (hidem 0) (by
      calc
        P 1 + P 2 + P 0 = P 0 + P 1 + P 2 := by abel
        _ = LinearMap.id := hsum)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- The pair is constructed inside the actual projector image.-/
theorem exists_image_hyperbolic_pair
    (omega : BilinForm (K := K) (V := V))
    (hright : IsRightNondegenerate omega) (P : V →ₗ[K] V)
    (hP : IsIdempotent P) (hself : IsSelfAdjoint omega P) (hne : P ≠ 0) :
    ∃ u v : V, P u = u ∧ P v = v ∧ omega u v = 1 := by
  classical
  have hex : ∃ x, P x ≠ 0 := by
    by_contra h
    apply hne
    ext x
    exact not_not.mp (fun hx => h ⟨x, hx⟩)
  obtain ⟨x, hx⟩ := hex
  obtain ⟨y, hy⟩ := hright (P x) hx
  exact ⟨P x, normalizedPartner omega P (P x) y,
    idempotent_apply P hP x, normalizedPartner_mem omega P hP (P x) y,
    normalizedPartner_pairs_one omega P hP hself x y hy⟩

/-- Three nonzero self-adjoint idempotents summing to one yield an ordered
hyperbolic triple, with the full labelled projector action on its vectors.-/
theorem exists_hyperbolicTriple_of_complete_frame
    (omega : BilinForm (K := K) (V := V))
    (hright : IsRightNondegenerate omega) (P : Fin 3 → V →ₗ[K] V)
    (hidem : ∀ i, IsIdempotent (P i))
    (hself : ∀ i, IsSelfAdjoint omega (P i)) (hne : ∀ i, P i ≠ 0)
    (hsum : P 0 + P 1 + P 2 = LinearMap.id) :
    ∃ u v : Fin 3 → V, HyperbolicTriple omega u v ∧
      (∀ i j, P i (u j) = if i = j then u j else 0) ∧
      (∀ i j, P i (v j) = if i = j then v j else 0) := by
  classical
  choose u v hu hv huv using fun i =>
    exists_image_hyperbolic_pair omega hright (P i) (hidem i) (hself i) (hne i)
  have hcomp := comp_zero_of_complete_frame P hidem hsum
  have horth (i j : Fin 3) (hij : i ≠ j) (x y : V)
      (hx : P i x = x) (hy : P j y = y) : omega x y = 0 := by
    rw [← hx, ← hy]
    exact different_images_orthogonal omega (P i) (P j) (hself i) (hcomp i j hij) x y
  refine ⟨u, v, ⟨huv, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j hij
    exact horth i j hij (u i) (u j) (hu i) (hu j)
  · intro i j hij
    exact horth i j hij (u i) (v j) (hu i) (hv j)
  · intro i j hij
    exact horth i j hij (v i) (u j) (hv i) (hu j)
  · intro i j hij
    exact horth i j hij (v i) (v j) (hv i) (hv j)
  · intro i j
    by_cases hij : i = j
    · subst j
      simpa using hu i
    · rw [ite_eq_right hij, ← hu j]
      exact LinearMap.congr_fun (hcomp i j hij) (u j)
  · intro i j
    by_cases hij : i = j
    · subst j
      simpa using hv i
    · rw [ite_eq_right hij, ← hv j]
      exact LinearMap.congr_fun (hcomp i j hij) (v j)

end AlbertLean.Generic.SymplecticProjectorFrame
