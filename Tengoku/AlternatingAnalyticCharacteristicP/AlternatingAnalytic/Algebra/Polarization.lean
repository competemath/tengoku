import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Algebra.SymmetricDiagonal
import Tengoku.Seed.Algebra.Module.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Squarefree polarization over arbitrary commutative rings

The sum of a multilinear map over all permutations of its arguments is determined by its
diagonal, through an inclusion-exclusion sum over subsets. The formula involves no division,
so it holds in every characteristic. It gives (Pw) ⇒ (Pol1) in Proposition B.8(1).
-/

open Finset

namespace Polarization

/-- Summing over self-maps of `Fin k` with full range is summing over permutations.
@isnad1 id=eq.0h3v.s7.02efddac8d91 from=translated src=- shape=37a3ce7b vocab=d8ecd081
-/
theorem sum_full_range_eq_sum_perm {k : ℕ} {M : Type*} [AddCommMonoid M]
    (g : (Fin k → Fin k) → M) :
    (∑ σ : Fin k → Fin k, if univ.image σ = univ then g σ else 0) =
      ∑ τ : Equiv.Perm (Fin k), g τ := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij' (fun τ _ => (τ : Fin k → Fin k))
    (fun σ hσ => Equiv.ofBijective σ ?_) ?_ ?_ ?_ ?_ ?_
  · have hs : Function.Surjective σ := by
      intro y
      have hy : y ∈ univ.image σ := by
        rw [(Finset.mem_filter.mp hσ).2]
        exact Finset.mem_univ y
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  · intro τ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.image_univ_of_surjective τ.surjective
  · intro σ _
    exact Finset.mem_univ _
  · intro τ _
    ext x
    rfl
  · intro σ _
    rfl
  · intro τ _
    rfl

end Polarization

namespace MultilinearMap

variable {R A M : Type*} [CommRing R]
  [AddCommMonoid A] [Module R A] [AddCommMonoid M] [Module R M] {k : ℕ}

/-- Expand the diagonal at a subset sum `∑_{i ∈ S} b i` over the self-maps with range in `S`.
@isnad1 id=eq.0h7v.s8.e4796a4d89e7 from=translated src=- shape=88003df7 vocab=6e721a12
-/
theorem map_diagonal_sum (P : MultilinearMap R (fun _ : Fin k => A) M)
    (b : Fin k → A) (S : Finset (Fin k)) :
    P (fun _ => ∑ i ∈ S, b i) =
      ∑ σ : Fin k → Fin k, if univ.image σ ⊆ S then P (fun j => b (σ j)) else 0 := by
  classical
  have he : (fun _ : Fin k => ∑ i ∈ S, b i) =
      fun _ : Fin k => ∑ i : Fin k, (if i ∈ S then (1 : R) else 0) • b i := by
    funext j
    simp
  rw [he, P.map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [P.map_smul_univ]
  have hrange : (∀ j, σ j ∈ S) ↔ univ.image σ ⊆ S := by
    simp [Finset.image_subset_iff]
  simp only [Fintype.prod_boole, hrange, ite_smul, one_smul, zero_smul]

/-- The squarefree polarization formula. No division by `k!` is involved.
@isnad1 id=eq.0h6v.s8.dd233ae51fa4 from=translated src=- shape=8e26341e vocab=304d081f
-/
theorem squarefree_polarization (P : MultilinearMap R (fun _ : Fin k => A) M)
    (b : Fin k → A) :
    (∑ S : Finset (Fin k), (-1 : R) ^ Sᶜ.card • P (fun _ => ∑ i ∈ S, b i)) =
      ∑ σ : Equiv.Perm (Fin k), P (fun i => b (σ i)) := by
  classical
  simp_rw [map_diagonal_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ σ : Fin k → Fin k, ∑ S : Finset (Fin k),
        (-1 : R) ^ Sᶜ.card •
          (if univ.image σ ⊆ S then P (fun j => b (σ j)) else 0)) =
        ∑ σ : Fin k → Fin k,
          if univ.image σ = univ then P (fun j => b (σ j)) else 0 := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      calc
        (∑ S : Finset (Fin k), (-1 : R) ^ Sᶜ.card •
            (if univ.image σ ⊆ S then P (fun j => b (σ j)) else 0)) =
            (∑ S : Finset (Fin k),
              if univ.image σ ⊆ S then (-1 : R) ^ Sᶜ.card else 0) •
                P (fun j => b (σ j)) := by
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun S _ => ?_
          split_ifs <;> simp
        _ = _ := by
          rw [SymmetricDiagonal.sum_superset_neg_one_pow]
          split_ifs <;> simp
    _ = _ := Polarization.sum_full_range_eq_sum_perm _

/-- Multilinear maps with the same diagonal have the same permutation sums, over every
commutative ring.
@isnad1 id=eq.1h7v.s8.e06ab7ab4e1e from=translated src=- shape=bcb8f0b5 vocab=83c235a7
-/
theorem sum_perm_eq_of_diagonal_eq
    (P Q : MultilinearMap R (fun _ : Fin k => A) M)
    (h : ∀ a : A, P (fun _ => a) = Q (fun _ => a)) (b : Fin k → A) :
    (∑ σ : Equiv.Perm (Fin k), P (fun i => b (σ i))) =
      ∑ σ : Equiv.Perm (Fin k), Q (fun i => b (σ i)) := by
  rw [← squarefree_polarization P b, ← squarefree_polarization Q b]
  exact Finset.sum_congr rfl fun S _ => congrArg (((-1 : R) ^ Sᶜ.card) • ·) (h _)

/-- (Pw) implies (Pol1) (Proposition B.8(1)). Here `P` is a lift with the vector arguments `x`
fixed, and taking `W` to be the wedge gives the paper's statement.
@isnad1 id=eq.1h10v.s10.9b79e2bbc4f9 from=translated src=- shape=b4b2a132 vocab=2ec1e68f
-/
theorem sum_perm_eq_of_multiplier_diagonal
    {V : Type*} [AddCommMonoid V] [Module R V]
    (P : MultilinearMap R (fun _ : Fin k => A) M)
    (W : MultilinearMap R (fun _ : Fin k => V) M)
    (D : A →ₗ[R] (V →ₗ[R] V)) (x : Fin k → V)
    (h : ∀ a : A, P (fun _ => a) = W (fun i => D a (x i))) (b : Fin k → A) :
    (∑ σ : Equiv.Perm (Fin k), P (fun i => b (σ i))) =
      ∑ σ : Equiv.Perm (Fin k), W (fun i => D (b (σ i)) (x i)) := by
  let Q := W.compLinearMap fun i => (LinearMap.applyₗ (R := R) (x i)).comp D
  exact sum_perm_eq_of_diagonal_eq P Q h b

end MultilinearMap
