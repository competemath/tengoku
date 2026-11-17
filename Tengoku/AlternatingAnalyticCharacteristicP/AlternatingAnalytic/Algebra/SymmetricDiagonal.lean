import Tengoku.Seed.LinearAlgebra.Multilinear.Basic
import Tengoku.Seed.GroupTheory.Perm.Sign
import Tengoku.Seed.Data.Nat.Choose.Sum
import Tengoku.Seed.Data.Fintype.Perm
import Tengoku.Seed.Algebra.BigOperators.Pi
import Tengoku.Seed.Algebra.BigOperators.GroupWithZero.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The factorial identity for symmetric diagonal lifts

Let `q` be multilinear in `k` groups of variables, each group a vector in `R^k`, with
diagonal `q (a, …, a) = a_1 ⋯ a_k` and invariant under simultaneous permutation of the
coordinates. Then `k! * q (e_1, …, e_k) = 1`, so `(k! : R) ≠ 0` in any nontrivial commutative
ring. This mirrors the last step of the proof of Theorem B.9. The rest of the library uses only
the Möbius identity `sum_superset_neg_one_pow` from this file.
-/

namespace SymmetricDiagonal

open Finset

variable {R : Type*} [CommRing R] {k : ℕ}

/-- Coefficient of the monomial `∏_s A s (σ s)`.-/
def coeffOf (q : MultilinearMap R (fun _ : Fin k => Fin k → R) R) (σ : Fin k → Fin k) : R :=
  q fun s => Pi.single (σ s) 1

/-- Monomial expansion of a map multilinear in `k` groups of `k` variables.
@isnad1 id=eq.0h4v.s8.056897585a8b from=translated src=- shape=b1c4fb52 vocab=efdaa97f
-/
theorem expand (q : MultilinearMap R (fun _ : Fin k => Fin k → R) R) (A : Fin k → Fin k → R) :
    q A = ∑ σ : Fin k → Fin k, (∏ s, A s (σ s)) * coeffOf q σ := by
  classical
  have hA : A = fun s => ∑ t, A s t • (Pi.single t (1 : R) : Fin k → R) := by
    funext s j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hA]
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul, coeffOf]

/--
@isnad1 id=eq.0h4v.s7.e7af0f2b79f1 from=translated src=- shape=daa132ce vocab=7908ffc5
-/
theorem single_comp_perm (π : Equiv.Perm (Fin k)) (a : Fin k) :
    (Pi.single a (1 : R) : Fin k → R) ∘ π = Pi.single (π.symm a) 1 := by
  classical
  funext t
  simp only [Function.comp_apply, Pi.single_apply]
  congr 1
  exact propext ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩

/-- Invariance of `q` under coordinate permutations makes the coefficient constant on
permutations.
@isnad1 id=eq.1h4v.s9.ad48869e842f from=translated src=- shape=597f7352 vocab=88ba5058
-/
theorem coeffOf_perm (q : MultilinearMap R (fun _ : Fin k => Fin k → R) R)
    (hsymm : ∀ (π : Equiv.Perm (Fin k)) (A : Fin k → Fin k → R), q (fun s => A s ∘ π) = q A)
    (τ : Equiv.Perm (Fin k)) : coeffOf q τ = coeffOf q id := by
  have h := hsymm τ (fun s => Pi.single (τ s) 1)
  simp only [single_comp_perm, Equiv.symm_apply_apply] at h
  rw [coeffOf, ← h]
  rfl

/-- Möbius inversion on the Boolean lattice: `∑_{T ⊇ S} (-1)^|Tᶜ|` is `1` if `S` is everything
and `0` otherwise.
@isnad1 id=eq.0h3v.s7.38d957c970b0 from=translated src=- shape=9b0b1196 vocab=415fe3de
-/
theorem sum_superset_neg_one_pow (S : Finset (Fin k)) :
    (∑ T : Finset (Fin k), if S ⊆ T then ((-1 : R) ^ Tᶜ.card) else 0)
      = if S = univ then 1 else 0 := by
  classical
  have h1 : (∑ T : Finset (Fin k), if S ⊆ T then ((-1 : R) ^ Tᶜ.card) else 0)
      = ∑ U : Finset (Fin k), if U ⊆ Sᶜ then ((-1 : R) ^ U.card) else 0 := by
    refine Fintype.sum_bijective compl compl_involutive.bijective _ _ ?_
    intro T
    simp only [Finset.compl_subset_compl]
  rw [h1, ← Finset.sum_filter]
  have h2 : (univ.filter fun U : Finset (Fin k) => U ⊆ Sᶜ) = Sᶜ.powerset := by
    ext U; simp
  have h3 : (∑ a ∈ Sᶜ.powerset, (-1 : R) ^ a.card)
      = ((∑ a ∈ Sᶜ.powerset, (-1 : ℤ) ^ a.card : ℤ) : R) := by
    push_cast; rfl
  rw [h2, h3, Finset.sum_powerset_neg_one_pow_card]
  by_cases hS : S = univ
  · simp [hS]
  · have : Sᶜ ≠ ∅ := by rwa [Ne, Finset.compl_eq_empty_iff]
    simp [hS, this]

/-- The factorial identity `k! * q (e_1, …, e_k) = 1`.
@isnad1 id=eq.2h3v.s9.d1854c0ca6e3 from=translated src=- shape=1bb4f151 vocab=37584484
-/
theorem factorial_mul_coeff_eq_one (q : MultilinearMap R (fun _ : Fin k => Fin k → R) R)
    (hdiag : ∀ a : Fin k → R, q (fun _ => a) = ∏ t, a t)
    (hsymm : ∀ (π : Equiv.Perm (Fin k)) (A : Fin k → Fin k → R), q (fun s => A s ∘ π) = q A) :
    (k.factorial : R) * q (fun s => Pi.single s 1) = 1 := by
  classical
  let ind : Finset (Fin k) → Fin k → R := fun T t => if t ∈ T then 1 else 0
  have hdiagT : ∀ T : Finset (Fin k),
      (∑ σ : Fin k → Fin k, (if univ.image σ ⊆ T then (1 : R) else 0) * coeffOf q σ)
        = if T = univ then 1 else 0 := by
    intro T
    have := hdiag (ind T)
    rw [expand] at this
    simp only [ind, Fintype.prod_boole] at this
    have e1 : ∀ σ : Fin k → Fin k, (∀ s, σ s ∈ T) ↔ univ.image σ ⊆ T := by
      intro σ; simp [Finset.image_subset_iff]
    simp only [e1, Finset.image_id', Finset.univ_subset_iff] at this
    exact this
  -- Möbius-sum the diagonal identities over `T`
  have hsum : (∑ T : Finset (Fin k), (-1 : R) ^ Tᶜ.card *
      ∑ σ : Fin k → Fin k, (if univ.image σ ⊆ T then (1 : R) else 0) * coeffOf q σ)
      = ∑ T : Finset (Fin k), (-1 : R) ^ Tᶜ.card * (if T = univ then (1 : R) else 0) :=
    Finset.sum_congr rfl fun T _ => by rw [hdiagT T]
  have hrhs : (∑ T : Finset (Fin k), (-1 : R) ^ Tᶜ.card * (if T = univ then (1 : R) else 0)) = 1 := by
    simp
  rw [hrhs] at hsum
  have hlhs : (∑ T : Finset (Fin k), (-1 : R) ^ Tᶜ.card *
      ∑ σ : Fin k → Fin k, (if univ.image σ ⊆ T then (1 : R) else 0) * coeffOf q σ)
      = ∑ σ : Fin k → Fin k, (if univ.image σ = univ then coeffOf q σ else 0) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have := sum_superset_neg_one_pow (R := R) (univ.image σ)
    calc (∑ T : Finset (Fin k), (-1 : R) ^ Tᶜ.card *
            ((if univ.image σ ⊆ T then (1 : R) else 0) * coeffOf q σ))
        = (∑ T : Finset (Fin k), if univ.image σ ⊆ T then ((-1 : R) ^ Tᶜ.card) else 0)
            * coeffOf q σ := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun T _ => ?_
          split_ifs <;> ring
      _ = _ := by rw [this]; split_ifs <;> ring
  rw [hlhs] at hsum
  -- surjective self-maps of `Fin k` are the permutations
  have hperm : (∑ σ : Fin k → Fin k, (if univ.image σ = univ then coeffOf q σ else 0))
      = ∑ τ : Equiv.Perm (Fin k), coeffOf q τ := by
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_bij' (fun τ _ => (τ : Fin k → Fin k))
      (fun σ hσ => Equiv.ofBijective σ ?_) ?_ ?_ ?_ ?_ ?_
    · have hs : Function.Surjective σ := by
        intro y
        have : y ∈ univ.image σ := by
          rw [(Finset.mem_filter.mp hσ).2]; exact Finset.mem_univ y
        obtain ⟨x, -, hx⟩ := Finset.mem_image.mp this
        exact ⟨x, hx⟩
      exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
    · intro τ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.image_univ_of_surjective τ.surjective
    · intro σ _; exact Finset.mem_univ _
    · intro τ _; ext x; rfl
    · intro σ _; rfl
    · intro τ _; rfl
  rw [hperm] at hsum
  have hconst : (∑ τ : Equiv.Perm (Fin k), coeffOf q τ)
      = (k.factorial : R) * q (fun s => Pi.single s 1) := by
    rw [Finset.sum_congr rfl fun τ _ => coeffOf_perm q hsymm τ, Finset.sum_const,
      Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    rfl
  rw [hconst] at hsum
  exact hsum

/-- If `(k! : R) = 0`, no multilinear `q` has diagonal `∏ a` and is invariant under coordinate
permutations.
@isnad1 id=false.3h3v.s9.a268f1a2583f from=translated src=- shape=0f01c5f3 vocab=b8ba0bde
-/
theorem no_symmetric_diagonal_lift [Nontrivial R] (hk : (k.factorial : R) = 0)
    (q : MultilinearMap R (fun _ : Fin k => Fin k → R) R)
    (hdiag : ∀ a : Fin k → R, q (fun _ => a) = ∏ t, a t)
    (hsymm : ∀ (π : Equiv.Perm (Fin k)) (A : Fin k → Fin k → R), q (fun s => A s ∘ π) = q A) :
    False := by
  have h := factorial_mul_coeff_eq_one q hdiag hsymm
  rw [hk, zero_mul] at h
  exact zero_ne_one h

/-- Invariance under the adjacent transpositions `(i, i+1)` gives invariance under all
permutations of `Fin (n+1)`.
@isnad1 id=eq.1h5v.s11.c389327aeee6 from=translated src=- shape=edace147 vocab=b0fcb729
-/
theorem perm_invariant_of_adjacent {n : ℕ}
    (q : MultilinearMap R (fun _ : Fin (n + 1) => Fin (n + 1) → R) R)
    (hswap : ∀ (i : Fin n) (A : Fin (n + 1) → Fin (n + 1) → R),
      q (fun s => A s ∘ Equiv.swap i.castSucc i.succ) = q A)
    (π : Equiv.Perm (Fin (n + 1))) (A : Fin (n + 1) → Fin (n + 1) → R) :
    q (fun s => A s ∘ π) = q A := by
  have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; exact Submonoid.mem_top π
  induction hπ using Submonoid.closure_induction generalizing A with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hswap i A
  | one => rfl
  | mul x y _ _ hx hy =>
    have : (fun s => A s ∘ ⇑(x * y)) = fun s => (fun s' => A s' ∘ ⇑x) s ∘ ⇑y := by
      funext s; rfl
    rw [this, hy, hx]

/-- The factorial contradiction from adjacent-swap invariance, the form given by Lemma B.12.
@isnad1 id=false.3h3v.s10.f3d045d216e9 from=translated src=- shape=5731dc0e vocab=27bcaacf
-/
theorem no_adjacent_symmetric_diagonal_lift [Nontrivial R] {n : ℕ}
    (hk : ((n + 1).factorial : R) = 0)
    (q : MultilinearMap R (fun _ : Fin (n + 1) => Fin (n + 1) → R) R)
    (hdiag : ∀ a : Fin (n + 1) → R, q (fun _ => a) = ∏ t, a t)
    (hswap : ∀ (i : Fin n) (A : Fin (n + 1) → Fin (n + 1) → R),
      q (fun s => A s ∘ Equiv.swap i.castSucc i.succ) = q A) :
    False :=
  no_symmetric_diagonal_lift hk q hdiag (perm_invariant_of_adjacent q hswap)

end SymmetricDiagonal
