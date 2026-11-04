/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.GradedPrimeAvoidanceEventuallyD27

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Graded module avoidance on value tuples (route D29)

Pure algebra.  `R` is a graded ring acting on a graded family of abelian groups, but only through
the *value tuples* of the elements at finitely many evaluation points `i ∈ s` (`φ i : R →+* K i`
into domains): `V m` is the additive group of value tuples of degree `m`, and a homogeneous
`a ∈ R_n` maps a tuple `v ∈ V m` to a tuple `φ · a * v ∈ V (m + n)`.

If each point is eventually hit (`∃ v ∈ V d, v i ≠ 0` for large `d`) and the points have pairwise
distinct homogeneous kernels, then for all large `m` some tuple of degree `m` is nonzero at every
point.  No infinite-field hypothesis.
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false

open DirectSum

namespace RiemannRoch.GradedAvoidD29

open RiemannRoch.GradedAvoidD26

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜] {ι : Type*} {K : ι → Type*} [∀ i, CommRing (K i)] [∀ i, IsDomain (K i)]

/-- The homogeneous kernel ideal of an evaluation.-/
def hker (φ : ∀ i, A →+* K i) (i : ι) : Ideal A :=
  ((RingHom.ker (φ i)).homogeneousCore 𝒜).toIdeal

/--
@isnad1 id=ex.3h8v.s9.83e29b12a6fb from=translated src=- shape=9875e7b7 vocab=a234d737
-/
theorem graded_module_avoidance (φ : ∀ i, A →+* K i) (V : ℕ → AddSubgroup (∀ i, K i))
    (hact : ∀ n a, a ∈ 𝒜 n → ∀ m, ∀ v ∈ V m, ∃ w ∈ V (m + n), ∀ i, w i = φ i a * v i)
    (s : Finset ι)
    (hinj : Set.InjOn (hker 𝒜 φ) (s : Set ι))
    (hgen : ∀ i ∈ s, ∃ N, ∀ d, N ≤ d → ∃ v ∈ V d, v i ≠ 0) :
    ∃ m0, ∀ m, m0 ≤ m → ∃ v ∈ V m, ∀ i ∈ s, v i ≠ 0 := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun m _ => ⟨0, zero_mem _, by simp⟩⟩
  obtain ⟨p, hpS, hmin⟩ := (s.image (hker 𝒜 φ)).exists_minimal (hne.image _)
  obtain ⟨i0, hi0, rfl⟩ := Finset.mem_image.1 hpS
  obtain ⟨N, hN⟩ := hgen i0 hi0
  obtain ⟨m0', hm0'⟩ := ih (s.erase i0) (Finset.erase_ssubset hi0)
    (hinj.mono (by simp))
    fun i hi => hgen i (Finset.mem_of_mem_erase hi)
  have hprime : (hker 𝒜 φ i0).IsPrime := (RingHom.ker_isPrime (φ i0)).homogeneousCore
  have hT : ∀ q ∈ (s.erase i0).image (hker 𝒜 φ), q.IsHomogeneous 𝒜 ∧ ¬ q ≤ hker 𝒜 φ i0 := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
    have hjs : j ∈ s := Finset.mem_of_mem_erase hj
    refine ⟨(Ideal.homogeneousCore 𝒜 _).isHomogeneous, fun hle => ?_⟩
    have heq : hker 𝒜 φ j = hker 𝒜 φ i0 :=
      le_antisymm hle (hmin (Finset.mem_image_of_mem _ hjs) hle)
    exact Finset.ne_of_mem_erase hj (hinj hjs hi0 heq)
  obtain ⟨n, a, ha, haT, hap⟩ := exists_homogeneous_mem_forall_not_mem 𝒜 hprime _ hT
  have ha0 : ∀ j ∈ s.erase i0, φ j a = 0 := fun j hj =>
    (RingHom.mem_ker).1 (Ideal.toIdeal_homogeneousCore_le 𝒜 _
      (haT _ (Finset.mem_image_of_mem _ hj)))
  have hai : φ i0 a ≠ 0 := fun hz =>
    hap (Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨n, ha⟩ (RingHom.mem_ker.2 hz))
  refine ⟨max m0' (n + N), fun m hm => ?_⟩
  obtain ⟨f, hf, hfS⟩ := hm0' m (le_trans (le_max_left _ _) hm)
  by_cases hfi : f i0 = 0
  · obtain ⟨h, hh, hhi⟩ := hN (m - n) (by have := le_trans (le_max_right _ _) hm; omega)
    obtain ⟨w, hw, hwv⟩ := hact n a ha (m - n) h hh
    rw [show m - n + n = m by have := le_trans (le_max_right _ _) hm; omega] at hw
    refine ⟨f + w, add_mem hf hw, fun i hi => ?_⟩
    by_cases hii : i = i0
    · subst hii
      simp only [Pi.add_apply, hfi, zero_add, hwv]
      exact mul_ne_zero hai hhi
    · have hie : i ∈ s.erase i0 := Finset.mem_erase.2 ⟨hii, hi⟩
      simp only [Pi.add_apply, hwv, ha0 i hie, zero_mul, add_zero]
      exact hfS i hie
  · refine ⟨f, hf, fun i hi => ?_⟩
    by_cases hii : i = i0
    · exact hii ▸ hfi
    · exact hfS i (Finset.mem_erase.2 ⟨hii, hi⟩)

/-- Eventual hitting of a point from one hit in some degree plus a degree-one element with
unit value at that point (the chart coordinate).
@isnad1 id=ex.5h11v.s9.722684b1f9f9 from=translated src=- shape=81b313ce vocab=6da97f83
-/
theorem eventually_of_degree_one (φ : ∀ i, A →+* K i) (V : ℕ → AddSubgroup (∀ i, K i))
    (hact : ∀ n a, a ∈ 𝒜 n → ∀ m, ∀ v ∈ V m, ∃ w ∈ V (m + n), ∀ i, w i = φ i a * v i)
    (i : ι) (c : A) (hc : c ∈ 𝒜 1) (hci : φ i c = 1) (m1 : ℕ) (v : ∀ i, K i) (hv : v ∈ V m1)
    (hvi : v i ≠ 0) : ∃ N, ∀ d, N ≤ d → ∃ w ∈ V d, w i ≠ 0 := by
  refine ⟨m1, fun d hd => ?_⟩
  obtain ⟨w, hw, hwv⟩ := hact (d - m1) (c ^ (d - m1)) (by
    simpa using SetLike.pow_mem_graded (d - m1) hc) m1 v hv
  rw [show m1 + (d - m1) = d by omega] at hw
  refine ⟨w, hw, ?_⟩
  rw [hwv, map_pow, hci, one_pow, one_mul]
  exact hvi

end RiemannRoch.GradedAvoidD29
