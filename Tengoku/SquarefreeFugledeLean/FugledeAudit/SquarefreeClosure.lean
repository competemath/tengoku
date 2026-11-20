import Tengoku.SquarefreeFugledeLean.FugledeAudit.PrimeCollision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace FugledeAudit

/--
@isnad1 id=istransl.0h1v.s4.4dd898c76e1e from=translated src=- shape=456cb356 vocab=5f777470
-/
theorem whole_group_tiles
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] :
    IsTranslationalTile (Finset.univ : Finset G) := by
  refine ⟨{0}, ?_⟩
  intro x
  refine ⟨(⟨x, Finset.mem_univ x⟩, ⟨0, Finset.mem_singleton_self 0⟩), by simp, ?_⟩
  intro v hv
  have ht : v.2.val = 0 := Finset.mem_singleton.mp v.2.property
  apply Prod.ext
  · apply Subtype.ext
    simpa only [ht, add_zero] using hv
  · exact Subtype.ext ht

/--
@isnad1 id=dvd.3h2v.s5.32cb74890004 from=translated src=- shape=8131cf88 vocab=44871a4d
-/
theorem squarefree_dvd_twice_of_odd_primes_dvd
    (N m : ℕ) (hs : Squarefree N) (hm : 0 < m)
    (hp : ∀ q, q.Prime → 3 ≤ q → q ∣ N → q ∣ m) : N ∣ 2 * m := by
  have hm2 : 2 * m ≠ 0 := by omega
  have hd : (∏ q ∈ N.primeFactors, q) ∣ 2 * m := by
    apply (Nat.prod_primeFactors_dvd_iff hm2).mpr
    intro q hqN
    obtain ⟨hq, hqN, _⟩ := Nat.mem_primeFactors.mp hqN
    apply Nat.mem_primeFactors.mpr
    refine ⟨hq, ?_, hm2⟩
    by_cases hq2 : q = 2
    · subst q
      exact dvd_mul_right 2 m
    · exact dvd_mul_of_dvd_right (hp q hq (by have := hq.two_le; omega) hqN) 2
  simpa only [Nat.prod_primeFactors_of_squarefree hs] using hd

/--
@isnad1 id=or.3h2v.s5.951a25de462c from=translated src=- shape=c2b64a89 vocab=3a19dee0
-/
theorem size_eq_order_or_half
    (N m : ℕ) (hm : 0 < m) (hmN : m ≤ N) (hd : N ∣ 2 * m) :
    m = N ∨ N = 2 * m := by
  obtain ⟨k, hk⟩ := hd
  have hN : 0 < N := by omega
  have hkpos : 0 < k := by nlinarith
  have hkle : k ≤ 2 := by nlinarith
  interval_cases k <;> omega

/--
@isnad1 id=istransl.3h3v.s7.96369bb45ff9 from=translated src=- shape=da8e909a vocab=4c502d89
-/
theorem half_order_spectral_set_tiles
    (H : ℕ) [NeZero H] (hs : Squarefree (2 * H))
    (A Λ : Finset (ZMod (2 * H))) (h : IsCyclicSpectralPair A Λ) (hm : A.card = H) :
    IsTranslationalTile A := by
  classical
  have hcop := Nat.coprime_of_squarefree_mul hs
  have hnd : ¬2 ∣ A.card := by
    rw [hm]
    intro hd
    have hg : Nat.gcd 2 H = 2 := Nat.gcd_eq_left hd
    rw [hcop.gcd_eq_one] at hg
    omega
  have hi := spectral_physical_projection_injective_any_prime 2 H Nat.prime_two hcop A Λ h hnd
  have hfull : A.image (reducePrimeFactor 2 H) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hi, hm, ZMod.card]
  apply quotient_lifts_tiling (reducePrimeFactor 2 H).toAddMonoidHom A hi
  rw [show A.image (reducePrimeFactor 2 H).toAddMonoidHom = Finset.univ from hfull]
  exact whole_group_tiles (ZMod H)

end FugledeAudit
