import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LaurentPolynomial_uniqueFactorizationMonoid.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LaurentPolynomial_uniqueFactorizationMonoid
set_option autoImplicit false
set_option maxHeartbeats 3200000
universe u v

open scoped Polynomial
open LaurentPolynomial

namespace LaurentUFD

/--
@isnad1 id=uniquefa.1h3v.s6.5ac9cd39fcb1 from=translated src=- shape=3cad004a vocab=bf079896
-/
theorem uniqueFactorizationMonoid_of_isLocalization
    {R : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R)
    (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S] : UniqueFactorizationMonoid S := by
  haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  refine UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr fun J hJ hJp => ?_
  haveI := hJp

  set I : Ideal R := J.under R with hI
  haveI hIp : I.IsPrime := Ideal.IsPrime.under R J
  have hI0 : I ≠ ⊥ := by
    intro h0
    apply hJ
    rw [eq_bot_iff]
    intro s hs
    obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M s
    have hr : algebraMap R S r ∈ J := by
      have := J.mul_mem_left (algebraMap R S m) hs
      rwa [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mul_cancel_left] at this
    have hrI : r ∈ I := Ideal.mem_comap.mpr hr
    rw [h0, Ideal.mem_bot] at hrI
    rw [Submodule.mem_bot, hrI]
    exact IsLocalization.mk'_zero _

  obtain ⟨p, hpI, hp⟩ := (UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mp ‹_› I hI0 hIp)
  refine ⟨algebraMap R S p, Ideal.mem_comap.mp hpI, ?_⟩

  have hdisj : Disjoint (M : Set R) (Ideal.span {p} : Set R) := by
    rw [Set.disjoint_left]
    intro m hm hmp
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hmp
    have hu : IsUnit (algebraMap R S (c * p)) := IsLocalization.map_units S ⟨c * p, hm⟩
    rw [map_mul] at hu
    exact hJp.ne_top (J.eq_top_of_isUnit_mem (Ideal.mem_comap.mp hpI) (isUnit_of_mul_isUnit_right hu))
  have hprime : (Ideal.map (algebraMap R S) (Ideal.span {p})).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M S _ ((Ideal.span_singleton_prime hp.ne_zero).mpr hp) hdisj
  rw [Ideal.map_span, Set.image_singleton] at hprime
  have hp0 : algebraMap R S p ≠ 0 := fun h =>
    hp.ne_zero ((IsLocalization.injective S hM) (by rw [h, map_zero]))
  exact (Ideal.span_singleton_prime hp0).mp hprime

/--
@isnad1 id=uniquefa.0h1v.s5.2b7c9772725d from=translated src=- shape=7f51ae2a vocab=bae67215
-/
theorem laurentPolynomial (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid R[T;T⁻¹] :=
  uniqueFactorizationMonoid_of_isLocalization (Submonoid.powers (Polynomial.X : R[X]))
    (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero) R[T;T⁻¹]

end LaurentUFD

/--
@isnad1 id=uniquefa.0h1v.s5.2b7c9772725d from=translated src=- shape=7f51ae2a vocab=bae67215
-/
theorem solution (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid R[T;T⁻¹] :=
  LaurentUFD.laurentPolynomial R
