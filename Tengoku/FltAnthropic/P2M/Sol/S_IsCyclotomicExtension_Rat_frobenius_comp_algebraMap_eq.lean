import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsCyclotomicExtension_Rat_frobenius_comp_algebraMap_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsCyclotomicExtension_Rat_frobenius_comp_algebraMap_eq

set_option autoImplicit false

namespace L1Sol

/--
@isnad1 id=le.1h4v.s7.86f98ba9498e from=translated src=- shape=0634ba9c vocab=91379570
-/
theorem maximalIdeal_le_ker_of_charP (p : ℕ) [Fact p.Prime]
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (hp0 : (p : A) ≠ 0)
    {k : Type*} [CommRing k] [IsDomain k] [CharP k p] (φ : A →+* k) :
    IsLocalRing.maximalIdeal A ≤ RingHom.ker φ := by
  have hp : (p : A) ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hne : RingHom.ker φ ≠ ⊥ := fun h => hp0 (by rwa [h, Ideal.mem_bot] at hp)
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmax : (RingHom.ker φ).IsMaximal := IsPrime.to_maximal_ideal hne
  exact (IsLocalRing.eq_maximalIdeal hmax).ge

/--
@isnad1 id=eq.1h6v.s8.11ce23f99b28 from=translated src=- shape=63aa2301 vocab=6a3a42ad
-/
theorem apply_pow_eq_apply (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    {k : Type*} [CommRing k] [IsDomain k] [CharP k p] (φ : A →+* k) (a : A) :
    φ a ^ p = φ a := by
  have hp0 : (p : A) ≠ 0 := fun h => by
    have h' := congrArg (algebraMap A L) h
    rw [map_natCast, map_zero] at h'
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h')
  obtain ⟨n, hn⟩ := IsCyclotomicExtension.Rat.surjective_algebraMap_int_residueField_of_isDiscreteValuationRing
    p L A hAp (IsLocalRing.residue A a)
  have hres : IsLocalRing.residue A a = IsLocalRing.residue A (n : A) := by
    rw [← hn, eq_intCast, map_intCast]
  have hmem : a - (n : A) ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq.1 hres
  have hker := maximalIdeal_le_ker_of_charP p A hp0 φ hmem
  rw [RingHom.mem_ker, map_sub, sub_eq_zero, map_intCast] at hker
  have hfix : ((n : k)) ^ p = n := by rw [← frobenius_def, map_intCast]
  rw [hker, hfix]

end L1Sol

/--
@isnad1 id=eq.1h4v.s8.8d7657743f40 from=translated src=- shape=ec953005 vocab=22257cb3
-/
theorem solution
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (k : Type*) [CommRing k] [IsDomain k] [CharP k p] [Algebra A k] :
    (frobenius k p).comp (algebraMap A k) = algebraMap A k :=
  RingHom.ext fun a => L1Sol.apply_pow_eq_apply p L A hAp (algebraMap A k) a
