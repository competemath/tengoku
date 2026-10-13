module

public import Tengoku
import Tengoku.FltRegular.FltRegular.NumberTheory.Cyclotomic.MoreLemmas

/-!
# Cyclotomic integers

This file defines cyclotomic integers using `AdjoinRoot` and relates them to the ring of
integers of the corresponding rational cyclotomic field.
-/

@[expose] public section

noncomputable section

open Polynomial NumberField

variable (p : ℕ) [hpri : Fact p.Prime]

/-- The cyclotomic integers of conductor `p`, defined as an `AdjoinRoot`. -/
def CyclotomicIntegers : Type := AdjoinRoot (cyclotomic p ℤ)

instance : CommRing (CyclotomicIntegers p) := by
  delta CyclotomicIntegers
  infer_instance

set_option backward.isDefEq.respectTransparency false in
open Polynomial in
/--
@isnad1 id=eq.1h2v.s8.e653b96db3bf from=translated src=- shape=52972161 vocab=6bbcec05
-/
lemma IsPrimitiveRoot.cyclotomic_eq_minpoly
    (x : 𝓞 (CyclotomicField p ℚ)) (hx : IsPrimitiveRoot x.1 p) :
    minpoly ℤ x = cyclotomic p ℤ := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (RingHom.injective_int (algebraMap ℤ ℚ))
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ (CyclotomicField p ℚ)
    (IsIntegralClosure.isIntegral _ (CyclotomicField p ℚ) _),
    ← cyclotomic_eq_minpoly_rat (n := p) (hpos := hpri.out.pos), map_cyclotomic]
  exact hx

namespace CyclotomicIntegers

set_option backward.isDefEq.respectTransparency false in
/-- The canonical equivalence between `CyclotomicIntegers p` and the ring of integers of the
`p`-th cyclotomic field. -/
@[simps! -isSimp]
def equiv :
    CyclotomicIntegers p ≃+* 𝓞 (CyclotomicField p ℚ) := by
  have H := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  have hH : minpoly ℤ H.integralPowerBasis.gen = cyclotomic p ℤ :=
    H.integralPowerBasis_gen ▸ IsPrimitiveRoot.cyclotomic_eq_minpoly p H.toInteger H
  exact (AdjoinRoot.equiv' (cyclotomic p ℤ) H.integralPowerBasis
    (hH ▸ ((AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self))
    (hH ▸ minpoly.aeval _ _)).toRingEquiv

instance : IsDomain (CyclotomicIntegers p) :=
  AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (cyclotomic.irreducible hpri.out.pos))

/-- The tautological primitive root of unity in `CyclotomicIntegers p`. -/
def zeta : CyclotomicIntegers p := AdjoinRoot.root _

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h1v.s8.262ed8f13745 from=translated src=- shape=1cddddbf vocab=77b84054
-/
lemma equiv_zeta : equiv p (zeta p) = (IsCyclotomicExtension.zeta_spec
    p ℚ (CyclotomicField p ℚ)).toInteger := by
  simp [equiv_apply, zeta]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=prime.0h1v.s6.22585281ba1e from=translated src=- shape=7be907f5 vocab=25a16654
-/
lemma prime_one_sub_zeta :
    Prime (1 - zeta p) := by
  rw [← prime_units_mul (u := -1), Units.val_neg, Units.val_one, neg_mul, one_mul, neg_sub]
  apply (MulEquiv.prime_iff (equiv p)).1
  simp only [(equiv p).map_sub, (equiv p).map_one, equiv_zeta]
  exact (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)).zeta_sub_one_prime'

/--
@isnad1 id=mem.0h1v.s7.7a821b7450c7 from=translated src=- shape=8b6e34e0 vocab=6e85a1be
-/
lemma one_sub_zeta_mem_nonZeroDivisors :
    1 - zeta p ∈ nonZeroDivisors (CyclotomicIntegers p) := by
  simpa only [mem_nonZeroDivisors_iff_ne_zero] using (prime_one_sub_zeta p).1

/--
@isnad1 id=not.0h1v.s6.ed7d72d36c19 from=translated src=- shape=1eecab03 vocab=bf910110
-/
lemma not_isUnit_one_sub_zeta :
    ¬ IsUnit (1 - zeta p) := (prime_one_sub_zeta p).irreducible.1

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=iff.0h2v.s6.25c7a748236f from=translated src=- shape=8d3072b3 vocab=171dd0d5
-/
lemma one_sub_zeta_dvd_int_iff (n : ℤ) : 1 - zeta p ∣ n ↔ ↑p ∣ n := by
  rw [← map_dvd_iff (equiv p), map_sub, map_one, equiv_zeta, map_intCast,
    ← neg_dvd, neg_sub]
  exact IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' p
    (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ))

/--
@isnad1 id=dvd.0h1v.s6.1ba88490425e from=translated src=- shape=b5c8b615 vocab=9e3d956a
-/
lemma one_sub_zeta_dvd : 1 - zeta p ∣ p :=
  (one_sub_zeta_dvd_int_iff _ _).2 dvd_rfl

/--
@isnad1 id=iscoprim.1h2v.s6.d7ef63880177 from=translated src=- shape=b662cfea vocab=cd61a7ce
-/
lemma isCoprime_one_sub_zeta (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) : IsCoprime (1 - zeta p) n :=
  (((Nat.prime_iff_prime_int.mp hpri.out).coprime_iff_not_dvd.mpr hn).map
    (algebraMap ℤ <| CyclotomicIntegers p)).of_isCoprime_of_dvd_left (one_sub_zeta_dvd p)

/--
@isnad1 id=ex.1h2v.s6.6a25b0be313a from=translated src=- shape=a9927c2a vocab=3909be6c
-/
lemma exists_dvd_int (n : CyclotomicIntegers p) (hn : n ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ n ∣ m := by
  refine ⟨Algebra.norm ℤ ((equiv p) n), by simpa, ?_⟩
  rw [← map_dvd_iff (equiv p), map_intCast]
  have : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero p ℚ
  have : IsGalois ℚ (CyclotomicField p ℚ) := IsCyclotomicExtension.isGalois {p} _ _
  convert RingOfIntegers.dvd_norm ℚ (equiv p n) using 1
  ext1
  exact DFunLike.congr_arg (algebraMap ℚ _) (Algebra.coe_norm_int (equiv p n))

/-- The power basis of `CyclotomicIntegers p` generated by `zeta p`. -/
def powerBasis : PowerBasis ℤ (CyclotomicIntegers p) :=
  AdjoinRoot.powerBasis' (cyclotomic.monic _ _)

/--
@isnad1 id=eq.0h1v.s5.2fbe04c80d6d from=translated src=- shape=3b8e0eba vocab=11fa8925
-/
lemma powerBasis_dim : (powerBasis p).dim = p - 1 := by
  simp [powerBasis, Nat.totient_prime hpri.out, natDegree_cyclotomic]

instance : Module.Free ℤ (CyclotomicIntegers p) := ⟨_, (powerBasis p).basis⟩

/--
@isnad1 id=nontrivi.1h1v.s3.76469950f8d6 from=translated src=- shape=01e184dd vocab=d4612ecb
-/
lemma nontrivial {p} (hp : p ≠ 0) : Nontrivial (CyclotomicIntegers p) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  simp only [ne_eq, Ideal.span_singleton_eq_top]
  intro h
  have hdegree := natDegree_eq_zero_of_isUnit h
  rw [natDegree_cyclotomic] at hdegree
  exact hdegree.not_gt (Nat.totient_pos.2 <| Nat.zero_lt_of_ne_zero hp)

/--
@isnad1 id=charzero.1h1v.s4.a293f65dbfb8 from=translated src=- shape=01e184dd vocab=c106c9c1
-/
lemma charZero {p} (hp : p ≠ 0) : CharZero (CyclotomicIntegers p) :=
  have := nontrivial hp
  ⟨(FaithfulSMul.algebraMap_injective _ _).comp (algebraMap ℕ ℤ).injective_nat⟩

instance : CharZero (CyclotomicIntegers p) := charZero hpri.out.ne_zero

end CyclotomicIntegers
end
