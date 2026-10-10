import Tengoku

open Polynomial Finset

open scoped BigOperators

/-!
# The radical part

In this document we define what it means to be the radical part (squarefree part)
of an element in a commutative ring.

## Main definition:
- `IsRadicalPart` : predicate characterizing the radical of an element.

## Main results:
- `isRadicalPart_of_coprime_derivative_of_dvd_of_dvd_pow` : certifies the radical of a polynomial.
- `self_isRadicalPart_of_coprime'` : gives conditions that guarantee that the
  reduction of a polynomial is its own radical.  -/

variable {R : Type*} [CommMonoidWithZero R]

/-- `b` is the radical part of `a` if it has the same prime divisors as `a` and is squarefree· -/
def IsRadicalPart (b : R) (a : R) : Prop :=
  (∀ p : R, Prime p → (p ∣ a ↔ p ∣ b)) ∧ Squarefree b

/--
@isnad1 id=iff.0h3v.s5.64b823f5b779 from=translated src=- shape=a051d2b9 vocab=f673fed1
-/
lemma isRadicalPart_def (b : R) (a : R) :
    IsRadicalPart b a ↔ (∀ p : R, Prime p → (p ∣ a ↔ p ∣ b)) ∧ Squarefree b :=
  Iff.rfl

/-- If `b` is a squarefree element that divides `a`, and such that `a` divides a power of `b`, then
 `b` is the radical part of `a`·
@isnad1 id=isradica.3h3v.s6.23fea0165b2f from=translated src=- shape=1389f936 vocab=cc640307
-/
lemma isRadicalPart_of_dvd_pow {R : Type*} [CommMonoidWithZero R] {a b : R}
    (hg : Squarefree b) (hdvd : b ∣ a ) (h : ∃ n : ℕ, a ∣ b ^ n) :
    IsRadicalPart b a := by
  obtain ⟨n, hn⟩ := h
  rw [isRadicalPart_def]
  constructor
  intro a hap; constructor
  · intro hadvd
    exact Prime.dvd_of_dvd_pow hap (dvd_trans hadvd hn)
  · intro hdvd2; exact dvd_trans hdvd2 hdvd
  exact hg

/-- The radical part of `a` is the radical part of any power of `a`
@isnad1 id=isradica.2h4v.s5.549f15b82e21 from=translated src=- shape=76e601c1 vocab=ccacd821
-/
lemma isRadicalPart_pow_of_isRadicalPart {R : Type*} [CommMonoidWithZero R]
    {a b : R} {n : ℕ} (hn : n ≠ 0) (h : IsRadicalPart b a ) :
    IsRadicalPart b (a ^ n) := by
  rw [isRadicalPart_def] at h ⊢
  refine ⟨?_, h.2⟩
  intro a hap; constructor
  intro hadvd
  exact (h.1 a hap).1 (Prime.dvd_of_dvd_pow hap hadvd)
  intro hagdvd; refine dvd_pow ?_ hn; exact (h.1 a hap).2 hagdvd

/--
@isnad1 id=not.3h4v.s5.fc3814899ece from=translated src=- shape=b3832e6f vocab=462e3901
-/
lemma ne_dvd_of_isCoprime {R : Type*} [CommSemiring R] {a b p : R} (hp : ¬IsUnit p)
    (hgcd : IsCoprime a b) (h : p ∣ a ) : ¬p ∣ b := by
  obtain ⟨t, ht⟩ := h
  by_contra hg
  obtain ⟨q, hq⟩ := hg
  rw [ht, hq, IsCoprime.mul_left_iff, IsCoprime.mul_right_iff, isCoprime_self] at hgcd
  exact hp hgcd.1.1

/-- The associate of a radical part of `a` is also a radical part·
@isnad1 id=isradica.2h4v.s5.2472c91cd03d from=translated src=- shape=b6abee4f vocab=f06f75f8
-/
lemma associated_isRadicalPart_of_isRadicalPart {R : Type*} [CommMonoidWithZero R] {a b c : R}
    (ha : Associated b c) (hr : IsRadicalPart b a ) : IsRadicalPart c a := by
  rw [isRadicalPart_def] at hr ⊢
  rcases hr with ⟨h1, h2⟩
  constructor
  · simp_rw [Associated.dvd_iff_dvd_right ha] at h1
    exact h1
  · exact Squarefree.squarefree_of_dvd (Associated.dvd_dvd ha).2 h2

/--  The radical part of the product of two coprime elements
  is the product of the radical parts of each of these elements·
@isnad1 id=isradica.3h5v.s6.ce2efa6b7b1a from=translated src=- shape=abc9db95 vocab=75e83b46
-/
lemma mul_isRadicalPart_mul {R : Type*} [CommSemiring R] [IsDomain R] [DecompositionMonoid R]
    (a b c d : R) (hgcd : IsRelPrime b d) (hr1 : IsRadicalPart b a ) (hr2 : IsRadicalPart d c) :
    IsRadicalPart (b * d) (a * c) := by
  constructor
  intro a hap
  · constructor
    · intro hadvd
      cases Prime.dvd_or_dvd hap hadvd
      case _ h_1 => exact dvd_mul_of_dvd_left ((hr1.1 a hap).1 h_1) d
      case _ h_1 => exact dvd_mul_of_dvd_right ((hr2.1 a hap).1 h_1) b
    · intro hadvd
      cases Prime.dvd_or_dvd hap hadvd
      case _ h_1 => apply dvd_mul_of_dvd_left; exact (hr1.1 a hap).2 h_1
      case _ h_1 => apply dvd_mul_of_dvd_right; exact (hr2.1 a hap).2 h_1
  · refine (squarefree_mul_iff (x := b) (y := d)).2 ?_
    exact ⟨hgcd, hr1.2, hr2.2⟩

open UniqueFactorizationMonoid

/-- A certificate for the radical part of polynomials:
  `k` is the radical of `f` if `k ∣ f`, there is `n` such that `f ∣ k ^ n `,
  and `k` and the derivative of `k` are coprime.
@isnad1 id=isradica.3h3v.s8.af44d463dc2d from=translated src=- shape=88e36924 vocab=5ca9885a
-/
lemma isRadicalPart_of_coprime_derivative_of_dvd_of_dvd_pow {K : Type*}
    [CommSemiring K] [DecidableEq K] (f k : Polynomial K)
    (h : k ∣ f ) (h2 : ∃ n : ℕ, f ∣ k ^ n) (h3 : ∃ a b , a * k + b * derivative k = 1) :
    IsRadicalPart k f := by
  rw [← Polynomial.separable_def'] at h3
  refine isRadicalPart_of_dvd_pow (Polynomial.Separable.squarefree h3) h h2

/-- If a polynomial is coprime with its derivative, then it is its own radical.
@isnad1 id=isradica.1h2v.s7.045e48aee103 from=translated src=- shape=f1a03f83 vocab=6ea0d15b
-/
lemma self_isRadicalPart_of_gcd_unit {K : Type*} [CommSemiring K] [DecidableEq K] (f : Polynomial K)
    (hgcd : IsCoprime f (derivative f)) : IsRadicalPart f f := by
  refine isRadicalPart_of_coprime_derivative_of_dvd_of_dvd_pow f f (dvd_refl f) ?_ ?_
  · use 1
    simp only [pow_one, dvd_refl]
  · exact hgcd

/-- If the gcd of a polynomial `f` in `ZMod p` and its derivative is associated to an integer
coprime to `p`, then `f` is the radical of `f`·
@isnad1 id=isradica.2h3v.s9.61a53b221076 from=translated src=- shape=03325416 vocab=8a4a5946
-/
lemma self_isRadicalPart_of_coprime {p n : ℕ}
    (f : Polynomial <| ZMod p) (hgcd : ∃ a b ,  a * f + b * (derivative f) = n)
    (hc : n.Coprime p) : IsRadicalPart f f := by
  have : Associated (n : Polynomial <| ZMod p) 1 := by
    rw [← C_eq_natCast, associated_one_iff_isUnit, Polynomial.isUnit_C]
    use ZMod.unitOfCoprime n hc; exact ZMod.coe_unitOfCoprime n hc
  obtain ⟨k,hk⟩:= this
  obtain ⟨a',b',hab'⟩ := hgcd
  refine isRadicalPart_of_coprime_derivative_of_dvd_of_dvd_pow f f (dvd_refl f) ?_ ?_
  · use 1
    simp only [pow_one, dvd_refl]
  · use (k * a') , (k * b')
    rw [mul_assoc, mul_assoc, ← mul_add, hab', mul_comm, hk]

/-- A more general version of `self_isRadicalPart_of_coprime`
@isnad1 id=isradica.3h6v.s9.8b19ac924f2c from=translated src=- shape=8020a411 vocab=0c1d6b6a
-/
lemma self_isRadicalPart_of_coprime_ideal {K R : Type*} [CommRing R] [CommRing K] [DecidableEq K]
    {n : R } (g : R →+* K ) (P : Ideal R) (hgker : RingHom.ker g = P )
    (f : Polynomial K) (hgcd : ∃ a b , a * f + b * (derivative f) = C (g n))
    (hc : IsCoprime (Ideal.span {n}) P ) : IsRadicalPart f f := by
  have : IsUnit (g n) := by
    obtain ⟨a, ha, b, hb, hab⟩ := IsCoprime.exists hc
    replace ⟨k, hk⟩  := Ideal.mem_span_singleton.1 ha
    apply_fun g at hab
    simp only [hk, map_add, map_mul, map_one] at hab
    have : g b = 0 := by
      rw [← RingHom.mem_ker, hgker ]
      exact hb
    rw [this,  add_zero] at hab
    exact IsUnit.of_mul_eq_one _ hab
  refine self_isRadicalPart_of_gcd_unit f ?_
  obtain ⟨k,hk⟩ := (isUnit_iff_dvd_one).1 this
  obtain ⟨a',b',hab'⟩ := hgcd
  use (C k * a') , (C k * b')
  rw [mul_assoc, mul_assoc, ← mul_add, hab', mul_comm, ← C_mul, ← hk, map_one]

/-- A specialized version of `self_isRadicalPart_of_coprime_ideal`
@isnad1 id=isradica.3h6v.s9.4499df11ebbf from=translated src=- shape=40efa6a2 vocab=0c1d6b6a
-/
lemma self_isRadicalPart_of_coprime' {K R : Type*} [CommRing R] [CommRing K] [DecidableEq K] {π n : R }
    (g : R →+* K ) (hgker : RingHom.ker g = Ideal.span {π} )
    (f : Polynomial K) (hgcd : ∃ a b , a * f + b * (derivative f) = C (g n))
    (hc : IsCoprime n π ) : IsRadicalPart f f := by
  refine self_isRadicalPart_of_coprime_ideal g (Ideal.span {π}) hgker f hgcd ?_
  rw [Ideal.isCoprime_span_singleton_iff]
  exact hc

/-- If `f` is a polynomial in `ZMod p` with derivative `0`,
then the radical part of `f` is the radical part of the `p`-th root of `f`·
@isnad1 id=isradica.2h3v.s9.9269b4f498f9 from=translated src=- shape=6d1ee698 vocab=1df19b1b
-/
lemma radical_pth_power {p : ℕ} [hp : Fact <| Nat.Prime p] (f g : Polynomial <| ZMod p)
    (h1 : derivative f = 0 ) (h2 : IsRadicalPart g (Polynomial.contract p f)) :
    IsRadicalPart g f := by
  rw [← Polynomial.expand_contract p h1 (Nat.Prime.ne_zero hp.out)]
  have : expand (ZMod p) p (contract p f) = contract p f ^ p := by
    rw [ZMod.expand_card (Polynomial.contract p f)]
  rw [this]
  exact isRadicalPart_pow_of_isRadicalPart (Nat.Prime.ne_zero hp.out) h2
