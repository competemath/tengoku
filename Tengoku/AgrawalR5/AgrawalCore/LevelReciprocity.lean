/-
Reciprocity at the primitive H4 level.

For a split root `γ` of `X² - 5X + 5`, the element `-γ` is a square
precisely in the cyclotomic branch `p ≡ 1 (mod 5)`.  Combined with the
exact primitive order `4rs`, this determines the parity of the residual
multiplier `(p-1)/(4rs)`.

This removes half of the residue classes available to a hypothetical
split H4 prime.  It does not prove H4.
-/
import Tengoku.AgrawalR5.AgrawalCore.PrimitiveScalarBridge
import Tengoku.AgrawalR5.AgrawalCore.Reciprocity
import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.Seed.GroupTheory.Perm.Cycle.Type
import Tengoku.Seed.RingTheory.ZMod.UnitsCyclic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

private theorem two_ne_zero_mod_prime (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hp : p ∣ 2 :=
    (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hzero
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hp)

private theorem five_ne_zero_mod_prime (hp5 : p ≠ 5) :
    (5 : ZMod p) ≠ 0 := by
  intro hzero
  have hp : p ∣ 5 :=
    (CharP.cast_eq_zero_iff (ZMod p) p 5).mp hzero
  exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hp)

omit [Fact p.Prime] in
private theorem mod_five_one_iff_dvd_sub_one (hp0 : 0 < p) :
    p % 5 = 1 ↔ 5 ∣ p - 1 := by
  constructor <;> intro h
  · omega
  · omega

private theorem cyclotomic_five_of_pow_eq_one {z : ZMod p}
    (hzpow : z ^ 5 = 1) (hz1 : z ≠ 1) :
    z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0 := by
  have hprod :
      (z - 1) * (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) = 0 := by
    calc
      (z - 1) * (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) = z ^ 5 - 1 := by ring
      _ = 0 := by rw [hzpow]; ring
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hz1)

private theorem period_roots_sum_and_product {z : ZMod p}
    (hcyclo : z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0) :
    let v₁ := z - z ^ 4
    let v₂ := z ^ 2 - z ^ 3
    (-v₁ ^ 2) + (-v₂ ^ 2) = 5 ∧
      (-v₁ ^ 2) * (-v₂ ^ 2) = 5 := by
  dsimp
  constructor
  · linear_combination
      -(z ^ 4 - z ^ 3 + z ^ 2 - 5 * z + 5) * hcyclo
  · linear_combination
      (z ^ 10 - 3 * z ^ 9 + 3 * z ^ 8 - 3 * z ^ 7 +
        6 * z ^ 6 - 5 * z ^ 5 + 5 * z - 5) * hcyclo

/-- **Cyclotomic square criterion for the golden level.**

For either root `γ` of `X² - 5X + 5` over `ZMod p`, assuming `p ≠ 2,5`,
`-γ` is a square exactly when `p ≡ 1 (mod 5)`.

The forward implication reconstructs a nontrivial fifth root of unity
from a square root of `-γ`.  The reverse implication uses an element of
order five and the two Gaussian periods
`-(z-z⁴)²`, `-(z²-z³)²`, whose sum and product are both `5`.
@isnad1 id=iff.3h2v.s7.fc33d84bcfce from=translated src=- shape=b490b37c vocab=a406124c
-/
theorem neg_gamma_isSquare_iff_mod_five_one
    (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5) :
    IsSquare (-γ) ↔ p % 5 = 1 := by
  constructor
  · rintro ⟨v, hv⟩
    have hv2 : v ^ 2 = -γ := by simpa [pow_two] using hv.symm
    let a : ZMod p := γ - 3
    let z : ZMod p := (a + v) / 2
    have ha : a ^ 2 + a = 1 := by
      dsimp [a]
      linear_combination hγ
    have hvdisc : v ^ 2 = a ^ 2 - 4 := by
      rw [hv2]
      dsimp [a]
      linear_combination -hγ
    have hzquad : z ^ 2 = a * z - 1 := by
      dsimp [z]
      field_simp [two_ne_zero_mod_prime hp2]
      linear_combination hvdisc
    have hz3 : z ^ 3 = -a * z - a := by
      calc
        z ^ 3 = z * z ^ 2 := by ring
        _ = z * (a * z - 1) := by rw [hzquad]
        _ = a * z ^ 2 - z := by ring
        _ = a * (a * z - 1) - z := by rw [hzquad]
        _ = -a * z - a := by
          linear_combination z * ha
    have hz4 : z ^ 4 = -z + a := by
      calc
        z ^ 4 = z * z ^ 3 := by ring
        _ = z * (-a * z - a) := by rw [hz3]
        _ = -a * z ^ 2 - a * z := by ring
        _ = -a * (a * z - 1) - a * z := by rw [hzquad]
        _ = -z + a := by
          linear_combination -z * ha
    have hz5 : z ^ 5 = 1 := by
      calc
        z ^ 5 = z * z ^ 4 := by ring
        _ = z * (-z + a) := by rw [hz4]
        _ = -(z ^ 2) + a * z := by ring
        _ = -(a * z - 1) + a * z := by rw [hzquad]
        _ = 1 := by ring
    have hz1 : z ≠ 1 := by
      intro hz
      have ha2 : a = 2 := by
        rw [hz] at hzquad
        norm_num at hzquad
        linear_combination -hzquad
      have h5zero : (5 : ZMod p) = 0 := by
        rw [ha2] at ha
        norm_num at ha ⊢
        linear_combination ha
      exact five_ne_zero_mod_prime hp5 h5zero
    have hzord : orderOf z = 5 :=
      orderOf_eq_prime hz5 hz1
    have hz0 : z ≠ 0 := by
      intro hz
      rw [hz, zero_pow (by norm_num)] at hz5
      exact zero_ne_one hz5
    have horddvd : orderOf z ∣ p - 1 :=
      ZMod.orderOf_dvd_card_sub_one hz0
    have h5dvd : 5 ∣ p - 1 := by simpa [hzord] using horddvd
    exact (mod_five_one_iff_dvd_sub_one (Fact.out : p.Prime).pos).2 h5dvd
  · intro hpmod
    have h5dvd : 5 ∣ Fintype.card ((ZMod p)ˣ) := by
      rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
      exact (mod_five_one_iff_dvd_sub_one (Fact.out : p.Prime).pos).1 hpmod
    obtain ⟨zu, hzuord⟩ :=
      exists_prime_orderOf_dvd_card (G := (ZMod p)ˣ) 5 h5dvd
    let z : ZMod p := zu
    have hzpow : z ^ 5 = 1 := by
      change ((zu ^ 5 : (ZMod p)ˣ) : ZMod p) = 1
      rw [← hzuord, pow_orderOf_eq_one]
      rfl
    have hz1 : z ≠ 1 := by
      intro hz
      have hzu1 : zu = 1 := Units.ext hz
      rw [hzu1, orderOf_one] at hzuord
      norm_num at hzuord
    have hcyclo :
        z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0 :=
      cyclotomic_five_of_pow_eq_one hzpow hz1
    let v₁ : ZMod p := z - z ^ 4
    let v₂ : ZMod p := z ^ 2 - z ^ 3
    let y₁ : ZMod p := -v₁ ^ 2
    let y₂ : ZMod p := -v₂ ^ 2
    have hperiod := period_roots_sum_and_product hcyclo
    have hsum : y₁ + y₂ = 5 := by simpa [y₁, y₂, v₁, v₂] using hperiod.1
    have hprod : y₁ * y₂ = 5 := by simpa [y₁, y₂, v₁, v₂] using hperiod.2
    have hfactor : (γ - y₁) * (γ - y₂) = 0 := by
      linear_combination hγ - γ * hsum + hprod
    rcases mul_eq_zero.mp hfactor with hy | hy
    · refine ⟨v₁, ?_⟩
      have hgy : γ = y₁ := sub_eq_zero.mp hy
      simp [hgy, y₁, pow_two]
    · refine ⟨v₂, ?_⟩
      have hgy : γ = y₂ := sub_eq_zero.mp hy
      simp [hgy, y₂, pow_two]

/-- A root of the golden quadratic exposes an explicit square root of
`5`, namely `2γ-5`.
@isnad1 id=issquare.1h2v.s7.9a46c61373c8 from=translated src=- shape=ad115cca vocab=1bd888d5
-/
theorem five_isSquare_of_golden_root
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5) :
    IsSquare (5 : ZMod p) := by
  refine ⟨2 * γ - 5, ?_⟩
  linear_combination -4 * hγ

/-- Outside characteristics `2` and `5`, a root of
`X²-5X+5` can exist over the prime field only in one of the two split
residue classes modulo `5`.
@isnad1 id=or.3h2v.s7.5a0fb62fc821 from=translated src=- shape=6d39038c vocab=9de8b228
-/
theorem golden_root_mod_five_split
    (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5) :
    p % 5 = 1 ∨ p % 5 = 4 := by
  have hsq : IsSquare (5 : ZMod p) :=
    five_isSquare_of_golden_root γ hγ
  have hlt : p % 5 < 5 := Nat.mod_lt p (by norm_num)
  have hcases :
      p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
    omega
  rcases hcases with h0 | h1 | h2 | h3 | h4
  · have h5p : 5 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h0
    have hpEq : 5 = p :=
      (Nat.prime_dvd_prime_iff_eq fact_prime_five.out Fact.out).mp h5p
    exact absurd hpEq.symm hp5
  · exact Or.inl h1
  · exact absurd hsq (not_isSquare_five hp2 (Or.inl h2))
  · exact absurd hsq (not_isSquare_five hp2 (Or.inr h3))
  · exact Or.inr h4

private theorem pow_half_order_eq_neg_one
    (_hp2 : p ≠ 2) {x : ZMod p} {m : ℕ}
    (hmpos : 0 < m) (hmEven : Even m) (hord : orderOf x = m) :
    x ^ (m / 2) = -1 := by
  obtain ⟨a, ha⟩ := hmEven
  have hmhalf : m / 2 + m / 2 = m := by omega
  have hsq : (x ^ (m / 2)) * (x ^ (m / 2)) = 1 := by
    rw [← pow_add, hmhalf, ← hord, pow_orderOf_eq_one]
  have hne : x ^ (m / 2) ≠ 1 := by
    intro hone
    have hdvd₀ : orderOf x ∣ m / 2 :=
      orderOf_dvd_of_pow_eq_one hone
    have hdvd : m ∣ m / 2 := by simpa [hord] using hdvd₀
    have hlt : m / 2 < m := Nat.div_lt_self hmpos (by norm_num)
    have hhalfpos : 0 < m / 2 := by omega
    exact (Nat.not_dvd_of_pos_of_lt hhalfpos hlt) hdvd
  rcases mul_self_eq_one_iff.mp hsq with hone | hneg
  · exact absurd hone hne
  · exact hneg

/-- If a split primitive element has exact order `m`, where `4 ∣ m`,
and `p-1 = m*h`, then `-x` is a square precisely when the residual
multiplier `h` is even.
@isnad1 id=iff.5h4v.s7.6f4377634dea from=translated src=- shape=ae194966 vocab=01ff9cbd
-/
theorem neg_isSquare_iff_residual_multiplier_even
    (hp2 : p ≠ 2) {x : ZMod p} {m h : ℕ}
    (hx0 : x ≠ 0) (hm4 : 4 ∣ m)
    (hord : orderOf x = m) (hfactor : p - 1 = m * h) :
    IsSquare (-x) ↔ Even h := by
  have hmpos : 0 < m := by
    have hpgt : 1 < p := (Fact.out : p.Prime).one_lt
    have hpsub : 0 < p - 1 := Nat.sub_pos_of_lt hpgt
    by_contra hm
    have hmzero : m = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp hm)
    rw [hmzero, zero_mul] at hfactor
    omega
  have hmEven : Even m :=
    even_iff_two_dvd.mpr (dvd_trans (by norm_num : 2 ∣ 4) hm4)
  have hmHalfEven : Even (m / 2) := by
    have h2m : 2 ∣ m :=
      dvd_trans (by norm_num : 2 ∣ 4) hm4
    exact even_iff_two_dvd.mpr <|
      (Nat.dvd_div_iff_mul_dvd h2m).2 (by simpa using hm4)
  have hpOdd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hpHalf :
      p / 2 = (m / 2) * h := by
    obtain ⟨b, hb⟩ := hpOdd
    have hpdiv : p / 2 = b := by omega
    rw [hpdiv]
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
    calc
      2 * b = p - 1 := by omega
      _ = m * h := hfactor
      _ = (2 * (m / 2)) * h := by
        rw [Nat.two_mul_div_two_of_even hmEven]
      _ = 2 * ((m / 2) * h) := by ring
  have hxhalf : x ^ (m / 2) = -1 :=
    pow_half_order_eq_neg_one hp2 hmpos hmEven hord
  have hpow :
      (-x) ^ (p / 2) = (-1 : ZMod p) ^ h := by
    rw [hpHalf, pow_mul, hmHalfEven.neg_pow, hxhalf]
  have hnegx0 : (-x : ZMod p) ≠ 0 := neg_ne_zero.mpr hx0
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  rw [FiniteField.isSquare_iff hchar hnegx0, ZMod.card, hpow]
  apply neg_one_pow_eq_one_iff_even
  intro hneg
  have h2zero : (2 : ZMod p) = 0 := by
    calc
      (2 : ZMod p) = 1 - (-1) := by ring
      _ = 0 := by rw [hneg]; ring
  exact two_ne_zero_mod_prime hp2 h2zero

/-- **Parity form of level reciprocity.**

For a split root of `X²-5X+5` having exact order `m`, with `4 ∣ m`,
the residual multiplier in `p-1=m*h` is even exactly in the branch
`p ≡ 1 (mod 5)`.
@isnad1 id=iff.6h4v.s8.7e32f57e956f from=translated src=- shape=285499ae vocab=3d6cf1a3
-/
theorem residual_multiplier_even_iff_mod_five_one
    (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    {m h : ℕ} (hm4 : 4 ∣ m)
    (hord : orderOf γ = m) (hfactor : p - 1 = m * h) :
    Even h ↔ p % 5 = 1 := by
  have hγ0 : γ ≠ 0 := by
    intro hz
    rw [hz] at hγ
    norm_num at hγ
    exact five_ne_zero_mod_prime hp5 hγ
  exact
    (neg_isSquare_iff_residual_multiplier_even hp2 hγ0 hm4 hord hfactor).symm.trans
      (neg_gamma_isSquare_iff_mod_five_one hp2 hp5 γ hγ)

omit [Fact p.Prime] in
/-- The congruence branch is also exactly the divisibility of the
residual multiplier by `5`, provided the primitive level itself is
prime to `5`.
@isnad1 id=iff.3h3v.s6.be55c8c6155e from=translated src=- shape=a857043d vocab=bd114726
-/
theorem mod_five_one_iff_five_dvd_residual_multiplier
    {m h : ℕ} (hp0 : 0 < p) (h5m : ¬5 ∣ m)
    (hfactor : p - 1 = m * h) :
    p % 5 = 1 ↔ 5 ∣ h := by
  rw [mod_five_one_iff_dvd_sub_one hp0, hfactor]
  constructor
  · intro hprod
    exact (fact_prime_five.out.dvd_mul.mp hprod).resolve_left h5m
  · exact fun hh => dvd_mul_of_dvd_right hh m

/-- **Direct four-coefficient level-reciprocity theorem.**

A good split divisor of the canonical four-coefficient integer has
`p-1 = 4rs*h`.  The residual multiplier is even exactly for
`p ≡ 1 (mod 5)`.  This is the kernel form of the factor-two restriction
on hypothetical split H4 primes.
@isnad1 id=iff.9h6v.s8.d0a575d9960a from=translated src=- shape=5c9d508b vocab=eef49e7c
-/
theorem dvd_D_residual_multiplier_even_iff_mod_five_one
    (hp5 : p ≠ 5) (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    {h : ℕ} (hfactor : p - 1 = (4 * r * s) * h) :
    Even h ↔ p % 5 = 1 := by
  have hp2 : p ≠ 2 := by
    intro hpEq
    subst p
    apply hpm
    exact ⟨2 * r * s, by ring⟩
  have hord :
      orderOf γ = 4 * r * s :=
    (dvd_primitiveFourCoefficientD_exact_order_profile
      hp5 hr hs hkpos hpm hsig γ hγ hD).1
  exact residual_multiplier_even_iff_mod_five_one
    hp2 hp5 γ hγ (by simp [mul_assoc]) hord hfactor

/-- **Full residual-multiplier form.**

If the primitive level `4rs` is also prime to `5`, then the two
apparently different restrictions on the residual multiplier coincide:
its parity and its divisibility by `5` both detect the split
cyclotomic branch `p ≡ 1 (mod 5)`.
@isnad1 id=iff.10h6v.s8.681afb1adc5d from=translated src=- shape=15e1ab0a vocab=184f67a4
-/
theorem dvd_D_residual_multiplier_even_iff_five_dvd
    (hp5 : p ≠ 5) (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s) (h5level : ¬5 ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    {h : ℕ} (hfactor : p - 1 = (4 * r * s) * h) :
    Even h ↔ 5 ∣ h := by
  exact
    (dvd_D_residual_multiplier_even_iff_mod_five_one
      hp5 hr hs hkpos hpm hsig γ hγ hD hfactor).trans
      (mod_five_one_iff_five_dvd_residual_multiplier
        (Fact.out : p.Prime).pos h5level hfactor)

/-- In the good H4 range the branch `p ≡ 1 (mod 5)` is equivalently
the divisibility `10 ∣ h`; otherwise `h` is odd and prime to `5`.
Thus five of the ten residue classes of the residual multiplier are
excluded before any search.
@isnad1 id=iff.10h6v.s8.467f80d93d41 from=translated src=- shape=fc992ebe vocab=670af792
-/
theorem dvd_D_ten_dvd_residual_multiplier_iff_mod_five_one
    (hp5 : p ≠ 5) (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s) (h5level : ¬5 ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    {h : ℕ} (hfactor : p - 1 = (4 * r * s) * h) :
    10 ∣ h ↔ p % 5 = 1 := by
  have heven :
      Even h ↔ p % 5 = 1 :=
    dvd_D_residual_multiplier_even_iff_mod_five_one
      hp5 hr hs hkpos hpm hsig γ hγ hD hfactor
  have hevenFive :
      Even h ↔ 5 ∣ h :=
    dvd_D_residual_multiplier_even_iff_five_dvd
      hp5 hr hs hkpos hpm h5level hsig γ hγ hD hfactor
  constructor
  · intro h10
    apply heven.mp
    exact even_iff_two_dvd.mpr <|
      dvd_trans (by norm_num : 2 ∣ 10) h10
  · intro hpmod
    have h2 : 2 ∣ h := even_iff_two_dvd.mp (heven.mpr hpmod)
    have h5 : 5 ∣ h := hevenFive.mp (heven.mpr hpmod)
    have hlcm : Nat.lcm 2 5 ∣ h := Nat.lcm_dvd h2 h5
    norm_num at hlcm ⊢
    exact hlcm

/-- **Two-branch residual signature.**

For a fixed primitive level, the residual multiplier does not occupy
five arbitrary classes modulo `10`.  It is either divisible by `10`,
or it is odd and satisfies the single congruence forced by the
`p ≡ 4 (mod 5)` branch.
@isnad1 id=or.10h6v.s8.e0b840e63423 from=translated src=- shape=f36ab94e vocab=a324139f
-/
theorem dvd_D_residual_multiplier_branch_dichotomy
    (hp5 : p ≠ 5) (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s) (h5level : ¬5 ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    {h : ℕ} (hfactor : p - 1 = (4 * r * s) * h) :
    10 ∣ h ∨ (Odd h ∧ (4 * r * s * h) % 5 = 3) := by
  have hp2 : p ≠ 2 := by
    intro hpEq
    subst p
    apply hpm
    exact ⟨2 * r * s, by ring⟩
  have hsplit := golden_root_mod_five_split hp2 hp5 γ hγ
  rcases hsplit with hp1 | hp4
  · exact Or.inl <|
      (dvd_D_ten_dvd_residual_multiplier_iff_mod_five_one
        hp5 hr hs hkpos hpm h5level hsig γ hγ hD hfactor).mpr hp1
  · right
    have hnotEven : ¬Even h := by
      intro heven
      have hp1 :
          p % 5 = 1 :=
        (dvd_D_residual_multiplier_even_iff_mod_five_one
          hp5 hr hs hkpos hpm hsig γ hγ hD hfactor).mp heven
      omega
    refine ⟨Nat.not_even_iff_odd.mp hnotEven, ?_⟩
    rw [← hfactor]
    omega

/-- **Class-specific residual table.**

In the `p ≡ 4 (mod 5)` branch, `rs mod 5` determines the unique
remaining class of the residual multiplier modulo `10`.  The four
classes are respectively `7,1,9,3`.
@isnad1 id=and.10h6v.s9.cfcabf13f691 from=translated src=- shape=7ac7647c vocab=670af792
-/
theorem dvd_D_residual_multiplier_mod_ten_table
    (hp5 : p ≠ 5) (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    {h : ℕ} (hfactor : p - 1 = (4 * r * s) * h)
    (hp4 : p % 5 = 4) :
    ((r * s) % 5 = 1 → h % 10 = 7) ∧
      ((r * s) % 5 = 2 → h % 10 = 1) ∧
      ((r * s) % 5 = 3 → h % 10 = 9) ∧
      ((r * s) % 5 = 4 → h % 10 = 3) := by
  have hp2 : p ≠ 2 := by
    intro hpEq
    subst p
    apply hpm
    exact ⟨2 * r * s, by ring⟩
  have hnotEven : ¬Even h := by
    intro heven
    have hp1 :
        p % 5 = 1 :=
      (dvd_D_residual_multiplier_even_iff_mod_five_one
        hp5 hr hs hkpos hpm hsig γ hγ hD hfactor).mp heven
    omega
  have hoddmod : h % 2 = 1 :=
    Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hnotEven)
  have hrel : (4 * r * s * h) % 5 = 3 := by
    rw [← hfactor]
    omega
  have htenTwo : h % 10 % 2 = h % 2 :=
    Nat.mod_mod_of_dvd h (by norm_num)
  have htenFive : h % 10 % 5 = h % 5 :=
    Nat.mod_mod_of_dvd h (by norm_num)
  have htenLt : h % 10 < 10 := Nat.mod_lt h (by norm_num)
  constructor
  · intro hrs
    have hh5 : h % 5 = 2 := by
      have hrsMod : r * s ≡ 1 [MOD 5] := by
        change (r * s) % 5 = 1
        exact hrs
      have hmul :
          4 * 1 * h ≡ 4 * (r * s) * h [MOD 5] :=
        (((Nat.ModEq.refl 4).mul hrsMod).mul (Nat.ModEq.refl h)).symm
      have hrelMod : 4 * (r * s) * h ≡ 3 [MOD 5] := by
        change (4 * (r * s) * h) % 5 = 3
        simpa [mul_assoc] using hrel
      have hh : (4 * h) % 5 = 3 := by
        change 4 * 1 * h ≡ 3 [MOD 5]
        exact hmul.trans hrelMod
      have hhLt : h % 5 < 5 := Nat.mod_lt h (by norm_num)
      omega
    omega
  constructor
  · intro hrs
    have hh5 : h % 5 = 1 := by
      have hrsMod : r * s ≡ 2 [MOD 5] := by
        change (r * s) % 5 = 2
        exact hrs
      have hmul :
          4 * 2 * h ≡ 4 * (r * s) * h [MOD 5] :=
        (((Nat.ModEq.refl 4).mul hrsMod).mul (Nat.ModEq.refl h)).symm
      have hrelMod : 4 * (r * s) * h ≡ 3 [MOD 5] := by
        change (4 * (r * s) * h) % 5 = 3
        simpa [mul_assoc] using hrel
      have hh : (8 * h) % 5 = 3 := by
        change 4 * 2 * h ≡ 3 [MOD 5]
        exact hmul.trans hrelMod
      have hhLt : h % 5 < 5 := Nat.mod_lt h (by norm_num)
      omega
    omega
  constructor
  · intro hrs
    have hh5 : h % 5 = 4 := by
      have hrsMod : r * s ≡ 3 [MOD 5] := by
        change (r * s) % 5 = 3
        exact hrs
      have hmul :
          4 * 3 * h ≡ 4 * (r * s) * h [MOD 5] :=
        (((Nat.ModEq.refl 4).mul hrsMod).mul (Nat.ModEq.refl h)).symm
      have hrelMod : 4 * (r * s) * h ≡ 3 [MOD 5] := by
        change (4 * (r * s) * h) % 5 = 3
        simpa [mul_assoc] using hrel
      have hh : (12 * h) % 5 = 3 := by
        change 4 * 3 * h ≡ 3 [MOD 5]
        exact hmul.trans hrelMod
      have hhLt : h % 5 < 5 := Nat.mod_lt h (by norm_num)
      omega
    omega
  · intro hrs
    have hh5 : h % 5 = 3 := by
      have hrsMod : r * s ≡ 4 [MOD 5] := by
        change (r * s) % 5 = 4
        exact hrs
      have hmul :
          4 * 4 * h ≡ 4 * (r * s) * h [MOD 5] :=
        (((Nat.ModEq.refl 4).mul hrsMod).mul (Nat.ModEq.refl h)).symm
      have hrelMod : 4 * (r * s) * h ≡ 3 [MOD 5] := by
        change (4 * (r * s) * h) % 5 = 3
        simpa [mul_assoc] using hrel
      have hh : (16 * h) % 5 = 3 := by
        change 4 * 4 * h ≡ 3 [MOD 5]
        exact hmul.trans hrelMod
      have hhLt : h % 5 < 5 := Nat.mod_lt h (by norm_num)
      omega
    omega

/-- The class-specific residue table gives four explicit lower bounds
for a hypothetical split primitive divisor in the `p ≡ 4 (mod 5)`
branch.
@isnad1 id=and.10h6v.s9.65bbf8bc643d from=translated src=- shape=722358e7 vocab=dd1948f2
-/
theorem dvd_D_class_specific_lower_bounds
    (hp5 : p ≠ 5) (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    {h : ℕ} (hfactor : p - 1 = (4 * r * s) * h)
    (hp4 : p % 5 = 4) :
    ((r * s) % 5 = 1 → 28 * r * s + 1 ≤ p) ∧
      ((r * s) % 5 = 2 → 4 * r * s + 1 ≤ p) ∧
      ((r * s) % 5 = 3 → 36 * r * s + 1 ≤ p) ∧
      ((r * s) % 5 = 4 → 12 * r * s + 1 ≤ p) := by
  have htable :=
    dvd_D_residual_multiplier_mod_ten_table
      hp5 hr hs hkpos hpm hsig γ hγ hD hfactor hp4
  have hpEq : p = (4 * r * s) * h + 1 := by
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    omega
  constructor
  · intro hrs
    have hhrem : h % 10 = 7 := htable.1 hrs
    have hhle : 7 ≤ h := by
      have := Nat.mod_le h 10
      omega
    have hmul : (4 * r * s) * 7 ≤ (4 * r * s) * h :=
      Nat.mul_le_mul_left (4 * r * s) hhle
    calc
      28 * r * s + 1 = (4 * r * s) * 7 + 1 := by ring
      _ ≤ (4 * r * s) * h + 1 := Nat.add_le_add_right hmul 1
      _ = p := hpEq.symm
  constructor
  · intro hrs
    have hhrem : h % 10 = 1 := htable.2.1 hrs
    have hhle : 1 ≤ h := by
      have := Nat.mod_le h 10
      omega
    have hmul : (4 * r * s) * 1 ≤ (4 * r * s) * h :=
      Nat.mul_le_mul_left (4 * r * s) hhle
    calc
      4 * r * s + 1 = (4 * r * s) * 1 + 1 := by ring
      _ ≤ (4 * r * s) * h + 1 := Nat.add_le_add_right hmul 1
      _ = p := hpEq.symm
  constructor
  · intro hrs
    have hhrem : h % 10 = 9 := htable.2.2.1 hrs
    have hhle : 9 ≤ h := by
      have := Nat.mod_le h 10
      omega
    have hmul : (4 * r * s) * 9 ≤ (4 * r * s) * h :=
      Nat.mul_le_mul_left (4 * r * s) hhle
    calc
      36 * r * s + 1 = (4 * r * s) * 9 + 1 := by ring
      _ ≤ (4 * r * s) * h + 1 := Nat.add_le_add_right hmul 1
      _ = p := hpEq.symm
  · intro hrs
    have hhrem : h % 10 = 3 := htable.2.2.2 hrs
    have hhle : 3 ≤ h := by
      have := Nat.mod_le h 10
      omega
    have hmul : (4 * r * s) * 3 ≤ (4 * r * s) * h :=
      Nat.mul_le_mul_left (4 * r * s) hhle
    calc
      12 * r * s + 1 = (4 * r * s) * 3 + 1 := by ring
      _ ≤ (4 * r * s) * h + 1 := Nat.add_le_add_right hmul 1
      _ = p := hpEq.symm

end AgrawalCore
