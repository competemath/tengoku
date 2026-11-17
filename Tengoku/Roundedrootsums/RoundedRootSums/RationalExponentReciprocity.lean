/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku.Seed.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Tengoku.Seed.Data.Nat.Factorization.Root
import Tengoku.Roundedrootsums.RoundedRootSums.RationalShiftRealInversion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reciprocity for rational exponents

This file develops the integer-value criterion for rational
powers and derives the floor-floor reciprocity law.
-/

namespace RoundedRootSums
/--
The rational exponent `p / q` viewed as a real number.-/
noncomputable def rationalExponent
    (p q : Nat) : ℝ :=
  (p : ℝ) / (q : ℝ)

/--
The floor sum for the rational exponent `p / q`.-/
noncomputable def rationalFloorPowerSum
    (p q n : Nat) : Nat :=
  realFloorPowerSum
    (rationalExponent p q)
    n

/--
The ceiling sum for the rational exponent `p / q`.-/
noncomputable def rationalCeilPowerSum
    (p q n : Nat) : Nat :=
  realCeilPowerSum
    (rationalExponent p q)
    n

/--
A natural number is a perfect `q`-th power if it is equal
to `a^q` for some natural number `a`.-/
def IsPerfectNatPower
    (q k : Nat) : Prop :=
  ∃ a : Nat, a ^ q = k

/--
A rational exponent `p / q` is positive whenever both
numerator and denominator are positive.
@isnad1 id=lt.2h2v.s5.35a367cc752f from=translated src=- shape=e8b7e832 vocab=3b793685
-/
theorem rationalExponent_pos
    (p q : Nat)
    (hp : 0 < p)
    (hq : 0 < q) :
    0 < rationalExponent p q := by
  have hpR :
      (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp
  have hqR :
      (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq
  unfold rationalExponent
  exact div_pos hpR hqR

/--
For positive natural `p` and `q`, the reciprocal of the
real exponent `p / q` is `q / p`.
@isnad1 id=eq.2h2v.s5.ca110fb7ac2d from=translated src=- shape=bba64e3e vocab=22943793
-/
theorem rationalExponent_inv
    (p q : Nat)
    (hp : 0 < p)
    (hq : 0 < q) :
    (rationalExponent p q)⁻¹ =
      rationalExponent q p := by
  have hpNe :
      (p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hp)
  have hqNe :
      (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  unfold rationalExponent
  field_simp [hpNe, hqNe]

/--
The floor/ceiling reciprocity law specialized to the
rational exponent `p / q`.

Writing `r = ⌊n^(p/q)⌋`, this gives

`F_(p/q)(n) + C_(q/p)(r) = (n + 1) r`.
@isnad1 id=eq.2h3v.s6.4cfc6e1badb4 from=translated src=- shape=55ac8b55 vocab=1eba3494
-/
theorem rationalPowerReciprocity
    (p q n : Nat)
    (hp : 0 < p)
    (hq : 0 < q) :
    rationalFloorPowerSum p q n +
      rationalCeilPowerSum
        q p
        (realFloorPowerCutoff
          (rationalExponent p q)
          n) =
      (n + 1) *
        realFloorPowerCutoff
          (rationalExponent p q)
          n := by
  have hExpPos :
      0 < rationalExponent p q :=
    rationalExponent_pos p q hp hq
  have hInv :
      (rationalExponent p q)⁻¹ =
        rationalExponent q p :=
    rationalExponent_inv p q hp hq
  unfold
    rationalFloorPowerSum
    rationalCeilPowerSum
  rw [← hInv]
  exact
    realPowerReciprocity
      (rationalExponent p q)
      n
      hExpPos

/--
For a positive exponent `q`, a natural number is a perfect
`q`-th power exactly when raising its factorization floor
root back to the `q`-th power recovers the number.
@isnad1 id=iff.1h2v.s5.481d1360ecc8 from=translated src=- shape=041f5f80 vocab=0706b8c8
-/
theorem isPerfectNatPower_iff_floorRoot_pow_eq
    (q k : Nat)
    (hq : 0 < q) :
    IsPerfectNatPower q k ↔
      Nat.floorRoot q k ^ q = k := by
  constructor
  · rintro ⟨a, rfl⟩
    rw [
      Nat.floorRoot_pow_self
        (Nat.ne_of_gt hq)
    ]
  · intro h
    exact
      ⟨Nat.floorRoot q k, h⟩

/--
If `k` is a perfect `q`-th power, then the exponent of
every prime in the factorization of `k` is divisible by `q`.
@isnad1 id=dvd.1h3v.s5.54100cf8461d from=translated src=- shape=713907bb vocab=72d6bf3d
-/
theorem factorization_dvd_of_isPerfectNatPower
    (q k ℓ : Nat)
    (hperfect : IsPerfectNatPower q k) :
    q ∣ k.factorization ℓ := by
  rcases hperfect with ⟨a, rfl⟩
  simp [Nat.factorization_pow]

/--
If `x^q = k^p`, then at every prime coordinate the
corresponding factorization exponents satisfy

`q * v(x) = p * v(k)`.
@isnad1 id=eq.1h5v.s6.5aea221590fa from=translated src=- shape=f8d1f237 vocab=d5c6b2c9
-/
theorem factorization_mul_eq_of_pow_eq_pow
    (p q x k ℓ : Nat)
    (hpow :
      x ^ q = k ^ p) :
    q * x.factorization ℓ =
      p * k.factorization ℓ := by
  have hfac :
      (x ^ q).factorization =
        (k ^ p).factorization := by
    rw [hpow]
  have happ :=
    congrArg
      (fun f : Nat →₀ Nat => f ℓ)
      hfac
  simpa [Nat.factorization_pow] using happ

/--
If `p` and `q` are coprime and

`q * a = p * b`,

then `q ∣ b`.
@isnad1 id=dvd.2h4v.s5.8204a355ec9e from=translated src=- shape=7c7bc808 vocab=77beb901
-/
theorem dvd_right_of_coprime_mul_eq
    (p q a b : Nat)
    (hpq : Nat.Coprime p q)
    (h :
      q * a = p * b) :
    q ∣ b := by
  have hdiv :
      q ∣ p * b := by
    rw [← h]
    exact ⟨a, rfl⟩
  exact
    (hpq.symm.dvd_mul_left).mp hdiv

/--
If `p` and `q` are coprime and `x^q = k^p`, then every
factorization exponent of `k` is divisible by `q`.
@isnad1 id=dvd.2h5v.s6.293accbe1524 from=translated src=- shape=3c7e0663 vocab=12e70805
-/
theorem factorization_dvd_of_coprime_pow_eq_pow
    (p q x k ℓ : Nat)
    (hpq : Nat.Coprime p q)
    (hpow :
      x ^ q = k ^ p) :
    q ∣ k.factorization ℓ := by
  apply
    dvd_right_of_coprime_mul_eq
      p q
      (x.factorization ℓ)
      (k.factorization ℓ)
      hpq
  exact
    factorization_mul_eq_of_pow_eq_pow
      p q x k ℓ hpow

/--
If every factorization exponent of `k` is divisible by the
positive integer `q`, then `k` is a perfect `q`-th power.
@isnad1 id=isperfec.2h2v.s5.95d104df64f9 from=translated src=- shape=505d19b4 vocab=af0ea7c1
-/
theorem isPerfectNatPower_of_factorization_dvd
    (q k : Nat)
    (hq : 0 < q)
    (hdiv :
      ∀ ℓ : Nat,
        q ∣ k.factorization ℓ) :
    IsPerfectNatPower q k := by
  by_cases hk : k = 0
  · subst k
    exact
      ⟨0, by
        simp [Nat.ne_of_gt hq]⟩
  · apply
      (isPerfectNatPower_iff_floorRoot_pow_eq
        q k hq).2
    apply Nat.eq_of_factorization_eq'
    · exact
        pow_ne_zero
          _
          (Nat.floorRoot_ne_zero.2
            ⟨Nat.ne_of_gt hq, hk⟩)
    · exact hk
    · rw [
        Nat.factorization_pow,
        Nat.factorization_floorRoot
      ]
      ext ℓ
      simp only [
        Finsupp.smul_apply,
        Finsupp.floorDiv_apply,
        Nat.floorDiv_eq_div,
        nsmul_eq_mul
      ]
      exact
        Nat.mul_div_cancel'
          (hdiv ℓ)

/--
For positive `q`, a natural number is a perfect `q`-th
power exactly when every exponent in its prime
factorization is divisible by `q`.
@isnad1 id=iff.1h2v.s5.56014b847b2a from=translated src=- shape=7c8610ff vocab=af0ea7c1
-/
theorem isPerfectNatPower_iff_factorization_dvd
    (q k : Nat)
    (hq : 0 < q) :
    IsPerfectNatPower q k ↔
      ∀ ℓ : Nat,
        q ∣ k.factorization ℓ := by
  constructor
  · intro hperfect ℓ
    exact
      factorization_dvd_of_isPerfectNatPower
        q k ℓ hperfect
  · intro hdiv
    exact
      isPerfectNatPower_of_factorization_dvd
        q k hq hdiv

/--
If `p` and `q` are coprime, `q > 0`, and

`x^q = k^p`,

then `k` is a perfect `q`-th power.
@isnad1 id=isperfec.3h4v.s5.4a3df4b9314c from=translated src=- shape=33b227f8 vocab=d0675560
-/
theorem isPerfectNatPower_of_coprime_pow_eq_pow
    (p q x k : Nat)
    (hq : 0 < q)
    (hpq : Nat.Coprime p q)
    (hpow :
      x ^ q = k ^ p) :
    IsPerfectNatPower q k := by
  apply
    isPerfectNatPower_of_factorization_dvd
      q k hq
  intro ℓ
  exact
    factorization_dvd_of_coprime_pow_eq_pow
      p q x k ℓ hpq hpow

/--
Multiplying the rational exponent `p / q` by its positive
denominator recovers `p`.
@isnad1 id=eq.1h2v.s5.9fb068e247e0 from=translated src=- shape=7260d9b4 vocab=c48006b9
-/
theorem rationalExponent_mul_denominator
    (p q : Nat)
    (hq : 0 < q) :
    rationalExponent p q * (q : ℝ) = (p : ℝ) := by
  unfold rationalExponent
  have hqNe :
      (q : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hq
  field_simp [hqNe]

/--
If the rational power of the natural number `k` is the
natural number `x`, then clearing the denominator gives

`k^p = x^q`.
@isnad1 id=eq.2h4v.s5.9dfebcc39314 from=translated src=- shape=c0e8490a vocab=fb493a8c
-/
theorem pow_eq_pow_of_rpow_rational_eq_natCast
    (p q k x : Nat)
    (hq : 0 < q)
    (h :
      Real.rpow
        (k : ℝ)
        (rationalExponent p q) =
      (x : ℝ)) :
    k ^ p = x ^ q := by
  have hkNonneg :
      0 ≤ (k : ℝ) := by
    positivity
  have hexp :
      rationalExponent p q * (q : ℝ) =
        (p : ℝ) :=
    rationalExponent_mul_denominator
      p q hq
  have hpow :
      Real.rpow
          (k : ℝ)
          (rationalExponent p q * (q : ℝ)) =
        Real.rpow
          (x : ℝ)
          (q : ℝ) := by
    calc
      Real.rpow
          (k : ℝ)
          (rationalExponent p q * (q : ℝ)) =
        Real.rpow
          (Real.rpow
            (k : ℝ)
            (rationalExponent p q))
          (q : ℝ) := by
            exact
              Real.rpow_mul
                hkNonneg
                (rationalExponent p q)
                (q : ℝ)
      _ =
        Real.rpow
          (x : ℝ)
          (q : ℝ) := by
            rw [h]
  rw [hexp] at hpow
  have hpowNat :
      (k : ℝ) ^ p =
        (x : ℝ) ^ q := by
    calc
      (k : ℝ) ^ p =
          Real.rpow
            (k : ℝ)
            (p : ℝ) := by
        symm
        exact Real.rpow_natCast (k : ℝ) p
      _ =
          Real.rpow
            (x : ℝ)
            (q : ℝ) :=
        hpow
      _ =
          (x : ℝ) ^ q := by
        exact Real.rpow_natCast (x : ℝ) q
  exact_mod_cast hpowNat

/--
For coprime positive numerator and denominator, if the
rational power `k^(p/q)` is a natural number, then `k`
must be a perfect `q`-th power.
@isnad1 id=isperfec.3h4v.s5.8a0cd91eecf6 from=translated src=- shape=40210ecc vocab=99d524e1
-/
theorem isPerfectNatPower_of_rpow_rational_eq_natCast
    (p q k x : Nat)
    (hq : 0 < q)
    (hpq : Nat.Coprime p q)
    (h :
      Real.rpow
        (k : ℝ)
        (rationalExponent p q) =
      (x : ℝ)) :
    IsPerfectNatPower q k := by
  apply
    isPerfectNatPower_of_coprime_pow_eq_pow
      p q x k hq hpq
  symm
  exact
    pow_eq_pow_of_rpow_rational_eq_natCast
      p q k x hq h

/--
For positive `q`,

`(a^q)^(p/q) = a^p`.
@isnad1 id=eq.1h3v.s5.f8f9f462aaa8 from=translated src=- shape=18dfe633 vocab=fb493a8c
-/
theorem rpow_rational_of_nat_pow
    (p q a : Nat)
    (hq : 0 < q) :
    Real.rpow
        ((a ^ q : Nat) : ℝ)
        (rationalExponent p q) =
      ((a ^ p : Nat) : ℝ) := by
  have haNonneg :
      0 ≤ (a : ℝ) := by
    positivity
  have hexp :
      (q : ℝ) * rationalExponent p q =
        (p : ℝ) := by
    rw [mul_comm]
    exact
      rationalExponent_mul_denominator
        p q hq
  have hqPow :
      (a : ℝ) ^ q =
        Real.rpow
          (a : ℝ)
          (q : ℝ) := by
    symm
    exact
      Real.rpow_natCast
        (a : ℝ)
        q
  calc
    Real.rpow
        ((a ^ q : Nat) : ℝ)
        (rationalExponent p q) =
      Real.rpow
        ((a : ℝ) ^ q)
        (rationalExponent p q) := by
          norm_num
    _ =
      Real.rpow
        (Real.rpow
          (a : ℝ)
          (q : ℝ))
        (rationalExponent p q) := by
          rw [hqPow]
    _ =
      Real.rpow
        (a : ℝ)
        ((q : ℝ) * rationalExponent p q) := by
          symm
          exact
            Real.rpow_mul
              haNonneg
              (q : ℝ)
              (rationalExponent p q)
    _ =
      Real.rpow
        (a : ℝ)
        (p : ℝ) := by
          rw [hexp]
    _ =
      (a : ℝ) ^ p := by
          exact
            Real.rpow_natCast
              (a : ℝ)
              p
    _ =
      ((a ^ p : Nat) : ℝ) := by
          norm_num

/--
Integer-value criterion for reduced rational exponents.

If `p` and `q` are coprime and `q > 0`, then `k^(p/q)` is
a natural number exactly when `k` is a perfect `q`-th
power.
@isnad1 id=iff.2h3v.s5.0f7a7913bcb2 from=translated src=- shape=518e1ab6 vocab=99d524e1
-/
theorem rpow_rational_isNat_iff_isPerfectNatPower
    (p q k : Nat)
    (hq : 0 < q)
    (hpq : Nat.Coprime p q) :
    (∃ x : Nat,
        Real.rpow
            (k : ℝ)
            (rationalExponent p q) =
          (x : ℝ)) ↔
      IsPerfectNatPower q k := by
  constructor
  · rintro ⟨x, hx⟩
    exact
      isPerfectNatPower_of_rpow_rational_eq_natCast
        p q k x hq hpq hx
  · intro hperfect
    rcases hperfect with ⟨a, ha⟩
    subst k
    refine ⟨a ^ p, ?_⟩
    exact
      rpow_rational_of_nat_pow
        p q a hq

/--
For positive `q`, `k` is a perfect `q`-th power exactly
when its numerical `q`-th root raises back to `k`.
@isnad1 id=iff.1h2v.s5.697c268dfc93 from=translated src=- shape=041f5f80 vocab=0639b33b
-/
theorem isPerfectNatPower_iff_nthRoot_pow_eq
    (q k : Nat)
    (hq : 0 < q) :
    IsPerfectNatPower q k ↔
      Nat.nthRoot q k ^ q = k := by
  unfold IsPerfectNatPower
  exact
    Nat.exists_pow_eq_iff'
      (Nat.ne_of_gt hq)

/--
The positive perfect `q`-th powers not exceeding `n`.-/
def perfectNatPowersUpTo
    (q n : Nat) : Finset Nat :=
  (Finset.Icc
      1
      (Nat.nthRoot q n)).image
    (fun a => a ^ q)

/--
Membership in `perfectNatPowersUpTo q n` is equivalent to
being a positive perfect `q`-th power not exceeding `n`.
@isnad1 id=iff.1h3v.s5.d536ea2910ef from=translated src=- shape=a64d8af6 vocab=b0901b57
-/
theorem mem_perfectNatPowersUpTo_iff
    (q n k : Nat)
    (hq : 0 < q) :
    k ∈ perfectNatPowersUpTo q n ↔
      k ∈ Finset.Icc 1 n ∧
        IsPerfectNatPower q k := by
  classical
  have hqNe :
      q ≠ 0 :=
    Nat.ne_of_gt hq
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with
      ⟨a, ha, rfl⟩
    have haBounds :
        1 ≤ a ∧
          a ≤ Nat.nthRoot q n :=
      Finset.mem_Icc.mp ha
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · exact
          (one_le_pow_iff hqNe).2
            haBounds.1
      · exact
          (Nat.le_nthRoot_iff hqNe).1
            haBounds.2
    · exact ⟨a, rfl⟩
  · rintro ⟨hk, ⟨a, ha⟩⟩
    subst k
    have hkBounds :
        1 ≤ a ^ q ∧
          a ^ q ≤ n :=
      Finset.mem_Icc.mp hk
    apply Finset.mem_image.mpr
    refine ⟨a, ?_, rfl⟩
    apply Finset.mem_Icc.mpr
    constructor
    · exact
        (one_le_pow_iff hqNe).1
          hkBounds.1
    · exact
        (Nat.le_nthRoot_iff hqNe).2
          hkBounds.2

/--
There are exactly `nthRoot q n` positive perfect
`q`-th powers not exceeding `n`.
@isnad1 id=eq.1h2v.s4.6ccf2dbccc96 from=translated src=- shape=b08b3c33 vocab=e6b30096
-/
theorem perfectNatPowersUpTo_card
    (q n : Nat)
    (hq : 0 < q) :
    (perfectNatPowersUpTo q n).card =
      Nat.nthRoot q n := by
  unfold perfectNatPowersUpTo
  rw [
    Finset.card_image_of_injective
      (Finset.Icc 1 (Nat.nthRoot q n))
      (pow_left_injective
        (Nat.ne_of_gt hq))
  ]
  simp [Nat.card_Icc]

/--
For a nonnegative real number, the natural ceiling equals
the natural floor exactly when the number is a natural
number.
@isnad1 id=iff.1h1v.s5.26c6f52516a9 from=translated src=- shape=d20b4f95 vocab=fd0b1efd
-/
theorem natCeil_eq_natFloor_iff_exists_natCast
    (y : ℝ)
    (hy : 0 ≤ y) :
    ⌈y⌉₊ = ⌊y⌋₊ ↔
      ∃ m : Nat, y = (m : ℝ) := by
  constructor
  · intro hEq
    refine ⟨⌊y⌋₊, ?_⟩
    apply le_antisymm
    · have hceil :
          y ≤ (⌈y⌉₊ : ℝ) :=
        Nat.le_ceil y
      simpa [hEq] using hceil
    · exact
        Nat.floor_le hy
  · rintro ⟨m, rfl⟩
    simp

/--
For a reduced rational exponent `p / q`, the ceiling and
floor of `k^(p/q)` coincide exactly at perfect `q`-th
powers.
@isnad1 id=iff.2h3v.s5.c9971acb4976 from=translated src=- shape=151a5421 vocab=466f3041
-/
theorem rationalRpow_ceil_eq_floor_iff
    (p q k : Nat)
    (hq : 0 < q)
    (hpq : Nat.Coprime p q) :
    ⌈Real.rpow
        (k : ℝ)
        (rationalExponent p q)⌉₊ =
      ⌊Real.rpow
        (k : ℝ)
        (rationalExponent p q)⌋₊ ↔
      IsPerfectNatPower q k := by
  have hyNonneg :
      0 ≤
        Real.rpow
          (k : ℝ)
          (rationalExponent p q) := by
    exact
      Real.rpow_nonneg
        (by positivity)
        (rationalExponent p q)
  rw [
    natCeil_eq_natFloor_iff_exists_natCast
      _
      hyNonneg
  ]
  exact
    rpow_rational_isNat_iff_isPerfectNatPower
      p q k hq hpq

/--
For a reduced rational exponent, the ceiling differs from
the floor by one exactly away from perfect `q`-th powers.

The perfect-power condition is expressed computationally
through `Nat.nthRoot`.
@isnad1 id=eq.2h3v.s6.31e5daf681aa from=translated src=- shape=a9f49e9c vocab=3e398a90
-/
theorem rationalRpow_ceil_eq_floor_add_indicator
    (p q k : Nat)
    (hq : 0 < q)
    (hpq : Nat.Coprime p q) :
    ⌈Real.rpow
        (k : ℝ)
        (rationalExponent p q)⌉₊ =
      ⌊Real.rpow
        (k : ℝ)
        (rationalExponent p q)⌋₊ +
        if Nat.nthRoot q k ^ q = k then 0 else 1 := by
  by_cases hroot :
      Nat.nthRoot q k ^ q = k
  · have hperfect :
        IsPerfectNatPower q k :=
      (isPerfectNatPower_iff_nthRoot_pow_eq
        q k hq).2 hroot
    have hEq :
        ⌈Real.rpow
            (k : ℝ)
            (rationalExponent p q)⌉₊ =
          ⌊Real.rpow
            (k : ℝ)
            (rationalExponent p q)⌋₊ :=
      (rationalRpow_ceil_eq_floor_iff
        p q k hq hpq).2 hperfect
    rw [ite_eq_left hroot, Nat.add_zero]
    exact hEq
  · have hnotPerfect :
        ¬ IsPerfectNatPower q k := by
      intro hperfect
      apply hroot
      exact
        (isPerfectNatPower_iff_nthRoot_pow_eq
          q k hq).1 hperfect
    have hNe :
        ⌈Real.rpow
            (k : ℝ)
            (rationalExponent p q)⌉₊ ≠
          ⌊Real.rpow
            (k : ℝ)
            (rationalExponent p q)⌋₊ := by
      intro hEq
      apply hnotPerfect
      exact
        (rationalRpow_ceil_eq_floor_iff
          p q k hq hpq).1 hEq
    have hLower :
        ⌊Real.rpow
            (k : ℝ)
            (rationalExponent p q)⌋₊ ≤
          ⌈Real.rpow
            (k : ℝ)
            (rationalExponent p q)⌉₊ :=
      Nat.floor_le_ceil _
    have hUpper :
        ⌈Real.rpow
            (k : ℝ)
            (rationalExponent p q)⌉₊ ≤
          ⌊Real.rpow
            (k : ℝ)
            (rationalExponent p q)⌋₊ + 1 :=
      Nat.ceil_le_floor_add_one _
    have hSucc :
        ⌈Real.rpow
            (k : ℝ)
            (rationalExponent p q)⌉₊ =
          ⌊Real.rpow
            (k : ℝ)
            (rationalExponent p q)⌋₊ + 1 := by
      omega
    rw [ite_eq_right hroot]
    exact hSucc

/--
The indicator of perfect `q`-th powers over `1, ..., n`
sums to `Nat.nthRoot q n`.
@isnad1 id=eq.1h2v.s6.24a98924132c from=translated src=- shape=12d9e76a vocab=5963d399
-/
theorem perfectNatPowerIndicatorSum
    (q n : Nat)
    (hq : 0 < q) :
    Finset.sum
        (Finset.Icc 1 n)
        (fun k =>
          if Nat.nthRoot q k ^ q = k
          then 1
          else 0) =
      Nat.nthRoot q n := by
  classical
  rw [Finset.sum_boole]
  have hfilter :
      (Finset.Icc 1 n).filter
          (fun k =>
            Nat.nthRoot q k ^ q = k) =
        perfectNatPowersUpTo q n := by
    ext k
    simp only [Finset.mem_filter]
    rw [
      mem_perfectNatPowersUpTo_iff
        q n k hq,
      isPerfectNatPower_iff_nthRoot_pow_eq
        q k hq
    ]
  have hcard :
      ((Finset.Icc 1 n).filter
          (fun k =>
            Nat.nthRoot q k ^ q = k)).card =
        Nat.nthRoot q n := by
    rw [hfilter]
    exact
      perfectNatPowersUpTo_card
        q n hq
  exact_mod_cast hcard

/--
Among `1, ..., n`, exactly

`n - Nat.nthRoot q n`

indices are not perfect `q`-th powers.
@isnad1 id=eq.1h2v.s6.774171a0d200 from=translated src=- shape=30c2fde3 vocab=92de6617
-/
theorem nonPerfectNatPowerIndicatorSum
    (q n : Nat)
    (hq : 0 < q) :
    Finset.sum
        (Finset.Icc 1 n)
        (fun k =>
          if Nat.nthRoot q k ^ q = k
          then 0
          else 1) =
      n - Nat.nthRoot q n := by
  classical
  have htotal :
      Finset.sum
          (Finset.Icc 1 n)
          (fun k =>
            if Nat.nthRoot q k ^ q = k
            then 0
            else 1) +
        Finset.sum
          (Finset.Icc 1 n)
          (fun k =>
            if Nat.nthRoot q k ^ q = k
            then 1
            else 0) =
        n := by
    calc
      Finset.sum
            (Finset.Icc 1 n)
            (fun k =>
              if Nat.nthRoot q k ^ q = k
              then 0
              else 1) +
          Finset.sum
            (Finset.Icc 1 n)
            (fun k =>
              if Nat.nthRoot q k ^ q = k
              then 1
              else 0) =
        Finset.sum
          (Finset.Icc 1 n)
          (fun k =>
            (if Nat.nthRoot q k ^ q = k
             then 0
             else 1) +
            (if Nat.nthRoot q k ^ q = k
             then 1
             else 0)) := by
          rw [Finset.sum_add_distrib]
      _ =
        Finset.sum
          (Finset.Icc 1 n)
          (fun _ => 1) := by
          apply Finset.sum_congr rfl
          intro k _hk
          by_cases h :
              Nat.nthRoot q k ^ q = k
          · simp [h]
          · simp [h]
      _ = n := by
          simp [Nat.card_Icc]
  have hperfect :
      Finset.sum
          (Finset.Icc 1 n)
          (fun k =>
            if Nat.nthRoot q k ^ q = k
            then 1
            else 0) =
        Nat.nthRoot q n :=
    perfectNatPowerIndicatorSum
      q n hq
  omega

/--
For a reduced rational exponent `p / q`, the ceiling sum
differs from the floor sum by the number of non-perfect
`q`-th powers in `1, ..., n`.
@isnad1 id=eq.2h3v.s5.1a8fafb942b7 from=translated src=- shape=f8f93e45 vocab=162bb45d
-/
theorem rationalCeilPowerSum_eq_floorPowerSum_add_correction
    (p q n : Nat)
    (hq : 0 < q)
    (hpq : Nat.Coprime p q) :
    rationalCeilPowerSum p q n =
      rationalFloorPowerSum p q n +
        (n - Nat.nthRoot q n) := by
  unfold
    rationalCeilPowerSum
    rationalFloorPowerSum
    realCeilPowerSum
    realFloorPowerSum
  calc
    Finset.sum
        (Finset.Icc 1 n)
        (fun k =>
          ⌈Real.rpow
              (k : ℝ)
              (rationalExponent p q)⌉₊) =
      Finset.sum
        (Finset.Icc 1 n)
        (fun k =>
          ⌊Real.rpow
              (k : ℝ)
              (rationalExponent p q)⌋₊ +
            if Nat.nthRoot q k ^ q = k
            then 0
            else 1) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact
        rationalRpow_ceil_eq_floor_add_indicator
          p q k hq hpq
    _ =
      Finset.sum
          (Finset.Icc 1 n)
          (fun k =>
            ⌊Real.rpow
                (k : ℝ)
                (rationalExponent p q)⌋₊) +
        Finset.sum
          (Finset.Icc 1 n)
          (fun k =>
            if Nat.nthRoot q k ^ q = k
            then 0
            else 1) := by
      rw [Finset.sum_add_distrib]
    _ =
      Finset.sum
          (Finset.Icc 1 n)
          (fun k =>
            ⌊Real.rpow
                (k : ℝ)
                (rationalExponent p q)⌋₊) +
        (n - Nat.nthRoot q n) := by
      rw [
        nonPerfectNatPowerIndicatorSum
          q n hq
      ]

/--
The rational reciprocity law written entirely in terms of
floor sums, with the perfect-power correction still shown
explicitly.

Here the cutoff is `floor(n^(p/q))`.
@isnad1 id=eq.3h3v.s6.1c1cdf636120 from=translated src=- shape=71124caa vocab=d9e5e244
-/
theorem rationalFloorPowerReciprocity_with_correction
    (p q n : Nat)
    (hp : 0 < p)
    (hq : 0 < q)
    (hpq : Nat.Coprime p q) :
    rationalFloorPowerSum p q n +
        rationalFloorPowerSum q p
          (realFloorPowerCutoff
            (rationalExponent p q) n) +
        (realFloorPowerCutoff
              (rationalExponent p q) n -
          Nat.nthRoot p
            (realFloorPowerCutoff
              (rationalExponent p q) n)) =
      (n + 1) *
        realFloorPowerCutoff
          (rationalExponent p q) n := by
  let r :=
    realFloorPowerCutoff
      (rationalExponent p q) n
  have hceil :
      rationalCeilPowerSum q p r =
        rationalFloorPowerSum q p r +
          (r - Nat.nthRoot p r) := by
    exact
      rationalCeilPowerSum_eq_floorPowerSum_add_correction
        q p r hp hpq.symm
  have hrec :
      rationalFloorPowerSum p q n +
          rationalCeilPowerSum q p r =
        (n + 1) * r := by
    dsimp [r]
    exact
      rationalPowerReciprocity
        p q n hp hq
  change
    rationalFloorPowerSum p q n +
        rationalFloorPowerSum q p r +
        (r - Nat.nthRoot p r) =
      (n + 1) * r
  rw [Nat.add_assoc, ← hceil]
  exact hrec

/--
The cutoff `floor(n^(p/q))` lies between the `p`-th powers
of `nthRoot q n` and its successor.
@isnad1 id=and.2h3v.s6.f9704affc8ea from=translated src=- shape=2a683016 vocab=20b62e79
-/
theorem rationalFloorPowerCutoff_root_bounds
    (p q n : Nat)
    (hp : 0 < p)
    (hq : 0 < q) :
    Nat.nthRoot q n ^ p ≤
        realFloorPowerCutoff
          (rationalExponent p q)
          n ∧
      realFloorPowerCutoff
          (rationalExponent p q)
          n <
        (Nat.nthRoot q n + 1) ^ p := by
  have hqNe :
      q ≠ 0 :=
    Nat.ne_of_gt hq
  have hExpPos :
      0 < rationalExponent p q :=
    rationalExponent_pos
      p q hp hq
  have hrootLower :
      Nat.nthRoot q n ^ q ≤ n := by
    exact
      (Nat.le_nthRoot_iff hqNe).1
        le_rfl
  have hrootUpper :
      n <
        (Nat.nthRoot q n + 1) ^ q :=
    Nat.lt_pow_nthRoot_add_one
      hqNe n
  have hrootLowerR :
      ((Nat.nthRoot q n ^ q : Nat) : ℝ) ≤
        (n : ℝ) := by
    exact_mod_cast hrootLower
  have hrootUpperR :
      (n : ℝ) <
        (((Nat.nthRoot q n + 1) ^ q : Nat) : ℝ) := by
    exact_mod_cast hrootUpper
  have hmonoLower :
      Real.rpow
          ((Nat.nthRoot q n ^ q : Nat) : ℝ)
          (rationalExponent p q) ≤
        Real.rpow
          (n : ℝ)
          (rationalExponent p q) := by
    exact
      Real.rpow_le_rpow
        (by positivity)
        hrootLowerR
        (le_of_lt hExpPos)
  have hlowerReal :
      ((Nat.nthRoot q n ^ p : Nat) : ℝ) ≤
        Real.rpow
          (n : ℝ)
          (rationalExponent p q) := by
    calc
      ((Nat.nthRoot q n ^ p : Nat) : ℝ) =
          Real.rpow
            ((Nat.nthRoot q n ^ q : Nat) : ℝ)
            (rationalExponent p q) := by
        symm
        exact
          rpow_rational_of_nat_pow
            p q
            (Nat.nthRoot q n)
            hq
      _ ≤
          Real.rpow
            (n : ℝ)
            (rationalExponent p q) :=
        hmonoLower
  have hmonoUpper :
      Real.rpow
          (n : ℝ)
          (rationalExponent p q) <
        Real.rpow
          (((Nat.nthRoot q n + 1) ^ q : Nat) : ℝ)
          (rationalExponent p q) := by
    exact
      Real.rpow_lt_rpow
        (by positivity)
        hrootUpperR
        hExpPos
  have hupperReal :
      Real.rpow
          (n : ℝ)
          (rationalExponent p q) <
        (((Nat.nthRoot q n + 1) ^ p : Nat) : ℝ) := by
    calc
      Real.rpow
          (n : ℝ)
          (rationalExponent p q) <
        Real.rpow
          (((Nat.nthRoot q n + 1) ^ q : Nat) : ℝ)
          (rationalExponent p q) :=
        hmonoUpper
      _ =
        (((Nat.nthRoot q n + 1) ^ p : Nat) : ℝ) := by
        exact
          rpow_rational_of_nat_pow
            p q
            (Nat.nthRoot q n + 1)
            hq
  constructor
  · unfold realFloorPowerCutoff
    exact
      Nat.le_floor
        hlowerReal
  · have hyNonneg :
        0 ≤
          Real.rpow
            (n : ℝ)
            (rationalExponent p q) := by
      exact
        Real.rpow_nonneg
          (by positivity)
          (rationalExponent p q)
    unfold realFloorPowerCutoff
    exact
      (Nat.floor_lt hyNonneg).2
        hupperReal

/--
Taking the numerical `p`-th root of `floor(n^(p/q))`
recovers the numerical `q`-th root of `n`.
@isnad1 id=eq.2h3v.s5.f39de1b294c0 from=translated src=- shape=e8de8457 vocab=3aba319e
-/
theorem nthRoot_rationalFloorPowerCutoff
    (p q n : Nat)
    (hp : 0 < p)
    (hq : 0 < q) :
    Nat.nthRoot p
        (realFloorPowerCutoff
          (rationalExponent p q)
          n) =
      Nat.nthRoot q n := by
  rcases
      rationalFloorPowerCutoff_root_bounds
        p q n hp hq with
    ⟨hlower, hupper⟩
  exact
    Nat.nthRoot_eq_of_le_of_lt
      hlower
      hupper

/--
Exact floor-floor reciprocity for a reduced positive
rational exponent.

If

`r = floor(n^(p/q))`,

then

`F_(p/q)(n) + F_(q/p)(r)
   = n * r + nthRoot q n`.
@isnad1 id=eq.3h3v.s6.f00e4b2ad325 from=translated src=- shape=9ec8a8f4 vocab=ec6d8404
-/
theorem rationalFloorPowerReciprocity
    (p q n : Nat)
    (hp : 0 < p)
    (hq : 0 < q)
    (hpq : Nat.Coprime p q) :
    rationalFloorPowerSum p q n +
        rationalFloorPowerSum q p
          (realFloorPowerCutoff
            (rationalExponent p q)
            n) =
      n *
          realFloorPowerCutoff
            (rationalExponent p q)
            n +
        Nat.nthRoot q n := by
  let r :=
    realFloorPowerCutoff
      (rationalExponent p q)
      n
  let a :=
    Nat.nthRoot q n
  have hroot :
      Nat.nthRoot p r = a := by
    dsimp [r, a]
    exact
      nthRoot_rationalFloorPowerCutoff
        p q n hp hq
  have hapowLe :
      a ^ p ≤ r := by
    dsimp [a, r]
    exact
      (rationalFloorPowerCutoff_root_bounds
        p q n hp hq).1
  have haLePow :
      a ≤ a ^ p := by
    exact
      Nat.le_self_pow
        (Nat.ne_of_gt hp)
        a
  have haLeR :
      a ≤ r :=
    haLePow.trans hapowLe
  have hrSplit :
      a + (r - a) = r := by
    omega
  have hrec :
      rationalFloorPowerSum p q n +
          rationalFloorPowerSum q p r +
          (r - Nat.nthRoot p r) =
        (n + 1) * r := by
    dsimp [r]
    exact
      rationalFloorPowerReciprocity_with_correction
        p q n hp hq hpq
  rw [hroot] at hrec
  change
    rationalFloorPowerSum p q n +
        rationalFloorPowerSum q p r =
      n * r + a
  have hright :
      (n + 1) * r =
        (n * r + a) + (r - a) := by
    calc
      (n + 1) * r =
          n * r + r := by
        rw [Nat.add_mul]
        simp
      _ =
          n * r + (a + (r - a)) := by
        rw [hrSplit]
      _ =
          (n * r + a) + (r - a) := by
        ac_rfl
  have hcancel :
      (rationalFloorPowerSum p q n +
          rationalFloorPowerSum q p r) +
          (r - a) =
        (n * r + a) +
          (r - a) := by
    calc
      (rationalFloorPowerSum p q n +
          rationalFloorPowerSum q p r) +
          (r - a) =
        (n + 1) * r :=
          hrec
      _ =
        (n * r + a) +
          (r - a) :=
          hright
  exact
    Nat.add_right_cancel hcancel

/--
Main floor-floor reciprocity theorem for a reduced positive
rational exponent.

For

`r = floor(n^(p/q))`,

we have

`F_(p/q)(n) + F_(q/p)(r)
   = n * r + nthRoot q n`.
@isnad1 id=eq.3h3v.s6.dd8d9fb2223d from=translated src=- shape=a96d3d54 vocab=3feca048
-/
theorem rationalExponentReciprocityMainTheorem
    (p q n : Nat)
    (hp : 0 < p)
    (hq : 0 < q)
    (hpq : Nat.Coprime p q) :
    realFloorPowerSum
        (rationalExponent p q)
        n +
      realFloorPowerSum
        (rationalExponent q p)
        (realFloorPowerCutoff
          (rationalExponent p q)
          n) =
      n *
          realFloorPowerCutoff
            (rationalExponent p q)
            n +
        Nat.nthRoot q n := by
  simpa [
    rationalFloorPowerSum
  ] using
    rationalFloorPowerReciprocity
      p q n hp hq hpq

/--
Article-form floor-floor reciprocity for a reduced positive
rational exponent.

Writing

`r = floor(n^(p/q))`,

the correction term is written as the `p`-th root of `r`,
exactly as in the article.
@isnad1 id=eq.3h3v.s6.a50978c31d2d from=translated src=- shape=b2b3d264 vocab=ec6d8404
-/
theorem rationalFloorPowerReciprocity_articleForm
    (p q n : Nat)
    (hp : 0 < p)
    (hq : 0 < q)
    (hpq : Nat.Coprime p q) :
    rationalFloorPowerSum p q n +
        rationalFloorPowerSum q p
          (realFloorPowerCutoff
            (rationalExponent p q)
            n) =
      n *
          realFloorPowerCutoff
            (rationalExponent p q)
            n +
        Nat.nthRoot p
          (realFloorPowerCutoff
            (rationalExponent p q)
            n) := by
  calc
    rationalFloorPowerSum p q n +
        rationalFloorPowerSum q p
          (realFloorPowerCutoff
            (rationalExponent p q)
            n) =
      n *
          realFloorPowerCutoff
            (rationalExponent p q)
            n +
        Nat.nthRoot q n :=
      rationalFloorPowerReciprocity
        p q n hp hq hpq
    _ =
      n *
          realFloorPowerCutoff
            (rationalExponent p q)
            n +
        Nat.nthRoot p
          (realFloorPowerCutoff
            (rationalExponent p q)
            n) := by
      rw [
        nthRoot_rationalFloorPowerCutoff
          p q n hp hq
      ]

/--
The article-form reciprocity theorem expanded to the
underlying real floor-power sums.
@isnad1 id=eq.3h3v.s6.87e9348cc026 from=translated src=- shape=b8b7d26a vocab=3feca048
-/
theorem rationalExponentReciprocityArticleTheorem
    (p q n : Nat)
    (hp : 0 < p)
    (hq : 0 < q)
    (hpq : Nat.Coprime p q) :
    realFloorPowerSum
        (rationalExponent p q)
        n +
      realFloorPowerSum
        (rationalExponent q p)
        (realFloorPowerCutoff
          (rationalExponent p q)
          n) =
      n *
          realFloorPowerCutoff
            (rationalExponent p q)
            n +
        Nat.nthRoot p
          (realFloorPowerCutoff
            (rationalExponent p q)
            n) := by
  simpa [
    rationalFloorPowerSum
  ] using
    rationalFloorPowerReciprocity_articleForm
      p q n hp hq hpq

end RoundedRootSums
