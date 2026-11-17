/-
The dyadic depth behind primitive H4 level reciprocity.

The parity theorem in `LevelReciprocity` is the first layer of a more
general cyclic-group fact: if an element has exact order `m`, with
`4 ∣ m`, inside a cyclic group of order `m * h`, then for every positive
`d ∣ m` the availability of a `d`-th root of its negative is controlled
exactly by `d ∣ h`.

This module develops the abstract power-map criterion and then exposes
the full residual depth, including the quartic layer, for prime fields.
It does not prove H4.
-/
import Tengoku.AgrawalR5.AgrawalCore.LevelReciprocity
import Tengoku.Seed.Algebra.Group.Subgroup.Finite
import Tengoku.Seed.GroupTheory.SpecificGroups.Cyclic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-- In a finite cyclic commutative group, when `d` divides the group
order, an element is a `d`-th power exactly when its
`(cardinality / d)`-th power is one.-/
theorem mem_powMonoidHom_range_iff_pow_card_div_eq_one
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    {d : ℕ} (hd : d ∣ Nat.card G) (x : G) :
    x ∈ (powMonoidHom d : G →* G).range ↔
      x ^ (Nat.card G / d) = 1 := by
  let H : Subgroup G := (powMonoidHom d : G →* G).range
  let K : Subgroup G := (powMonoidHom (Nat.card G / d) : G →* G).ker
  have hHK : H ≤ K := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    simp only [powMonoidHom_apply]
    rw [← pow_mul, Nat.mul_div_cancel' hd]
    exact pow_card_eq_one'
  have hcardH : Nat.card H = Nat.card G / d := by
    dsimp [H]
    rw [IsCyclic.card_powMonoidHom_range,
      Nat.gcd_eq_right_iff_dvd.mpr hd]
  have hquotdvd : Nat.card G / d ∣ Nat.card G := by
    refine ⟨d, ?_⟩
    rw [mul_comm, Nat.mul_div_cancel' hd]
  have hcardK : Nat.card K = Nat.card G / d := by
    dsimp [K]
    rw [IsCyclic.card_powMonoidHom_ker,
      Nat.gcd_eq_right_iff_dvd.mpr hquotdvd]
  have hEq : H = K :=
    Subgroup.eq_of_le_of_card_ge hHK (by rw [hcardH, hcardK])
  change x ∈ H ↔ _
  rw [hEq]
  rfl

private theorem shift_exponent_coprime_of_four_dvd {m : ℕ}
    (hm4 : 4 ∣ m) :
    Nat.Coprime m (m / 2 + 1) := by
  obtain ⟨q, rfl⟩ := hm4
  have hqcop : Nat.Coprime q (2 * q + 1) := by
    have hbase : Nat.Coprime (1 + q * 2) q :=
      (Nat.coprime_add_mul_left_left 1 q 2).mpr (by simp)
    rw [show 2 * q + 1 = 1 + q * 2 by ring]
    exact hbase.symm
  have h4cop : Nat.Coprime 4 (2 * q + 1) := by
    have h2cop : Nat.Coprime 2 (2 * q + 1) := by
      rw [Nat.coprime_two_left]
      exact ⟨q, by omega⟩
    simpa using h2cop.pow_left 2
  simpa only [show 4 * q / 2 + 1 = 2 * q + 1 by omega] using
    h4cop.mul_left hqcop

private theorem primitive_level_div_iff {d m h : ℕ}
    (hdpos : 0 < d) (hmpos : 0 < m) (hdm : d ∣ m) :
    m ∣ m * h / d ↔ d ∣ h := by
  obtain ⟨q, rfl⟩ := hdm
  have hqpos : 0 < q := by
    by_contra hq
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
    subst q
    simp at hmpos
  have hdiv :
      d * q * h / d = q * h := by
    rw [show d * q * h = d * (q * h) by ring,
      Nat.mul_div_cancel_left (q * h) hdpos]
  rw [hdiv, show d * q = q * d by ring]
  exact Nat.mul_dvd_mul_iff_left hqpos

/-- **Power depth in a finite cyclic group.**

Let `x` have exact order `m`, with `4 ∣ m`, in a cyclic group of
cardinality `m*h`.  For every positive `d ∣ m`, the shifted generator
`x^(m/2+1)` is a `d`-th power in the ambient group exactly when
`d ∣ h`.

Over a prime field the shifted generator is `-x`, because
`x^(m/2) = -1`.-/
theorem shifted_generator_isPower_iff
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    {x : G} {d m h : ℕ}
    (hdpos : 0 < d) (hdm : d ∣ m)
    (hm4 : 4 ∣ m) (hord : orderOf x = m)
    (hcard : Nat.card G = m * h) :
    (∃ y : G, y ^ d = x ^ (m / 2 + 1)) ↔ d ∣ h := by
  have hmpos : 0 < m := by
    rw [← hord]
    exact orderOf_pos x
  have hcop : Nat.Coprime m (m / 2 + 1) :=
    shift_exponent_coprime_of_four_dvd hm4
  have hzord : orderOf (x ^ (m / 2 + 1)) = m := by
    rw [orderOf_pow, hord, hcop.gcd_eq_one, Nat.div_one]
  have hdcard : d ∣ Nat.card G := by
    rw [hcard]
    exact dvd_mul_of_dvd_left hdm h
  change
    x ^ (m / 2 + 1) ∈ (powMonoidHom d : G →* G).range ↔ d ∣ h
  rw [mem_powMonoidHom_range_iff_pow_card_div_eq_one hdcard]
  rw [← orderOf_dvd_iff_pow_eq_one, hzord, hcard]
  exact primitive_level_div_iff hdpos hmpos hdm

/-- Quartic specialization of `shifted_generator_isPower_iff`.-/
theorem shifted_generator_isFourthPower_iff
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    {x : G} {m h : ℕ}
    (hm4 : 4 ∣ m) (hord : orderOf x = m)
    (hcard : Nat.card G = m * h) :
    (∃ y : G, y ^ 4 = x ^ (m / 2 + 1)) ↔ 4 ∣ h :=
  shifted_generator_isPower_iff (by norm_num) hm4 hm4 hord hcard

variable {p : ℕ} [Fact p.Prime]

private theorem five_ne_zero_mod_prime_depth (hp5 : p ≠ 5) :
    (5 : ZMod p) ≠ 0 := by
  intro hzero
  have hp : p ∣ 5 :=
    (CharP.cast_eq_zero_iff (ZMod p) p 5).mp hzero
  exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hp)

private theorem pow_half_exact_order_eq_neg_one
    {x : ZMod p} {m : ℕ}
    (hx0 : x ≠ 0) (hm4 : 4 ∣ m) (hord : orderOf x = m) :
    x ^ (m / 2) = -1 := by
  have hmpos : 0 < m := by
    let xu : (ZMod p)ˣ := Units.mk0 x hx0
    have hordU : orderOf xu = m := by
      rw [← hord, ← orderOf_units]
      rfl
    rw [← hordU]
    exact orderOf_pos xu
  have hmEven : Even m :=
    even_iff_two_dvd.mpr (dvd_trans (by norm_num : 2 ∣ 4) hm4)
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

/-- **Residual power-depth theorem over a prime field.**

If `x` has exact order `m`, `4 ∣ m`, and `p-1=m*h`, then for every
positive divisor `d` of `m`, `-x` is a `d`-th power in `F_pˣ`
exactly when `d ∣ h`.-/
theorem neg_isPower_iff_residual_multiplier_dvd
    {x : ZMod p} {d m h : ℕ}
    (hx0 : x ≠ 0) (hdpos : 0 < d) (hdm : d ∣ m) (hm4 : 4 ∣ m)
    (hord : orderOf x = m) (hfactor : p - 1 = m * h) :
    (∃ y : ZMod p, y ^ d = -x) ↔ d ∣ h := by
  let xu : (ZMod p)ˣ := Units.mk0 x hx0
  have hordU : orderOf xu = m := by
    rw [← hord, ← orderOf_units]
    rfl
  have hcardU : Nat.card (ZMod p)ˣ = m * h := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units p, hfactor]
  have hxhalf : x ^ (m / 2) = -1 :=
    pow_half_exact_order_eq_neg_one hx0 hm4 hord
  have hshiftU : xu ^ (m / 2 + 1) = -xu := by
    apply Units.ext
    change x ^ (m / 2 + 1) = -x
    rw [pow_add, pow_one, hxhalf, neg_one_mul]
  have habstract :
      (∃ y : (ZMod p)ˣ, y ^ d = xu ^ (m / 2 + 1)) ↔ d ∣ h :=
    shifted_generator_isPower_iff hdpos hdm hm4 hordU hcardU
  rw [hshiftU] at habstract
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      intro hyzero
      rw [hyzero, zero_pow hdpos.ne'] at hy
      exact hx0 (neg_eq_zero.mp hy.symm)
    let yu : (ZMod p)ˣ := Units.mk0 y hy0
    apply habstract.mp
    refine ⟨yu, Units.ext ?_⟩
    simpa [yu, xu] using hy
  · intro hh
    obtain ⟨yu, hyu⟩ := habstract.mpr hh
    refine ⟨(yu : ZMod p), ?_⟩
    simpa [xu] using congrArg Units.val hyu

/-- Quartic specialization of the residual power-depth theorem.-/
theorem neg_isFourthPower_iff_residual_multiplier_four_dvd
    {x : ZMod p} {m h : ℕ}
    (hx0 : x ≠ 0) (hm4 : 4 ∣ m)
    (hord : orderOf x = m) (hfactor : p - 1 = m * h) :
    (∃ y : ZMod p, y ^ 4 = -x) ↔ 4 ∣ h :=
  neg_isPower_iff_residual_multiplier_dvd
    hx0 (by norm_num) hm4 hm4 hord hfactor

/-- **Direct four-coefficient power-depth theorem.**

For a good split divisor of the canonical primitive integer and every
positive `d ∣ 4rs`, `-γ` is a `d`-th power exactly when the residual
multiplier is divisible by `d`.-/
theorem dvd_D_neg_gamma_isPower_iff_dvd
    (hp5 : p ≠ 5) (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    {d : ℕ} (hdpos : 0 < d) (hdlevel : d ∣ 4 * r * s)
    {h : ℕ} (hfactor : p - 1 = (4 * r * s) * h) :
    (∃ y : ZMod p, y ^ d = -γ) ↔ d ∣ h := by
  have hγ0 : γ ≠ 0 := by
    intro hz
    rw [hz] at hγ
    norm_num at hγ
    exact five_ne_zero_mod_prime_depth hp5 hγ
  have hord :
      orderOf γ = 4 * r * s :=
    (dvd_primitiveFourCoefficientD_exact_order_profile
      hp5 hr hs hkpos hpm hsig γ hγ hD).1
  exact neg_isPower_iff_residual_multiplier_dvd
    hγ0 hdpos hdlevel (by simp [mul_assoc]) hord hfactor

/-- Quartic specialization of the direct four-coefficient theorem.-/
theorem dvd_D_neg_gamma_isFourthPower_iff_four_dvd
    (hp5 : p ≠ 5) (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    {h : ℕ} (hfactor : p - 1 = (4 * r * s) * h) :
    (∃ y : ZMod p, y ^ 4 = -γ) ↔ 4 ∣ h :=
  dvd_D_neg_gamma_isPower_iff_dvd
    hp5 hr hs hkpos hpm hsig γ hγ hD
      (by norm_num) (by simp [mul_assoc]) hfactor

/-- In the good H4 range, every even power depth also carries the
quintic divisibility forced by level reciprocity.-/
theorem dvd_D_neg_gamma_isPower_iff_lcm_five_dvd
    (hp5 : p ≠ 5) (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s) (h5level : ¬5 ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    {d : ℕ} (hdpos : 0 < d) (hdlevel : d ∣ 4 * r * s)
    (hdeven : 2 ∣ d)
    {h : ℕ} (hfactor : p - 1 = (4 * r * s) * h) :
    (∃ y : ZMod p, y ^ d = -γ) ↔ Nat.lcm d 5 ∣ h := by
  have hpower :
      (∃ y : ZMod p, y ^ d = -γ) ↔ d ∣ h :=
    dvd_D_neg_gamma_isPower_iff_dvd
      hp5 hr hs hkpos hpm hsig γ hγ hD hdpos hdlevel hfactor
  have hevenFive :
      Even h ↔ 5 ∣ h :=
    dvd_D_residual_multiplier_even_iff_five_dvd
      hp5 hr hs hkpos hpm h5level hsig γ hγ hD hfactor
  constructor
  · intro hpow
    have hd : d ∣ h := hpower.mp hpow
    have h2 : 2 ∣ h := dvd_trans hdeven hd
    have h5 : 5 ∣ h :=
      hevenFive.mp (even_iff_two_dvd.mpr h2)
    exact Nat.lcm_dvd hd h5
  · intro hlcm
    apply hpower.mpr
    exact dvd_trans (Nat.dvd_lcm_left d 5) hlcm

/-- In the good H4 range, the fourth-power condition absorbs both the
quartic and quintic divisibility of the residual multiplier:
`-γ` is a fourth power exactly when `20 ∣ h`.-/
theorem dvd_D_neg_gamma_isFourthPower_iff_twenty_dvd
    (hp5 : p ≠ 5) (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s) (h5level : ¬5 ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    {h : ℕ} (hfactor : p - 1 = (4 * r * s) * h) :
    (∃ y : ZMod p, y ^ 4 = -γ) ↔ 20 ∣ h := by
  have hmain :=
    dvd_D_neg_gamma_isPower_iff_lcm_five_dvd
      hp5 hr hs hkpos hpm h5level hsig γ hγ hD
      (d := 4) (by norm_num) (by simp [mul_assoc]) (by norm_num) hfactor
  norm_num at hmain ⊢
  exact hmain

end AgrawalCore
