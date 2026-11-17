/-
The norm-visible odd jaw inside the quartic order modulus.

For an inert prime `p`, the norm exponent

  S = 1 + p + p^2 + p^3

sends the canonical unit `zeta_5 - 1` to the scalar five.  Consequently
the order of the scalar five divides the cyclotomic order.  Its odd part
therefore embeds canonically into the odd tail of the quartic row.
-/
import Tengoku.AgrawalR5.AgrawalCore.OddTailTriangle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/-- The finite-field norm exponent from the quartic extension to the base
field.-/
def quarticNormExponent (p : ℕ) : ℕ :=
  1 + p + p ^ 2 + p ^ 3

/-- **Literal norm identity.**

For an inert residue, the four Frobenius conjugates of `zeta_5 - 1` are
exactly the four nontrivial cyclotomic units, whose product is five.
@isnad1 id=eq.2h1v.s8.e3eff022a8dc from=translated src=- shape=88fbecf7 vocab=52236a5b
-/
theorem localCyclotomicUnit_pow_normExponent_eq_five
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5) :
    (localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ)) ^
        quarticNormExponent p =
      localFiveUnit hp5 := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, localCyclotomicUnit_val,
    zmodFiveUnitOne_val, pow_one, localFiveUnit_val]
  change ((zeta5 : Phi5Ring p) - 1) ^
      (1 + p + p ^ 2 + p ^ 3) = 5
  rw [show
    ((zeta5 : Phi5Ring p) - 1) ^ (1 + p + p ^ 2 + p ^ 3) =
      (((zeta5 - 1) ^ 1 * (zeta5 - 1) ^ p) *
        (zeta5 - 1) ^ (p ^ 2)) * (zeta5 - 1) ^ (p ^ 3) by
      simp only [pow_add]]
  rw [pow_one]
  have hpow (j : ℕ) :
      ((zeta5 : Phi5Ring p) - 1) ^ (p ^ j) =
        zeta5 ^ (p ^ j) - 1 :=
    localS5_frobenius_power (p := p) j
  have hpowOne :
      ((zeta5 : Phi5Ring p) - 1) ^ p = zeta5 ^ p - 1 := by
    simpa using hpow 1
  rw [hpowOne, hpow 2, hpow 3]
  rw [zeta5_pow_mod p, zeta5_pow_mod (p ^ 2),
    zeta5_pow_mod (p ^ 3)]
  rcases hp with hp2 | hp3
  · have hpSq : (p ^ 2) % 5 = 4 := by
      simp [Nat.pow_mod, hp2]
    have hpCube : (p ^ 3) % 5 = 3 := by
      simp [Nat.pow_mod, hp2]
    rw [hp2, hpSq, hpCube]
    have hprod :=
      prod_pow_sub_one (R := Phi5Ring p) (ζ := zeta5)
        (zeta5_rel (p := p))
    linear_combination hprod
  · have hpSq : (p ^ 2) % 5 = 4 := by
      simp [Nat.pow_mod, hp3]
    have hpCube : (p ^ 3) % 5 = 2 := by
      simp [Nat.pow_mod, hp3]
    rw [hp3, hpSq, hpCube]
    have hprod :=
      prod_pow_sub_one (R := Phi5Ring p) (ζ := zeta5)
        (zeta5_rel (p := p))
    linear_combination hprod

/-- The order of the scalar-five unit in the quartic ring already divides
the base-field order `p - 1`.
@isnad1 id=dvd.1h1v.s6.d325f4a07ba8 from=translated src=- shape=cb908ba5 vocab=0caa8cbd
-/
theorem orderOf_localFiveUnit_dvd_sub_one (hp5 : p ≠ 5) :
    orderOf (localFiveUnit hp5) ∣ p - 1 := by
  apply orderOf_dvd_of_pow_eq_one
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, localFiveUnit_val, Units.val_one]
  have hbase :
      (5 : ZMod p) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one (five_ne_zero hp5)
  have hmap := congrArg (algebraMap (ZMod p) (Phi5Ring p)) hbase
  simpa only [map_pow, map_ofNat, map_one] using hmap

/-- The norm identity makes the scalar-five order a divisor of the
cyclotomic order.
@isnad1 id=dvd.2h1v.s8.eccc9ddd58d1 from=translated src=- shape=f73f82fc vocab=867ead00
-/
theorem orderOf_localFiveUnit_dvd_cyclotomic
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5) :
    orderOf (localFiveUnit hp5) ∣
      orderOf (localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ)) := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← localCyclotomicUnit_pow_normExponent_eq_five hp hp5]
  let u := localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ)
  calc
    (u ^ quarticNormExponent p) ^ orderOf u =
        u ^ (quarticNormExponent p * orderOf u) := by rw [pow_mul]
    _ = u ^ (orderOf u * quarticNormExponent p) := by rw [mul_comm]
    _ = (u ^ orderOf u) ^ quarticNormExponent p := by rw [pow_mul]
    _ = 1 := by rw [pow_orderOf_eq_one, one_pow]

/-- The complementary factor in the norm-order identity.  It is the
portion of the cyclotomic order living in the norm kernel.-/
noncomputable def quarticNormKernelFactor (p : ℕ) [Fact p.Prime]
    (hp5 : p ≠ 5) : ℕ :=
  Nat.gcd
    (orderOf (localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ)))
    (quarticNormExponent p)

/-- The norm-visible odd jaw: remove the complete two-primary part from
the scalar-five order.  The prime `5` does not occur for inert `p`, so no
second stripping is needed.-/
noncomputable def quarticMinusJaw (p : ℕ) [Fact p.Prime]
    (hp5 : p ≠ 5) : ℕ :=
  ordCompl[2] (orderOf (localFiveUnit hp5))

/-- The norm-visible jaw lies on the `p - 1` side.
@isnad1 id=dvd.1h1v.s5.981ad6480a1a from=translated src=- shape=7c006d55 vocab=50bacc4e
-/
theorem quarticMinusJaw_dvd_sub_one (hp5 : p ≠ 5) :
    quarticMinusJaw p hp5 ∣ p - 1 := by
  exact (Nat.ordCompl_dvd _ 2).trans
    (orderOf_localFiveUnit_dvd_sub_one hp5)

/-- An inert prime is never `1 mod 5`; hence five does not divide its
base-field group order.
@isnad1 id=not.1h1v.s6.bc0e61a6d8ed from=translated src=- shape=ecec3336 vocab=094df8da
-/
theorem five_not_dvd_sub_one_of_inert {p : ℕ}
    (hp : p % 5 = 2 ∨ p % 5 = 3) :
    ¬ 5 ∣ p - 1 := by
  intro hdvd
  obtain ⟨k, hk⟩ := hdvd
  rcases hp with hp2 | hp3
  · omega
  · omega

/-- The scalar-five order is nonzero.
@isnad1 id=ne.1h1v.s6.273b0c2bbd81 from=translated src=- shape=577f0a4e vocab=ac0a10f8
-/
theorem orderOf_localFiveUnit_ne_zero (hp5 : p ≠ 5) :
    orderOf (localFiveUnit hp5) ≠ 0 := by
  intro hzero
  have hdvd := orderOf_localFiveUnit_dvd_sub_one hp5
  rw [hzero] at hdvd
  have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
  exact (by omega : p - 1 ≠ 0) (Nat.eq_zero_of_zero_dvd hdvd)

/-- The norm-visible jaw embeds canonically into the canonical odd tail
of the quartic row.
@isnad1 id=dvd.2h1v.s6.5557804d379d from=translated src=- shape=8c603848 vocab=0b2267fc
-/
theorem quarticMinusJaw_dvd_oddTail
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5) :
    quarticMinusJaw p hp5 ∣ quarticOddTail p hp5 := by
  have hjawOrder :
      quarticMinusJaw p hp5 ∣ orderOf (localFiveUnit hp5) :=
    Nat.ordCompl_dvd _ 2
  have hjawT :
      quarticMinusJaw p hp5 ∣ quarticOrderModulus p hp5 :=
    hjawOrder.trans <| (orderOf_localFiveUnit_dvd_cyclotomic hp hp5).trans <|
      Nat.dvd_lcm_left _ _
  have htwo :
      ¬ 2 ∣ quarticMinusJaw p hp5 :=
    Nat.not_dvd_ordCompl Nat.prime_two
      (orderOf_localFiveUnit_ne_zero hp5)
  have hfiveSub : ¬ 5 ∣ p - 1 :=
    five_not_dvd_sub_one_of_inert hp
  have hfive :
      ¬ 5 ∣ quarticMinusJaw p hp5 := by
    intro hdvd
    exact hfiveSub <| hdvd.trans (quarticMinusJaw_dvd_sub_one hp5)
  have hstripTwo :
      quarticMinusJaw p hp5 ∣
        ordCompl[2] (quarticOrderModulus p hp5) :=
    Nat.dvd_ordCompl_of_dvd_not_dvd hjawT htwo
  exact Nat.dvd_ordCompl_of_dvd_not_dvd hstripTwo hfive

/-- **Exact norm-visible jaw.**

The odd scalar-five order is not merely contained in the `p - 1` side of
the canonical tail: it is the whole intersection with that side.

The key arithmetic point is that every divisor of `p - 1` which is prime
to `2` is prime to

`S = 1 + p + p² + p³ = (p + 1)(p² + 1)`.

Therefore the norm exponent cannot kill any of its odd `p - 1`
components.
@isnad1 id=eq.2h1v.s6.bef90f425fa0 from=translated src=- shape=4fa484d3 vocab=e4f4d341
-/
theorem quarticMinusJaw_eq_gcd_oddTail_sub_one
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5) :
    quarticMinusJaw p hp5 =
      Nat.gcd (quarticOddTail p hp5) (p - 1) := by
  let u := localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ)
  let T := orderOf u
  let S := quarticNormExponent p
  let A := Nat.gcd (quarticOddTail p hp5) (p - 1)
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (quarticMinusJaw_dvd_oddTail hp hp5)
      (quarticMinusJaw_dvd_sub_one hp5)
  · have hAD : A ∣ quarticOddTail p hp5 :=
      Nat.gcd_dvd_left _ _
    have hAm : A ∣ p - 1 :=
      Nat.gcd_dvd_right _ _
    have hDcop10 :
        Nat.Coprime (quarticOddTail p hp5) 10 :=
      quarticOddTail_coprime_ten hp hp5
    have hDcop2 :
        Nat.Coprime (quarticOddTail p hp5) 2 :=
      Nat.Coprime.of_dvd_right (by norm_num : 2 ∣ 10) hDcop10
    have hDcop5 :
        Nat.Coprime (quarticOddTail p hp5) 5 :=
      Nat.Coprime.of_dvd_right (by norm_num : 5 ∣ 10) hDcop10
    have hA2 : Nat.Coprime A 2 :=
      Nat.Coprime.of_dvd_left hAD hDcop2
    have hA5 : Nat.Coprime A 5 :=
      Nat.Coprime.of_dvd_left hAD hDcop5
    have hAT : A ∣ T := by
      have hAlcm :
          A ∣ Nat.lcm T 5 := by
        simpa [T, quarticOrderModulus] using
          hAD.trans (quarticOddTail_dvd_modulus hp5)
      have hAmul : A ∣ T * 5 :=
        hAlcm.trans (Nat.lcm_dvd_mul T 5)
      exact hA5.dvd_mul_right.mp hAmul
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    have hAplus : Nat.Coprime A (p + 1) := by
      have heq : p + 1 = 2 + (p - 1) := by omega
      rw [heq, Nat.coprime_add_iff_left hAm]
      exact hA2
    have hAsqPlus : Nat.Coprime A (p ^ 2 + 1) := by
      have hAprod : A ∣ (p - 1) * (p + 1) :=
        hAm.mul_right _
      have heq : p ^ 2 + 1 = 2 + (p - 1) * (p + 1) := by
        have hpred : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
        nlinarith
      rw [heq, Nat.coprime_add_iff_left hAprod]
      exact hA2
    have hAS : Nat.Coprime A S := by
      have hSeq : S = (p + 1) * (p ^ 2 + 1) := by
        simp only [S, quarticNormExponent]
        ring
      rw [hSeq]
      exact hAplus.mul_right hAsqPlus
    have hS0 : S ≠ 0 := by
      simp only [S, quarticNormExponent]
      omega
    have hnorm : u ^ S = localFiveUnit hp5 := by
      simpa [u, S] using
        localCyclotomicUnit_pow_normExponent_eq_five hp hp5
    have horder :
        orderOf (localFiveUnit hp5) =
          T / Nat.gcd T S := by
      rw [← hnorm]
      exact orderOf_pow' u hS0
    have hAgcd : Nat.Coprime A (Nat.gcd T S) :=
      Nat.Coprime.of_dvd_right (Nat.gcd_dvd_right T S) hAS
    have hAquot : A ∣ T / Nat.gcd T S := by
      apply hAgcd.dvd_mul_right.mp
      rw [Nat.div_mul_cancel (Nat.gcd_dvd_left T S)]
      exact hAT
    have hAorder : A ∣ orderOf (localFiveUnit hp5) := by
      rw [horder]
      exact hAquot
    have htwo : ¬ 2 ∣ A := by
      intro hdvd
      have hgcd : 2 ∣ Nat.gcd A 2 :=
        Nat.dvd_gcd hdvd (dvd_refl 2)
      rw [hA2.gcd_eq_one] at hgcd
      norm_num at hgcd
    exact Nat.dvd_ordCompl_of_dvd_not_dvd hAorder htwo

/-- The visible portion of the canonical tail on the `p + 1` side.

This definition is deliberately conservative: it records only the part
whose divisibility by `p + 1` is unconditional.-/
noncomputable def quarticPlusShadow (p : ℕ) [Fact p.Prime]
    (hp5 : p ≠ 5) : ℕ :=
  Nat.gcd (quarticOddTail p hp5) (p + 1)

/--
@isnad1 id=dvd.1h1v.s4.c294fb36f4ec from=translated src=- shape=c2faa8c9 vocab=66a47f94
-/
theorem quarticPlusShadow_dvd_oddTail (hp5 : p ≠ 5) :
    quarticPlusShadow p hp5 ∣ quarticOddTail p hp5 :=
  Nat.gcd_dvd_left _ _

/--
@isnad1 id=dvd.1h1v.s5.53209bbb1309 from=translated src=- shape=7c006d55 vocab=fc6a2a2e
-/
theorem quarticPlusShadow_dvd_add_one (hp5 : p ≠ 5) :
    quarticPlusShadow p hp5 ∣ p + 1 :=
  Nat.gcd_dvd_right _ _

/-- **Exact two-jaw factorization of the canonical odd tail.**

For an inert prime, the whole canonical odd tail splits into its two
coprime field sides:

`D_p = D_{p,-} D_{p,+}`,

where `D_{p,-}` is the odd order of scalar five and divides `p - 1`,
while `D_{p,+}` divides `p + 1`.

The proof uses only `D_p ∣ (p - 1)(p + 1)` and the fact that `D_p` is
odd, after the norm identity has identified the exact minus jaw.
@isnad1 id=eq.2h1v.s6.11def6319eae from=translated src=- shape=7a7f5d94 vocab=3205af9e
-/
theorem quarticOddTail_eq_mul_jaws
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5) :
    quarticOddTail p hp5 =
      quarticMinusJaw p hp5 * quarticPlusShadow p hp5 := by
  let D := quarticOddTail p hp5
  let a := p - 1
  let b := p + 1
  let g := Nat.gcd D a
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hDcop10 : Nat.Coprime D 10 := by
    simpa [D] using quarticOddTail_coprime_ten hp hp5
  have hD0 : D ≠ 0 := by
    intro hzero
    rw [hzero] at hDcop10
    norm_num at hDcop10
  have hDcop2 : Nat.Coprime D 2 :=
    Nat.Coprime.of_dvd_right (by norm_num : 2 ∣ 10) hDcop10
  have hga : g ∣ a := Nat.gcd_dvd_right _ _
  have hgD : g ∣ D := Nat.gcd_dvd_left _ _
  have hg2 : Nat.Coprime g 2 :=
    Nat.Coprime.of_dvd_left hgD hDcop2
  have hgb : Nat.Coprime g b := by
    have heq : b = 2 + a := by
      simp only [a, b]
      omega
    rw [heq, Nat.coprime_add_iff_left hga]
    exact hg2
  have hDab : D ∣ a * b := by
    have hfield := quarticOddTail_dvd_sq_sub_one hp hp5
    have hpred : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
    have heq : a * b = p * p - 1 := by
      simp only [a, b]
      apply Nat.eq_sub_of_add_eq
      nlinarith
    rwa [heq]
  have hgpos : 0 < g :=
    Nat.gcd_pos_of_pos_left a (Nat.pos_of_ne_zero hD0)
  have hredCoprime : Nat.Coprime (D / g) (a / g) := by
    simpa [g] using
      (Nat.coprime_div_gcd_div_gcd (m := D) (n := a) hgpos)
  have hredDiv : D / g ∣ (a / g) * b := by
    have hgab : g ∣ a * b := hga.mul_right b
    have hquot : D / g ∣ (a * b) / g := by
      apply (Nat.dvd_div_iff_mul_dvd hgab).2
      rw [Nat.mul_comm g, Nat.div_mul_cancel hgD]
      exact hDab
    have heq : (a * b) / g = (a / g) * b := by
      calc
        (a * b) / g = (b * a) / g := by rw [Nat.mul_comm]
        _ = b * (a / g) := Nat.mul_div_assoc b hga
        _ = (a / g) * b := by rw [Nat.mul_comm]
    rwa [heq] at hquot
  have hredB : D / g ∣ b :=
    hredCoprime.dvd_of_dvd_mul_left hredDiv
  have hredD : D / g ∣ D := by
    refine ⟨g, ?_⟩
    rw [Nat.mul_comm]
    exact (Nat.mul_div_cancel' hgD).symm
  have hredPlus : D / g ∣ Nat.gcd D b :=
    Nat.dvd_gcd hredD hredB
  have hplusRed : Nat.gcd D b ∣ D / g := by
    let c := Nat.gcd D b
    have hcD : c ∣ D := Nat.gcd_dvd_left _ _
    have hcb : c ∣ b := Nat.gcd_dvd_right _ _
    have hgc : Nat.Coprime g c :=
      Nat.Coprime.of_dvd_right hcb hgb
    apply hgc.symm.dvd_mul_right.mp
    rw [Nat.div_mul_cancel hgD]
    exact hcD
  have hplusEq : Nat.gcd D b = D / g :=
    Nat.dvd_antisymm hplusRed hredPlus
  have hminusEq : quarticMinusJaw p hp5 = g := by
    simpa [D, a, g] using
      quarticMinusJaw_eq_gcd_oddTail_sub_one hp hp5
  have hplusDef : quarticPlusShadow p hp5 = Nat.gcd D b := by
    rfl
  rw [hminusEq, hplusDef, hplusEq]
  exact (Nat.mul_div_cancel' hgD).symm

/-- The two jaws of a single row are coprime.
@isnad1 id=coprime.2h1v.s6.4108134e8b47 from=translated src=- shape=1bdd4342 vocab=54e14372
-/
theorem quarticJaws_coprime
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5) :
    Nat.Coprime (quarticMinusJaw p hp5) (quarticPlusShadow p hp5) := by
  have hminus :
      quarticMinusJaw p hp5 ∣ p - 1 :=
    quarticMinusJaw_dvd_sub_one hp5
  have hplus :
      quarticPlusShadow p hp5 ∣ p + 1 :=
    quarticPlusShadow_dvd_add_one hp5
  have hminus2 : Nat.Coprime (quarticMinusJaw p hp5) 2 := by
    have htail2 :
        Nat.Coprime (quarticOddTail p hp5) 2 :=
      Nat.Coprime.of_dvd_right (by norm_num : 2 ∣ 10)
        (quarticOddTail_coprime_ten hp hp5)
    exact Nat.Coprime.of_dvd_left
      (quarticMinusJaw_dvd_oddTail hp hp5) htail2
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hminusPlus :
      Nat.Coprime (quarticMinusJaw p hp5) (p + 1) := by
    have heq : p + 1 = 2 + (p - 1) := by omega
    rw [heq, Nat.coprime_add_iff_left hminus]
    exact hminus2
  exact Nat.Coprime.of_dvd_right hplus hminusPlus

/-- **Cross-sign incidence law.**

If a divisor occurs in the norm-visible `p - 1` jaw of one row and in the
visible `r + 1` shadow of another, then the ordinary odd-tail incidence
relation forces it to divide `2`.  Hence no odd prime can occur on opposite
sides.

The statement is separated from the row hypotheses on purpose: `hgap` is
the exact incidence consequence supplied by two compatible quartic rows.
@isnad1 id=dvd.7h3v.s7.a76f5d1769c5 from=translated src=- shape=ff510976 vocab=0003532c
-/
theorem quarticCrossJaw_dvd_two_of_incidence
    {p r ℓ : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hp5 : p ≠ 5) (hr5 : r ≠ 5) (hpr : p ≤ r)
    (hgap :
      Nat.gcd (quarticOddTail p hp5) (quarticOddTail r hr5) ∣ r - p)
    (hminus : ℓ ∣ quarticMinusJaw p hp5)
    (hplus : ℓ ∣ quarticPlusShadow r hr5) :
    ℓ ∣ 2 := by
  have hℓTailP : ℓ ∣ quarticOddTail p hp5 :=
    hminus.trans (quarticMinusJaw_dvd_oddTail hp hp5)
  have hℓTailR : ℓ ∣ quarticOddTail r hr5 :=
    hplus.trans (quarticPlusShadow_dvd_oddTail hr5)
  have hℓGap : ℓ ∣ r - p :=
    (Nat.dvd_gcd hℓTailP hℓTailR).trans hgap
  have hℓMinus : ℓ ∣ p - 1 :=
    hminus.trans (quarticMinusJaw_dvd_sub_one hp5)
  have hℓPlus : ℓ ∣ r + 1 :=
    hplus.trans (quarticPlusShadow_dvd_add_one hr5)
  have hℓWide : ℓ ∣ (r + 1) - (p - 1) :=
    Nat.dvd_sub hℓPlus hℓMinus
  have hwideEq : (r + 1) - (p - 1) = (r - p) + 2 := by
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    omega
  rw [hwideEq] at hℓWide
  have hℓTwo : ℓ ∣ ((r - p) + 2) - (r - p) :=
    Nat.dvd_sub hℓWide hℓGap
  simpa using hℓTwo

/-- The reverse orientation of the cross-sign law: a divisor in the
`p + 1` jaw of the smaller row and the `r - 1` jaw of the larger row is
also forced to divide `2`.
@isnad1 id=dvd.7h3v.s7.0b7c61a95d26 from=translated src=- shape=9c612443 vocab=0003532c
-/
theorem quarticCrossJaw_reverse_dvd_two_of_incidence
    {p r ℓ : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hp5 : p ≠ 5) (hr5 : r ≠ 5) (hpr : p ≤ r)
    (hgap :
      Nat.gcd (quarticOddTail p hp5) (quarticOddTail r hr5) ∣ r - p)
    (hplus : ℓ ∣ quarticPlusShadow p hp5)
    (hminus : ℓ ∣ quarticMinusJaw r hr5) :
    ℓ ∣ 2 := by
  have hℓTailP : ℓ ∣ quarticOddTail p hp5 :=
    hplus.trans (quarticPlusShadow_dvd_oddTail hp5)
  have hℓTailR : ℓ ∣ quarticOddTail r hr5 :=
    hminus.trans (quarticMinusJaw_dvd_oddTail hr hr5)
  have hℓGap : ℓ ∣ r - p :=
    (Nat.dvd_gcd hℓTailP hℓTailR).trans hgap
  have hℓPlus : ℓ ∣ p + 1 :=
    hplus.trans (quarticPlusShadow_dvd_add_one hp5)
  have hℓMinus : ℓ ∣ r - 1 :=
    hminus.trans (quarticMinusJaw_dvd_sub_one hr5)
  have hℓRPlus : ℓ ∣ (r - p) + (p + 1) :=
    dvd_add hℓGap hℓPlus
  have hsumEq : (r - p) + (p + 1) = r + 1 := by
    omega
  rw [hsumEq] at hℓRPlus
  have hℓTwo : ℓ ∣ (r + 1) - (r - 1) :=
    Nat.dvd_sub hℓRPlus hℓMinus
  have hr0 : 0 < r := (Fact.out : r.Prime).pos
  have htwoEq : (r + 1) - (r - 1) = 2 := by omega
  rwa [htwoEq] at hℓTwo

/-- Both cross orientations, packaged as the canonical forced partition
of two incident odd tails.
@isnad1 id=and.6h2v.s7.e0165c5e286d from=translated src=- shape=42680320 vocab=0003532c
-/
theorem quarticCrossJaws_partition_of_incidence
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hp5 : p ≠ 5) (hr5 : r ≠ 5) (hpr : p ≤ r)
    (hgap :
      Nat.gcd (quarticOddTail p hp5) (quarticOddTail r hr5) ∣ r - p) :
    (∀ ℓ, ℓ ∣ quarticMinusJaw p hp5 →
      ℓ ∣ quarticPlusShadow r hr5 → ℓ ∣ 2)
      ∧
    (∀ ℓ, ℓ ∣ quarticPlusShadow p hp5 →
      ℓ ∣ quarticMinusJaw r hr5 → ℓ ∣ 2) := by
  exact ⟨fun ℓ =>
      quarticCrossJaw_dvd_two_of_incidence hp hp5 hr5 hpr hgap,
    fun ℓ =>
      quarticCrossJaw_reverse_dvd_two_of_incidence hr hp5 hr5 hpr hgap⟩

end AgrawalCore
