/-
Copyright (c) 2024 Kevin Buzzard, Ruben Van de Velde, Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Ported from the Imperial College London FLT formalization
(https://github.com/ImperialCollegeLondon/FLT, blueprint §2.5–2.6).
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Weierstrass
import Tengoku.Seed.Algebra.Field.ZMod
import Tengoku.Seed.Algebra.GCDMonoid.Nat
import Tengoku.Seed.Algebra.EuclideanDomain.Int
import Tengoku.Seed.Data.Nat.Prime.Basic
import Tengoku.Seed.RingTheory.Int.Basic
import Tengoku.Seed.Tactic.ModCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

structure FreyPackage where

  a : ℤ

  b : ℤ

  c : ℤ
  ha0 : a ≠ 0
  hb0 : b ≠ 0
  hc0 : c ≠ 0

  p : ℕ
  pp : Nat.Prime p
  hp5 : 5 ≤ p

  hFLT : a ^ p + b ^ p = c ^ p

  hgcdab : gcd a b = 1

  ha4 : (a : ZMod 4) = 3

  hb2 : (b : ZMod 2) = 0

namespace FreyPackage

/--
@isnad1 id=lt.0h1v.s3.e2637505f9b6 from=translated src=- shape=b9369acb vocab=8a1366db
-/
lemma hppos (P : FreyPackage) : 0 < P.p := lt_of_lt_of_le (by omega) P.hp5

/--
@isnad1 id=ne.0h1v.s3.b2d973d1db5a from=translated src=- shape=a311c14d vocab=c1e0584d
-/
lemma hp0 (P : FreyPackage) : P.p ≠ 0 := P.hppos.ne'

/--
@isnad1 id=odd.0h1v.s2.ea198c174fee from=translated src=- shape=1a6c1393 vocab=3e42ab94
-/
lemma hp_odd (P : FreyPackage) : Odd P.p :=
  P.pp.odd_of_ne_two (by have := P.hp5; omega)

/--
@isnad1 id=eq.2h4v.s6.d2e66bed10f2 from=translated src=- shape=bf2e354d vocab=fd5cc21d
-/
lemma gcdab_eq_gcdac {a b c : ℤ} {p : ℕ} (hp : 0 < p) (h : a ^ p + b ^ p = c ^ p) :
    gcd a b = gcd a c := by
  have foo : gcd a b ∣ gcd a c := by
    apply dvd_gcd (gcd_dvd_left a b)
    rw [← Int.pow_dvd_pow_iff hp.ne', ← h]
    apply dvd_add <;> rw [Int.pow_dvd_pow_iff hp.ne']
    · exact gcd_dvd_left a b
    · exact gcd_dvd_right a b
  have bar : gcd a c ∣ gcd a b := by
    apply dvd_gcd (gcd_dvd_left a c)
    have h2 : b ^ p = c ^ p - a ^ p := eq_sub_of_add_eq' h
    rw [← Int.pow_dvd_pow_iff hp.ne', h2]
    apply dvd_add
    · rw [Int.pow_dvd_pow_iff hp.ne']; exact gcd_dvd_right a c
    · rw [dvd_neg, Int.pow_dvd_pow_iff hp.ne']; exact gcd_dvd_left a c
  change _ ∣ (Int.gcd a c : ℤ) at foo
  apply Int.ofNat_dvd.1 at bar
  apply Int.ofNat_dvd.1 at foo
  exact congr_arg ((↑) : ℕ → ℤ) <| Nat.dvd_antisymm foo bar

/--
@isnad1 id=eq.0h1v.s4.dd4c91b4ebe3 from=translated src=- shape=ce40f469 vocab=ca17dc30
-/
lemma hgcdac (P : FreyPackage) : gcd P.a P.c = 1 := by
  rw [← gcdab_eq_gcdac P.hppos P.hFLT, P.hgcdab]

/--
@isnad1 id=eq.0h1v.s4.7da9f18aef4e from=translated src=- shape=ce40f469 vocab=598dca26
-/
lemma hgcdbc (P : FreyPackage) : gcd P.b P.c = 1 := by
  rw [← gcdab_eq_gcdac P.hppos, gcd_comm, P.hgcdab]
  rw [add_comm]; exact P.hFLT

/--
@isnad1 id=ne.0h1v.s4.ff1faba46509 from=translated src=- shape=0226a5d7 vocab=23ab72f8
-/
lemma habc0 (P : FreyPackage) : P.a * P.b * P.c ≠ 0 :=
  mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0

/--
@isnad1 id=dvd.0h1v.s4.23e79e02d97c from=translated src=- shape=d82892f1 vocab=716c665b
-/
lemma two_dvd_abc (P : FreyPackage) : (2 : ℤ) ∣ P.a * P.b * P.c :=
  dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
    ((ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).1 P.hb2) _) _

def freyCurveInt (P : FreyPackage) : WeierstrassCurve ℤ where
  a₁ := 1
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16
  a₆ := 0

def freyCurve (P : FreyPackage) : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16
  a₆ := 0

end FreyPackage
