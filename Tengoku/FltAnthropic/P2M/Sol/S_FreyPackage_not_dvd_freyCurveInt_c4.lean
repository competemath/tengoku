import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Weierstrass
import Tengoku.Seed.RingTheory.Int.Basic
import Tengoku.Seed.Tactic
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FreyPackage_not_dvd_freyCurveInt_c4.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FreyPackage_not_dvd_freyCurveInt_c4

set_option autoImplicit false

namespace FreyArith

open Tengoku.FltAnthropic.FreyPackage

open WeierstrassCurve

/--
@isnad1 id=eq.0h1v.s4.309d22298e79 from=translated src=- shape=b4d18b3e vocab=01b2f9d2
-/
theorem freyCurveInt_map (P : FreyPackage) :
    (freyCurveInt P).map (algebraMap ℤ ℚ) = freyCurve P := by
  have two_dvd_b : 2 ∣ P.b := (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).1 P.hb2
  ext
  · rfl
  · change (((P.b ^ P.p - 1 - P.a ^ P.p) / 4 : ℤ) : ℚ) = (P.b ^ P.p - 1 - P.a ^ P.p) / 4
    rw [Rat.intCast_div]
    · norm_cast
    · rw [sub_sub]
      apply Int.dvd_sub
      · calc
          (4 : ℤ) = 2 ^ 2     := by norm_num
          _       ∣ P.b ^ 2   := pow_dvd_pow_of_dvd two_dvd_b 2
          _       ∣ P.b ^ P.p := pow_dvd_pow P.b (by linarith [P.hp5])
      · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1
        push_cast
        rw [P.ha4, show (3 : ZMod 4) = -1 from rfl, neg_one_pow_eq_ite, ite_eq_right]
        · norm_num
        · rw [Nat.Prime.even_iff P.pp]
          linarith [P.hp5]
  · rfl
  · change ((-(P.a ^ P.p) * (P.b ^ P.p) / 16 : ℤ) : ℚ) = -(P.a ^ P.p) * (P.b ^ P.p) / 16
    rw [Rat.intCast_div]
    · norm_cast
    · calc
        (16 : ℤ) = 2 ^ 4     := by norm_num
        _        ∣ P.b ^ 4   := pow_dvd_pow_of_dvd two_dvd_b 4
        _        ∣ P.b ^ P.p := pow_dvd_pow P.b (by linarith [P.hp5])
        _        ∣ _         := Int.dvd_mul_left _ _
  · rfl

def c₄Int (P : FreyPackage) : ℤ :=
  (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2

/--
@isnad1 id=eq.0h1v.s3.6ee3d6f8e2df from=translated src=- shape=58a91df6 vocab=3e6e0ad4
-/
theorem freyCurve_c₄_eq_intCast (P : FreyPackage) : P.freyCurve.c₄ = (c₄Int P : ℚ) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, freyCurve, c₄Int]
  push_cast
  field_simp
  ring

/--
@isnad1 id=eq.0h1v.s6.5e4a046db342 from=translated src=- shape=44b1da3a vocab=78a3bd4c
-/
theorem c₄Int_eq_sub (P : FreyPackage) : c₄Int P = (P.c ^ P.p) ^ 2 - (P.a * P.b) ^ P.p := by
  rw [c₄Int, ← P.hFLT, mul_pow]
  ring

/--
@isnad1 id=not.2h2v.s5.6bfba98cb787 from=translated src=- shape=6e09de33 vocab=2a74c187
-/
theorem not_dvd_c₄Int (P : FreyPackage) {q : ℤ} (hq : Prime q)
    (hqbad : q ∣ P.a * P.b * P.c) : ¬q ∣ c₄Int P := by
  intro hdvd
  rcases hq.dvd_mul.mp hqbad with hab | hc
  · rcases hq.dvd_mul.mp hab with ha | hb
    ·
      have hqb : ¬q ∣ P.b := fun hb =>
        hq.not_isUnit (isUnit_of_dvd_one (P.hgcdab ▸ dvd_gcd ha hb))
      have hqap : q ∣ P.a ^ P.p := dvd_pow ha P.hp0
      rw [c₄Int, dvd_add_right (dvd_add (dvd_pow hqap two_ne_zero)
        (dvd_mul_of_dvd_left hqap _))] at hdvd
      exact hqb (hq.dvd_of_dvd_pow (hq.dvd_of_dvd_pow hdvd))
    ·
      have hqa : ¬q ∣ P.a := fun ha =>
        hq.not_isUnit (isUnit_of_dvd_one (P.hgcdab ▸ dvd_gcd ha hb))
      have hqbp : q ∣ P.b ^ P.p := dvd_pow hb P.hp0
      rw [c₄Int, add_assoc, dvd_add_left (dvd_add (dvd_mul_of_dvd_right hqbp _)
        (dvd_pow hqbp two_ne_zero))] at hdvd
      exact hqa (hq.dvd_of_dvd_pow (hq.dvd_of_dvd_pow hdvd))
  ·
    have hqa : ¬q ∣ P.a := fun ha =>
      hq.not_isUnit (isUnit_of_dvd_one (P.hgcdac ▸ dvd_gcd ha hc))
    have hqb : ¬q ∣ P.b := fun hb =>
      hq.not_isUnit (isUnit_of_dvd_one (P.hgcdbc ▸ dvd_gcd hb hc))
    rw [c₄Int_eq_sub, dvd_sub_right (dvd_pow (dvd_pow hc P.hp0) two_ne_zero)] at hdvd
    rcases hq.dvd_mul.mp (hq.dvd_of_dvd_pow hdvd) with h | h
    exacts [hqa h, hqb h]

/--
@isnad1 id=eq.0h1v.s3.10664bafc521 from=translated src=- shape=0a9af14d vocab=421513d5
-/
theorem freyCurveInt_c₄ (P : FreyPackage) : (freyCurveInt P).c₄ = c₄Int P := by
  have h : (algebraMap ℤ ℚ) (freyCurveInt P).c₄ = ((c₄Int P : ℤ) : ℚ) := by
    rw [← map_c₄, freyCurveInt_map, ← freyCurve_c₄_eq_intCast]
  rw [eq_intCast] at h
  exact_mod_cast h

end FreyArith

/--
@isnad1 id=not.2h2v.s5.b037f1ec5650 from=translated src=- shape=120a904d vocab=f399301f
-/
theorem solution (P : FreyPackage) {q : ℕ} (hq : q.Prime)
    (hqabc : (q : ℤ) ∣ P.a * P.b * P.c) : ¬ (q : ℤ) ∣ P.freyCurveInt.c₄ := by
  rw [FreyArith.freyCurveInt_c₄]
  exact FreyArith.not_dvd_c₄Int P (Nat.prime_iff_prime_int.mp hq) hqabc
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
