import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Weierstrass
import Tengoku.Seed.RingTheory.Int.Basic
import Tengoku.Seed.Tactic
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FreyPackage_padicValInt_freyCurveInt_discr.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FreyPackage_padicValInt_freyCurveInt_discr

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

/--
@isnad1 id=eq.0h1v.s6.e8591116e2a1 from=translated src=- shape=52e0e257 vocab=65806b86
-/
theorem freyCurve_Δ (P : FreyPackage) :
    P.freyCurve.Δ = (P.a * P.b * P.c) ^ (2 * P.p) / 2 ^ 8 := by
  trans (P.a ^ P.p) ^ 2 * (P.b ^ P.p) ^ 2 * (P.c ^ P.p) ^ 2 / 2 ^ 8
  · field_simp
    norm_cast
    simp [← P.hFLT, WeierstrassCurve.Δ, freyCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  · simp [← mul_pow, ← pow_mul, mul_comm 2]

def c₄Int (P : FreyPackage) : ℤ :=
  (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2

/--
@isnad1 id=eq.0h1v.s6.83358e8f5bb7 from=translated src=- shape=f145f80f vocab=5874919a
-/
theorem freyCurveInt_Δ_mul (P : FreyPackage) :
    (freyCurveInt P).Δ * 2 ^ 8 = (P.a * P.b * P.c) ^ (2 * P.p) := by
  have hΔ : (algebraMap ℤ ℚ) (freyCurveInt P).Δ
      = (P.a * P.b * P.c : ℚ) ^ (2 * P.p) / 2 ^ 8 := by
    rw [← map_Δ, freyCurveInt_map, freyCurve_Δ]
  rw [eq_intCast] at hΔ
  have h : ((((freyCurveInt P).Δ * 2 ^ 8 : ℤ)) : ℚ)
      = (((P.a * P.b * P.c) ^ (2 * P.p) : ℤ) : ℚ) := by
    push_cast
    rw [hΔ]
    field_simp
    norm_num
  exact_mod_cast h

/--
@isnad1 id=ne.0h1v.s3.55fd660a0bdb from=translated src=- shape=562e4a6d vocab=f5c91ea8
-/
theorem freyCurveInt_Δ_ne_zero (P : FreyPackage) : (freyCurveInt P).Δ ≠ 0 := by
  intro h
  have := freyCurveInt_Δ_mul P
  rw [h, zero_mul] at this
  exact pow_ne_zero _ P.habc0 this.symm

/--
@isnad1 id=eq.2h2v.s6.5d864332aff3 from=translated src=- shape=6352cb2e vocab=ff236e90
-/
theorem padicValInt_freyCurveInt_Δ (P : FreyPackage) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    padicValInt q (freyCurveInt P).Δ = 2 * P.p * padicValInt q (P.a * P.b * P.c) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hq28 : ¬ (q : ℤ) ∣ 2 ^ 8 := by
    intro h
    have h2 : (q : ℤ) ∣ 2 := hqZ.dvd_of_dvd_pow h
    have h2' : q ∣ 2 := by exact_mod_cast h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2')
  have hmul : padicValInt q ((freyCurveInt P).Δ * 2 ^ 8) = padicValInt q (freyCurveInt P).Δ := by
    rw [padicValInt.mul (freyCurveInt_Δ_ne_zero P) (by norm_num),
      padicValInt.eq_zero_of_not_dvd hq28, add_zero]
  rw [← hmul, freyCurveInt_Δ_mul]
  simp only [padicValInt, Int.natAbs_pow]
  exact padicValNat.pow _ _

end FreyArith

/--
@isnad1 id=eq.2h2v.s6.5d864332aff3 from=translated src=- shape=6352cb2e vocab=ff236e90
-/
theorem solution (P : FreyPackage) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    padicValInt q P.freyCurveInt.Δ = 2 * P.p * padicValInt q (P.a * P.b * P.c) :=
  FreyArith.padicValInt_freyCurveInt_Δ P hq hq2
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
