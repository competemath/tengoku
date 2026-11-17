import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Weierstrass
import Tengoku.Seed.RingTheory.Int.Basic
import Tengoku.Seed.Tactic
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FreyPackage_dvd_freyCurveInt_discr_iff.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FreyPackage_dvd_freyCurveInt_discr_iff

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
@isnad1 id=dvd.2h2v.s5.a088e74b63b7 from=translated src=- shape=5b1fbc81 vocab=7120ff69
-/
theorem dvd_abc_of_dvd_freyCurveInt_Δ (P : FreyPackage) {q : ℕ} (hq : q.Prime)
    (hdvd : (q : ℤ) ∣ (freyCurveInt P).Δ) : (q : ℤ) ∣ P.a * P.b * P.c := by
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  exact hqZ.dvd_of_dvd_pow (n := 2 * P.p)
    (freyCurveInt_Δ_mul P ▸ hdvd.mul_right (2 ^ 8))

end FreyArith

/--
@isnad1 id=iff.1h2v.s5.ef63a4913ce5 from=translated src=- shape=19ed9daf vocab=7120ff69
-/
theorem solution (P : FreyPackage) {q : ℕ} (hq : q.Prime) :
    (q : ℤ) ∣ P.freyCurveInt.Δ ↔ (q : ℤ) ∣ P.a * P.b * P.c := by
  constructor
  · exact FreyArith.dvd_abc_of_dvd_freyCurveInt_Δ P hq
  · intro hqabc
    have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    by_cases hq2 : q = 2
    ·
      subst hq2
      have hb : (2 : ℤ) ∣ P.a * P.b * P.c := hqabc

      have h1 : (2 : ℤ) ^ (2 * P.p) ∣ P.freyCurveInt.Δ * 2 ^ 8 := by
        rw [FreyArith.freyCurveInt_Δ_mul]; exact pow_dvd_pow_of_dvd hb _
      have hp : 5 ≤ P.p := P.hp5
      have h2 : (2 : ℤ) ^ (2 * P.p) = 2 ^ 8 * (2 * 2 ^ (2 * P.p - 9)) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      rw [h2] at h1
      have h3 : (2 : ℤ) * 2 ^ (2 * P.p - 9) ∣ P.freyCurveInt.Δ := by
        have h8 : (2 : ℤ) ^ 8 ≠ 0 := by positivity
        rw [mul_comm] at h1
        exact (mul_dvd_mul_iff_right h8).mp (by simpa [mul_comm, mul_assoc, mul_left_comm] using h1)
      exact (Dvd.intro _ rfl).trans h3
    · have h : (q : ℤ) ∣ P.freyCurveInt.Δ * 2 ^ 8 := by
        rw [FreyArith.freyCurveInt_Δ_mul]; exact dvd_pow hqabc (by have := P.hp0; omega)
      refine (hqZ.dvd_or_dvd h).resolve_right ?_
      intro h28
      have h2 : (q : ℤ) ∣ 2 := hqZ.dvd_of_dvd_pow h28
      have h2' : q ∣ 2 := by exact_mod_cast h2
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2')
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
