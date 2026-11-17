import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FreyPackage_frey_isSemistableModel.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FreyPackage_frey_isSemistableModel

set_option autoImplicit false

namespace FreyPackage
export _root_.Tengoku.FltAnthropic.FreyPackage (hp0 hgcdac hgcdbc habc0 freyCurveInt freyCurve c hb2 p a hgcdab hp5 b hFLT ha4 pp)
open _root_.Tengoku.FltAnthropic.FreyPackage

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
@isnad1 id=eq.0h1v.s3.17ce1744ff6f from=translated src=- shape=58a91df6 vocab=e8f2fa11
-/
theorem freyCurve_c₄_eq_intCast (P : FreyPackage) : P.freyCurve.c₄ = (c₄Int P : ℚ) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, freyCurve, c₄Int]
  push_cast
  field_simp
  ring

/--
@isnad1 id=eq.0h1v.s6.ec9bd0e77bea from=translated src=- shape=44b1da3a vocab=825b52ca
-/
theorem c₄Int_eq_sub (P : FreyPackage) : c₄Int P = (P.c ^ P.p) ^ 2 - (P.a * P.b) ^ P.p := by
  rw [c₄Int, ← P.hFLT, mul_pow]
  ring

/--
@isnad1 id=not.2h2v.s5.d0f4f65d7494 from=translated src=- shape=6e09de33 vocab=9ed685b4
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
@isnad1 id=eq.0h1v.s3.53e762e4b0ec from=translated src=- shape=0a9af14d vocab=6094edaa
-/
theorem freyCurveInt_c₄ (P : FreyPackage) : (freyCurveInt P).c₄ = c₄Int P := by
  have h : (algebraMap ℤ ℚ) (freyCurveInt P).c₄ = ((c₄Int P : ℤ) : ℚ) := by
    rw [← map_c₄, freyCurveInt_map, ← freyCurve_c₄_eq_intCast]
  rw [eq_intCast] at h
  exact_mod_cast h

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

/--
@isnad1 id=issemist.0h1v.s2.4772ac545a2a from=translated src=- shape=76a08d12 vocab=2c31e2fc
-/
theorem frey_isSemistableModel (P : FreyPackage) : (freyCurveInt P).IsSemistableModel := by
  intro q hq hdvdΔ
  rw [freyCurveInt_c₄]
  exact not_dvd_c₄Int P (Nat.prime_iff_prime_int.mp hq)
    (dvd_abc_of_dvd_freyCurveInt_Δ P hq hdvdΔ)

end FreyPackage

/--
@isnad1 id=issemist.0h1v.s2.4772ac545a2a from=translated src=- shape=76a08d12 vocab=2c31e2fc
-/
theorem solution (P : FreyPackage) : P.freyCurveInt.IsSemistableModel :=
  FreyPackage.frey_isSemistableModel P
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
