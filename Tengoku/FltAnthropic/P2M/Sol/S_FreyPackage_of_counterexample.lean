import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage
import Tengoku.Seed.Tactic.ModCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FreyPackage_of_counterexample.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FreyPackage_of_counterexample

set_option autoImplicit false

namespace FreyPackage
export _root_.Tengoku.FltAnthropic.FreyPackage (gcdab_eq_gcdac c hb2 p a hc0 ha0 hgcdab hp5 b hFLT hb0 ha4 pp)
open _root_.Tengoku.FltAnthropic.FreyPackage

/--
@isnad1 id=nonempty.6h4v.s6.3e1c8eccca72 from=translated src=- shape=4225025c vocab=2053c56c
-/
theorem of_counterexample (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (p : ℕ) (pp : p.Prime) (hp5 : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p) :
    Nonempty FreyPackage := by
  have p_odd := pp.odd_of_ne_two (by omega)

  have ⟨a, b, c, a0, b0, c0, ab, H⟩ :
      ∃ (a b c : ℤ), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ Int.gcd a b = 1 ∧ a ^ p + b ^ p = c ^ p := by
    obtain ⟨d, a', b', d0, cop, a_eq, b_eq⟩ :=
      Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left b ha)
    simp only [a_eq, mul_pow, b_eq] at H
    rw [← add_mul, mul_comm] at H
    obtain ⟨c', rfl⟩ := (Int.pow_dvd_pow_iff pp.ne_zero).1 ⟨_, H.symm⟩
    rw [mul_pow] at H
    have a0' := left_ne_zero_of_mul (a_eq ▸ ha)
    have b0' := left_ne_zero_of_mul (b_eq ▸ hb)
    have c0' := right_ne_zero_of_mul hc
    exact ⟨a', b', c', a0', b0', c0', cop,
      mul_left_cancel₀ (pow_ne_zero _ (mod_cast d0.ne')) H⟩

  have ⟨a, b, c, a0, b0, c0, ab, eb, H⟩ :
      ∃ (a b c : ℤ), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ Int.gcd a b = 1 ∧ Even b ∧
        a ^ p + b ^ p = c ^ p := by
    if eb : Even b then
      exact ⟨a, b, c, a0, b0, c0, ab, eb, H⟩
    else if ea : Even a then
      exact ⟨b, a, c, b0, a0, c0, Int.gcd_comm a b ▸ ab, ea, by rwa [add_comm]⟩
    else
      refine ⟨a, -c, -b, a0, neg_ne_zero.2 c0, neg_ne_zero.2 b0, ?_, even_neg.2 ?_, ?_⟩
      · refine Int.gcd_neg.trans (.trans (.symm ?_) ab)
        exact Nat.cast_inj.1 (gcdab_eq_gcdac pp.pos H)
      · refine ((Int.even_pow (n := p)).1 (H.symm ▸ Int.even_add.2 (iff_of_false ?_ ?_))).1
        · exact fun h => ea (Int.even_pow.1 h).1
        · exact fun h => eb (Int.even_pow.1 h).1
      · simp [p_odd.neg_pow, ← H]

  have ⟨a, b, c, ha0, hb0, hc0, ab, ha3, eb, hFLT⟩ :
      ∃ (a b c : ℤ), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ Int.gcd a b = 1 ∧
        a ≡ 3 [ZMOD 4] ∧ Even b ∧ a ^ p + b ^ p = c ^ p := by
    have a_odd' : ∀ {i}, a ≡ i [ZMOD 4] → ¬2 ∣ i := fun ai ei => by
      have ea := (dvd_sub_right ei).1 (.trans (by decide) (Int.modEq_iff_dvd.1 ai))
      simpa +decide [gcd, ab] using dvd_gcd ea (even_iff_two_dvd.1 eb)
    mod_cases a_mod : a % 4
    · cases a_odd' a_mod (by decide)
    · exact ⟨-a, -b, -c, neg_ne_zero.2 a0, neg_ne_zero.2 b0, neg_ne_zero.2 c0,
        by rwa [Int.neg_gcd, Int.gcd_neg], a_mod.neg, eb.neg,
        by simp [p_odd.neg_pow, ← H, add_comm]⟩
    · cases a_odd' a_mod (by decide)
    · exact ⟨a, b, c, a0, b0, c0, ab, a_mod, eb, H⟩

  exact ⟨{
    a, b, c, ha0, hb0, hc0, p, pp, hp5, hFLT
    hgcdab := by simp [gcd, ab]
    ha4 := (ZMod.intCast_eq_intCast_iff ..).2 ha3
    hb2 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).2 (even_iff_two_dvd.1 eb)
  }⟩

end FreyPackage

/--
@isnad1 id=nonempty.6h4v.s6.3e1c8eccca72 from=translated src=- shape=4225025c vocab=2053c56c
-/
theorem solution (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (p : ℕ) (pp : p.Prime) (hp5 : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p) :
    Nonempty FreyPackage :=
  FreyPackage.of_counterexample a b c ha hb hc p pp hp5 H
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
