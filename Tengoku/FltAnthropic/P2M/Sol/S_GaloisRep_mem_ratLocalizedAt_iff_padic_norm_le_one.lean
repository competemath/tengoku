import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.Theorems.Thm_GaloisRep_mem_ratLocalizedAt_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRep_mem_ratLocalizedAt_iff_padic_norm_le_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRep_mem_ratLocalizedAt_iff_padic_norm_le_one

set_option maxHeartbeats 8000000

theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℚ) :
    q ∈ GaloisRep.ratLocalizedAt p ↔ ‖(q : ℚ_[p])‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  rw [GaloisRep.mem_ratLocalizedAt_iff hp]
  rcases eq_or_ne q 0 with rfl | hq
  · simp [Rat.den_zero, hp.one_lt.ne']

  rw [Padic.norm_le_one_iff_val_nonneg]

  have hval : (↑q : ℚ_[p]).valuation = padicValRat p q := by
    exact_mod_cast Padic.valuation_ratCast (p := p) q
  rw [hval]

  have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
  have hden : q.den ≠ 0 := q.den_ne_zero
  have hden0 : padicValNat p q.den = 0 ↔ ¬ p ∣ q.den := by
    simp [padicValNat.eq_zero_iff, hden, hp.one_lt.ne']
  constructor
  · intro hnd
    rw [← hden0] at hnd
    have : padicValRat p q = padicValInt p q.num - (0:ℤ) := by
      rw [show padicValRat p q = (padicValInt p q.num : ℤ) - padicValNat p q.den from rfl, hnd]
      ring
    rw [this]; simp [padicValInt]
  · intro h0
    intro hpden

    have hpnum : ¬ p ∣ q.num.natAbs := fun hpnum =>
      hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hpnum hpden)
    have hnum0 : padicValInt p q.num = 0 := by
      simp [padicValInt, padicValNat.eq_zero_iff, hpnum,
            Int.natAbs_eq_zero, Rat.num_ne_zero.mpr hq]
    have hdenpos : 1 ≤ padicValNat p q.den :=
      Nat.one_le_iff_ne_zero.mpr (fun h => (hden0.mp h) hpden)
    have : padicValRat p q < 0 := by
      rw [show padicValRat p q = (padicValInt p q.num : ℤ) - padicValNat p q.den from rfl,
          hnum0]
      omega
    linarith
