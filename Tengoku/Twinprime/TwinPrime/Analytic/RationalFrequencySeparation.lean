import Tengoku.Seed.Analysis.Normed.Group.AddCircle
import Tengoku.Seed.Data.Nat.GCD.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Spacing of rational frequencies on the unit additive circle

The nearest-integer representative of a difference of rational frequencies
has an integer numerator after multiplication by the two denominators.
Distinct frequencies therefore have distance at least the reciprocal product.
Reduced representatives are unique, including frequency zero at modulus one.
-/

noncomputable section

namespace TwinPrime.Analytic

/-- Distinct rational frequencies have reciprocal-product spacing on the circle.-/
theorem rational_frequency_dist_ge (a b : ℤ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hne : (((a : ℝ) / q : ℝ) : UnitAddCircle) ≠ (((b : ℝ) / r : ℝ) : UnitAddCircle)) :
    (1 : ℝ) / ((q : ℝ) * r) ≤
      dist ((((a : ℝ) / q : ℝ) : UnitAddCircle)) ((((b : ℝ) / r : ℝ) : UnitAddCircle)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  let x : ℝ := (a : ℝ) / q - (b : ℝ) / r
  let k : ℤ := a * r - b * q - round x * q * r
  have hnum : x - (round x : ℝ) = (k : ℝ) / ((q : ℝ) * r) := by
    dsimp only [k, x]
    push_cast
    field_simp
  have hdist : dist ((((a : ℝ) / q : ℝ) : UnitAddCircle))
      ((((b : ℝ) / r : ℝ) : UnitAddCircle)) = |(k : ℝ)| / ((q : ℝ) * r) := by
    rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq]
    change |x - (round x : ℝ)| = _
    rw [hnum, abs_div, abs_of_pos (mul_pos hq0 hr0)]
  have hk : k ≠ 0 := by
    intro hk
    have h := hdist
    simp only [hk, Int.cast_zero, abs_zero, zero_div] at h
    exact hne (dist_eq_zero.mp h)
  have hkabs : (1 : ℝ) ≤ |(k : ℝ)| := by
    rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero ℝ hk with h | h
    · exact (show (1 : ℝ) ≤ -(k : ℝ) by linarith).trans (neg_le_abs _)
    · exact h.trans (le_abs_self _)
  rw [hdist]
  exact div_le_div_of_nonneg_right hkabs (mul_pos hq0 hr0).le

/-- Uniform spacing for all denominators bounded by `Q`.-/
theorem rational_frequency_dist_ge_inv_sq (a b : ℤ) (q r Q : ℕ)
    (hq : 0 < q) (hr : 0 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (hne : (((a : ℝ) / q : ℝ) : UnitAddCircle) ≠ (((b : ℝ) / r : ℝ) : UnitAddCircle)) :
    (1 : ℝ) / (Q : ℝ) ^ 2 ≤
      dist ((((a : ℝ) / q : ℝ) : UnitAddCircle)) ((((b : ℝ) / r : ℝ) : UnitAddCircle)) := by
  have hprod0 : (0 : ℝ) < (q : ℝ) * r := by positivity
  have hprod : (q : ℝ) * r ≤ (Q : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul
      (show (q : ℝ) ≤ Q by exact_mod_cast hqQ)
      (show (r : ℝ) ≤ Q by exact_mod_cast hrQ)
      (Nat.cast_nonneg r) (Nat.cast_nonneg Q)
  exact (div_le_div_of_nonneg_left (by norm_num) hprod0 hprod).trans
    (rational_frequency_dist_ge a b q r hq hr hne)

/-- Two reduced representatives in `[0,1)` have the same frequency only if
both their denominators and their numerators agree.-/
theorem reduced_rational_frequency_unique (a b q r : ℕ)
    (hq : 0 < q) (hr : 0 < r) (ha : a < q) (hb : b < r)
    (haq : Nat.Coprime a q) (hbr : Nat.Coprime b r)
    (heq : (((a : ℝ) / q : ℝ) : UnitAddCircle) = (((b : ℝ) / r : ℝ) : UnitAddCircle)) :
    q = r ∧ a = b := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have haI : (a : ℝ) / q ∈ Set.Ico (0 : ℝ) (0 + 1) :=
    ⟨by positivity, by simpa only [zero_add] using
      (div_lt_one hq0).mpr (show (a : ℝ) < q by exact_mod_cast ha)⟩
  have hbI : (b : ℝ) / r ∈ Set.Ico (0 : ℝ) (0 + 1) :=
    ⟨by positivity, by simpa only [zero_add] using
      (div_lt_one hr0).mpr (show (b : ℝ) < r by exact_mod_cast hb)⟩
  have hreal : (a : ℝ) / q = (b : ℝ) / r :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp heq
  have hcross : a * r = b * q := by
    exact_mod_cast (div_eq_div_iff hq0.ne' hr0.ne').mp hreal
  have hqr : q ∣ r := haq.symm.dvd_of_dvd_mul_left (by rw [hcross]; exact dvd_mul_left _ _)
  have hrq : r ∣ q := hbr.symm.dvd_of_dvd_mul_left (by rw [← hcross]; exact dvd_mul_left _ _)
  have hden : q = r := Nat.dvd_antisymm hqr hrq
  refine ⟨hden, ?_⟩
  rw [← hden] at hcross
  exact Nat.eq_of_mul_eq_mul_right hq hcross

/-- Unit residues across positive moduli give distinct circle frequencies,
except for the identical denominator and canonical numerator.-/
theorem unit_rational_frequency_eq_iff {q r : ℕ} [NeZero q] [NeZero r]
    (u : (ZMod q)ˣ) (v : (ZMod r)ˣ) :
    ZMod.toAddCircle (u : ZMod q) = ZMod.toAddCircle (v : ZMod r) ↔
      q = r ∧ (u : ZMod q).val = (v : ZMod r).val := by
  constructor
  · intro h
    have hu : Nat.Coprime (u : ZMod q).val q :=
      (ZMod.isUnit_iff_coprime _ _).mp (by simpa only [ZMod.natCast_zmod_val] using u.isUnit)
    have hv : Nat.Coprime (v : ZMod r).val r :=
      (ZMod.isUnit_iff_coprime _ _).mp (by simpa only [ZMod.natCast_zmod_val] using v.isUnit)
    rw [ZMod.toAddCircle_apply, ZMod.toAddCircle_apply] at h
    exact reduced_rational_frequency_unique _ _ q r (NeZero.pos q) (NeZero.pos r)
      (ZMod.val_lt _) (ZMod.val_lt _) hu hv h
  · rintro ⟨hqr, huv⟩
    subst r
    exact congrArg ZMod.toAddCircle (ZMod.val_injective q huv)

/-- The reduced rational frequencies with modulus at most `Q` are separated
by `1/Q²`, with modulus one included.-/
theorem unit_rational_frequency_dist_ge_inv_sq {q r : ℕ} [NeZero q] [NeZero r]
    (Q : ℕ) (hqQ : q ≤ Q) (hrQ : r ≤ Q) (u : (ZMod q)ˣ) (v : (ZMod r)ˣ)
    (hne : ¬ (q = r ∧ (u : ZMod q).val = (v : ZMod r).val)) :
    (1 : ℝ) / (Q : ℝ) ^ 2 ≤ dist (ZMod.toAddCircle (u : ZMod q)) (ZMod.toAddCircle (v : ZMod r)) := by
  have hfreq : ZMod.toAddCircle (u : ZMod q) ≠ ZMod.toAddCircle (v : ZMod r) :=
    fun h => hne ((unit_rational_frequency_eq_iff u v).mp h)
  rw [ZMod.toAddCircle_apply, ZMod.toAddCircle_apply] at hfreq ⊢
  simpa only [Int.cast_natCast] using rational_frequency_dist_ge_inv_sq ((u : ZMod q).val : ℤ)
    ((v : ZMod r).val : ℤ) q r Q (NeZero.pos q) (NeZero.pos r) hqQ hrQ
      (by simpa only [Int.cast_natCast] using hfreq)

end TwinPrime.Analytic
