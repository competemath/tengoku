module

public import Tengoku.Seed.NumberTheory.Padics.PadicIntegers
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.NNReal
import Tengoku.Seed.Data.Nat.Choose.Multinomial
import Tengoku.Seed.Tactic.ENatToNat
import Tengoku.Seed.Tactic.Measurability.Init
import Tengoku.Seed.Tactic.NormNum.Irrational
import Tengoku.Seed.Tactic.NormNum.IsCoprime
import Tengoku.Seed.Tactic.NormNum.IsSquare
import Tengoku.Seed.Tactic.NormNum.LegendreSymbol
import Tengoku.Seed.Tactic.NormNum.ModEq
import Tengoku.Seed.Tactic.NormNum.NatFib
import Tengoku.Seed.Tactic.NormNum.NatLog
import Tengoku.Seed.Tactic.NormNum.NatSqrt
import Tengoku.Seed.Tactic.NormNum.Ordinal
import Tengoku.Seed.Tactic.NormNum.Parity
import Tengoku.Seed.Tactic.NormNum.Prime
import Tengoku.Seed.Tactic.NormNum.RealSqrt
import Tengoku.Seed.Tactic.Polynomial.Basic
import Tengoku.Seed.Tactic.ReduceModChar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rational numerator bookkeeping

This file records rational-number lemmas needed by the Diekmann/Jensen route.
The results here only talk about reduced rational numerators and avoid any
extra p-adic package assumptions.
-/

@[expose] public section

namespace KummerCriterion

/-- If a rational number has real absolute value greater than `1`, then the
reduced numerator has a prime divisor.
@isnad1 id=ex.1h1v.s5.ad8dae8e150a from=translated src=- shape=4327a390 vocab=a2ed611e
-/
theorem exists_prime_dvd_num_of_one_lt_abs
    {q : ℚ} (hq : (1 : ℝ) < |(q : ℝ)|) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ q.num := by
  have hq_rat : (1 : ℚ) < |q| := by
    exact_mod_cast hq
  have hnum_gt_den_int : ((|q|).den : ℤ) < (|q|).num := by
    have hnot : ¬ (|q|).num ≤ ((|q|).den : ℤ) := fun hle =>
      (not_le_of_gt hq_rat) ((Rat.num_le_denom_iff).mp hle)
    exact lt_of_not_ge hnot
  have hden_lt_num : q.den < q.num.natAbs := by
    have hcast : (q.den : ℤ) < (q.num.natAbs : ℤ) := by
      simpa using hnum_gt_den_int
    exact_mod_cast hcast
  have hone_lt_num : 1 < q.num.natAbs :=
    lt_of_le_of_lt (Nat.succ_le_iff.mpr q.den_pos) hden_lt_num
  obtain ⟨p, hp, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (show q.num.natAbs ≠ 1 by omega)
  exact ⟨p, hp, (Int.natCast_dvd (m := p) (n := q.num)).mpr hpdvd⟩

/-- If a prime divides the reduced numerator of a rational number, then the
rational is congruent to zero modulo `p` in the `p`-adic integers.
@isnad1 id=ex.1h2v.s6.97e6e3217ad3 from=translated src=- shape=8caaeb51 vocab=9f5437c0
-/
theorem padic_eq_p_mul_of_prime_dvd_num
    {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hdiv : (p : ℤ) ∣ q.num) :
    ∃ z : ℤ_[p], (q : ℚ_[p]) = (p : ℚ_[p]) * (z : ℚ_[p]) := by
  obtain ⟨c, hc⟩ := hdiv
  have hden : ¬ p ∣ q.den := by
    intro hpden
    have hpnum : p ∣ q.num.natAbs :=
      (Int.natCast_dvd (m := p) (n := q.num)).mp ⟨c, hc⟩
    exact Nat.not_coprime_of_dvd_of_dvd (Fact.out : p.Prime).one_lt hpnum hpden q.reduced
  let r : ℚ := Rat.divInt c (q.den : ℤ)
  have hrden : ¬ p ∣ r.den := by
    intro hprd
    have hrdvd : (r.den : ℤ) ∣ (q.den : ℤ) := by
      simpa [r] using Rat.den_dvd c (q.den : ℤ)
    have hrdvd_nat : r.den ∣ q.den := Int.natCast_dvd_natCast.mp hrdvd
    exact hden (hprd.trans hrdvd_nat)
  let z : ℤ_[p] := ⟨(r : ℚ_[p]), Padic.norm_rat_le_one hrden⟩
  refine ⟨z, ?_⟩
  have hq_eq : q = (p : ℚ) * r := by
    nth_rewrite 1 [← q.num_divInt_den]
    rw [hc]
    calc
      Rat.divInt ((p : ℤ) * c) (q.den : ℤ)
          = Rat.divInt ((p : ℤ) * c) (1 * (q.den : ℤ)) := by simp
      _ = Rat.divInt (p : ℤ) 1 * Rat.divInt c (q.den : ℤ) := by
        rw [Rat.divInt_mul_divInt]
      _ = (p : ℚ) * Rat.divInt c (q.den : ℤ) := by simp
  rw [hq_eq]
  simp [z, r]

/-- If a rational number is `p` times a `p`-adic integer, then `p` divides its
reduced numerator.
@isnad1 id=dvd.1h2v.s6.e2d92645fdaa from=translated src=- shape=827a8a50 vocab=9f5437c0
-/
theorem prime_dvd_num_of_padic_eq_p_mul
    {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hzero : ∃ z : ℤ_[p], (q : ℚ_[p]) = (p : ℚ_[p]) * (z : ℚ_[p])) :
    (p : ℤ) ∣ q.num := by
  obtain ⟨z, hz⟩ := hzero
  let w : ℤ_[p] := z * (q.den : ℤ_[p])
  have hnum_eq : ((q.num : ℤ_[p]) : ℚ_[p]) = (((p : ℤ_[p]) * w : ℤ_[p]) : ℚ_[p]) := by
    have hmul : (q : ℚ_[p]) * (q.den : ℚ_[p]) = (q.num : ℚ_[p]) := by
      have hrat : q * (q.den : ℚ) = q.num := by simp
      exact_mod_cast hrat
    calc
      ((q.num : ℤ_[p]) : ℚ_[p]) = (q.num : ℚ_[p]) := rfl
      _ = (q : ℚ_[p]) * (q.den : ℚ_[p]) := hmul.symm
      _ = ((p : ℚ_[p]) * (z : ℚ_[p])) * (q.den : ℚ_[p]) := by rw [hz]
      _ = (((p : ℤ_[p]) * w : ℤ_[p]) : ℚ_[p]) := by
        simp only [w, PadicInt.coe_mul, PadicInt.coe_natCast]
        ring
  have hpadic : (p : ℤ_[p]) ∣ (q.num : ℤ_[p]) := by
    refine ⟨w, ?_⟩
    exact Subtype.ext hnum_eq
  have hnorm : ‖(q.num : ℤ_[p])‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).2 hpadic
  exact (PadicInt.norm_int_lt_one_iff_dvd (p := p) q.num).mp hnorm

/-- Transport numerator divisibility across a `p`-adic congruence.
@isnad1 id=dvd.2h3v.s7.02ddbc778058 from=translated src=- shape=801bcdf5 vocab=40769dc1
-/
theorem prime_dvd_num_of_padic_sub_eq_p_mul
    {p : ℕ} [Fact p.Prime] {q r : ℚ}
    (hdiv : (p : ℤ) ∣ q.num)
    (hcong : ∃ z : ℤ_[p],
      (q : ℚ_[p]) - (r : ℚ_[p]) = (p : ℚ_[p]) * (z : ℚ_[p])) :
    (p : ℤ) ∣ r.num := by
  obtain ⟨zq, hzq⟩ := padic_eq_p_mul_of_prime_dvd_num (p := p) (q := q) hdiv
  obtain ⟨zdiff, hzdiff⟩ := hcong
  apply prime_dvd_num_of_padic_eq_p_mul (p := p) (q := r)
  refine ⟨zq - zdiff, ?_⟩
  calc
    (r : ℚ_[p]) = (q : ℚ_[p]) - ((q : ℚ_[p]) - (r : ℚ_[p])) := by ring
    _ = (q : ℚ_[p]) - (p : ℚ_[p]) * (zdiff : ℚ_[p]) := by
      rw [hzdiff]
    _ = (p : ℚ_[p]) * (zq : ℚ_[p]) - (p : ℚ_[p]) * (zdiff : ℚ_[p]) := by
      rw [hzq]
    _ = (p : ℚ_[p]) * ((zq - zdiff : ℤ_[p]) : ℚ_[p]) := by
      push_cast
      ring

/-- For a positive natural denominator, any prime divisor of the reduced
numerator of `q / n` already divides the reduced numerator of `q`.
@isnad1 id=dvd.2h3v.s5.e8024065ba1b from=translated src=- shape=2bbed505 vocab=8f682afc
-/
theorem dvd_num_of_dvd_div_nat_num
    {p n : ℕ} {q : ℚ} (hn_pos : 0 < n)
    (hdiv : (p : ℤ) ∣ ((q / n : ℚ).num)) :
    (p : ℤ) ∣ q.num := by
  have hden_ne : ((q.den : ℕ) * n : ℤ) ≠ 0 := by
    norm_num [Rat.den_nz, hn_pos.ne']
  have hq : (q / n : ℚ) = Rat.divInt q.num ((q.den : ℕ) * n : ℤ) := by
    rw [Rat.div_def']
    simp
  have hnum_dvd : ((q / n : ℚ).num) ∣ q.num := by
    rw [hq]
    simpa using Rat.num_dvd q.num hden_ne
  exact hdiv.trans hnum_dvd

end KummerCriterion
