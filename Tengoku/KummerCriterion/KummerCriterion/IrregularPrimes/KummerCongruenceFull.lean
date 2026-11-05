module

import Tengoku.KummerCriterion.KummerCriterion.KummerCongruence.Voronoi
import Tengoku.KummerCriterion.KummerCriterion.Reflection.ResidueSymbol.DworkFactorization.FiniteLogBounds
public import Tengoku.Seed.NumberTheory.Bernoulli
public import Tengoku.Seed.NumberTheory.Padics.PadicIntegers
import Tengoku.KummerCriterion.KummerCriterion.IrregularPrimes.VonStaudtConsequences
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.NNReal
import Tengoku.Seed.Data.ZMod.Units
import Tengoku.Seed.NumberTheory.Padics.RingHoms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kummer congruence interface for the Carlitz route

The final infinitude proof needs the unrestricted Kummer congruence:

```lean
m > 0, n > 0, Even m, Even n,
m ≡ n [MOD p - 1], ¬ (p - 1) ∣ n
  ⟹ B_m / m ≡ B_n / n mod p.
```

This file proves the congruence by the elementary Voronoi route: von
Staudt-Clausen integrality controls Bernoulli denominators, the strong
Faulhaber power-sum congruence feeds a strong Voronoi congruence, and the
primitive-root comparison removes the auxiliary side conditions.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

/-! ### Basic congruence and p-unit bookkeeping -/

/-- A natural number not divisible by `p` is a unit in `ℤ_[p]`.-/
theorem padicInt_natCast_isUnit_of_not_dvd
    {p n : ℕ} [Fact p.Prime] (h : ¬ p ∣ n) :
    IsUnit ((n : ℕ) : ℤ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact hp.coprime_iff_not_dvd.mpr h

/-- Split a positive natural number into its exact `p`-power and p-prime part.-/
theorem nat_eq_primePow_factorization_mul_unitPart
    {p n : ℕ} (_hn : n ≠ 0) :
    n = p ^ n.factorization p * (n / p ^ n.factorization p) :=
  (Nat.ordProj_mul_ordCompl_eq_self n p).symm

/-- The p-prime part of a nonzero natural number is not divisible by `p`.-/
theorem prime_not_dvd_factorization_unitPart
    {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬ p ∣ n / p ^ n.factorization p :=
  hp.coprime_iff_not_dvd.mp (Nat.coprime_ordCompl hp hn)

/-- Cast the exact `p`-power decomposition of a natural number to `ℚ_[p]`.-/
theorem qpadic_natCast_eq_primePow_mul_unitPart
    {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0) :
    ((n : ℕ) : ℚ_[p]) =
      (p : ℚ_[p]) ^ n.factorization p *
        ((n / p ^ n.factorization p : ℕ) : ℚ_[p]) := by
  conv_lhs =>
    rw [nat_eq_primePow_factorization_mul_unitPart (p := p) (n := n) hn]
  push_cast
  ring

/-- Divide a natural numerator by a natural denominator after the numerator has
enough exact `p`-power to cover the denominator's `p`-part and an additional
`p^r`.  The remaining denominator is a p-adic unit.-/
theorem qpadic_natCast_div_natCast_eq_primePow_mul_of_primePow_dvd
    {p A q r : ℕ} [Fact p.Prime] (hq_pos : 0 < q)
    (hdiv : p ^ (q.factorization p + r) ∣ A) :
    ∃ z : ℤ_[p],
      ((A : ℕ) : ℚ_[p]) / ((q : ℕ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ r * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  set s : ℕ := q.factorization p with hs_def
  set u : ℕ := q / p ^ s with hu_def
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hu_not_dvd : ¬ p ∣ u := by
    rw [hu_def, hs_def]
    exact prime_not_dvd_factorization_unitPart (p := p) (n := q) hp hq_ne
  have hu_unit : IsUnit ((u : ℕ) : ℤ_[p]) :=
    padicInt_natCast_isUnit_of_not_dvd (p := p) (n := u) hu_not_dvd
  set uInv : ℤ_[p] := (hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have huInv_mul : ((u : ℕ) : ℤ_[p]) * uInv = 1 := by
    change ((hu_unit.unit * hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  have huInv_mul_Qp : ((u : ℕ) : ℚ_[p]) * ((uInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) huInv_mul
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨(c : ℤ_[p]) * uInv, ?_⟩
  have hq_cast :
      ((q : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ s * ((u : ℕ) : ℚ_[p]) := by
    rw [hs_def, hu_def]
    exact qpadic_natCast_eq_primePow_mul_unitPart (p := p) (n := q) hq_ne
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp_pow_ne : (p : ℚ_[p]) ^ s ≠ 0 := pow_ne_zero _ hpQ_ne
  rw [hc]
  push_cast
  rw [pow_add, hq_cast]
  calc
    ((p : ℚ_[p]) ^ s * (p : ℚ_[p]) ^ r * (c : ℚ_[p])) /
        ((p : ℚ_[p]) ^ s * (u : ℚ_[p]))
        = (p : ℚ_[p]) ^ r * ((c : ℚ_[p]) / (u : ℚ_[p])) := by
          field_simp [hp_pow_ne]
    _ = (p : ℚ_[p]) ^ r * ((c : ℚ_[p]) * (uInv : ℚ_[p])) := by
      rw [div_eq_mul_inv, inv_eq_of_mul_eq_one_right huInv_mul_Qp]
    _ = (p : ℚ_[p]) ^ r * (((c : ℤ_[p]) * uInv : ℤ_[p]) : ℚ_[p]) := by
      push_cast
      ring

/-! ### Basic arithmetic for the unrestricted Voronoi route -/

/-- Under the non-boundary even-index hypotheses of Kummer, an odd prime is
automatically at least `5`: the only excluded odd prime case is `p = 3`, where
`p - 1 = 2` divides every even index.-/
theorem five_le_of_odd_prime_and_even_nonboundary
    {p n : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hn_even : Even n) (hnot : ¬ (p - 1) ∣ n) :
    5 ≤ p := by
  have hp : Nat.Prime p := Fact.out
  by_contra hlt
  have hp_lt_five : p < 5 := Nat.lt_of_not_ge hlt
  have hp_ge_two : 2 ≤ p := hp.two_le
  interval_cases p <;> try contradiction
  · have htwo_dvd : 2 ∣ n := even_iff_two_dvd.mp hn_even
    exact hnot (by simpa using htwo_dvd)

/-- Numerical valuation estimate from the elementary Voronoi proof.  For
`p ≥ 5`, the combined `p`-adic contributions of consecutive denominators
`s` and `s + 1` leave at least two powers beyond the `p`-adic contribution
already present in the index `h`.-/
theorem factorization_add_succ_factorization_add_two_le
    {p s : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p) (hs : 2 ≤ s) :
    s.factorization p + (s + 1).factorization p + 2 ≤ s := by
  have hp : Nat.Prime p := Fact.out
  have hp_pred_ge_four : 4 ≤ p - 1 := by omega
  have hs_ne : s ≠ 0 := by omega
  have hs_succ_ne : s + 1 ≠ 0 := by omega
  have hfac_s :=
    Nat.factorization_mul_pred_le_pred (ell := p) (n := s) hp hs_ne
  have hfac_succ :=
    Nat.factorization_mul_pred_le_pred (ell := p) (n := s + 1) hp hs_succ_ne
  have hfac_s_four : 4 * s.factorization p ≤ s - 1 := by
    calc
      4 * s.factorization p ≤ (p - 1) * s.factorization p :=
        Nat.mul_le_mul_right _ hp_pred_ge_four
      _ = s.factorization p * (p - 1) := by rw [Nat.mul_comm]
      _ ≤ s - 1 := hfac_s
  have hfac_succ_four : 4 * (s + 1).factorization p ≤ s := by
    calc
      4 * (s + 1).factorization p ≤
          (p - 1) * (s + 1).factorization p :=
        Nat.mul_le_mul_right _ hp_pred_ge_four
      _ = (s + 1).factorization p * (p - 1) := by rw [Nat.mul_comm]
      _ ≤ (s + 1) - 1 := hfac_succ
      _ = s := by omega
  omega

/-- Binomial-strength divisibility for the higher Faulhaber terms.  The
factor `Nat.choose h s` supplies the difference between `v_p(s)` and
`v_p(h)`, while `p^(s+1)` has enough remaining p-power to absorb the
denominator `s + 1` and leave three extra powers relative to `h`.-/
theorem primePow_succFactorization_add_indexFactorization_add_three_dvd_choose_mul_primePow
    {p h s : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hs_two : 2 ≤ s) (hs_le : s ≤ h) :
    p ^ ((s + 1).factorization p + (h.factorization p + 3)) ∣
      Nat.choose h s * p ^ (s + 1) := by
  have hp : Nat.Prime p := Fact.out
  have hchoose_pos : 0 < Nat.choose h s := Nat.choose_pos hs_le
  have hchoose_ne : Nat.choose h s ≠ 0 := hchoose_pos.ne'
  have hpow_ne : p ^ (s + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hprod_ne : Nat.choose h s * p ^ (s + 1) ≠ 0 :=
    Nat.mul_ne_zero hchoose_ne hpow_ne
  have hchoose_lower :
      h.factorization p ≤ (Nat.choose h s).factorization p + s.factorization p :=
    Nat.factorization_le_factorization_choose_add (p := p) hs_le (by omega)
  have hden :=
    factorization_add_succ_factorization_add_two_le (p := p) hp_ge_five hs_two
  have htarget_le :
      (s + 1).factorization p + (h.factorization p + 3) ≤
        (Nat.choose h s).factorization p + (s + 1) := by
    omega
  refine (hp.pow_dvd_iff_le_factorization hprod_ne).mpr ?_
  calc
    (s + 1).factorization p + (h.factorization p + 3)
        ≤ (Nat.choose h s).factorization p + (s + 1) := htarget_le
    _ = (Nat.choose h s * p ^ (s + 1)).factorization p := by
      rw [Nat.factorization_mul hchoose_ne hpow_ne]
      simp [Nat.Prime.factorization_self hp]

/-- Convert a `p^(v_p(h)+3)` factor into an `h*p^3` multiple.  This is used before
multiplying by a Bernoulli number, whose denominator may contain one `p`.-/
theorem primePow_indexFactorization_add_three_mul_padicInt_eq_natCast_mul_primeCubed
    {p h : ℕ} [Fact p.Prime] (hh_pos : 0 < h) (z : ℤ_[p]) :
    ∃ w : ℤ_[p],
      (p : ℚ_[p]) ^ (h.factorization p + 3) * (z : ℚ_[p]) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 3 * (w : ℚ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  set v : ℕ := h.factorization p with hv_def
  set u : ℕ := h / p ^ v with hu_def
  have hh_ne : h ≠ 0 := hh_pos.ne'
  have hu_not_dvd : ¬ p ∣ u := by
    rw [hu_def, hv_def]
    exact prime_not_dvd_factorization_unitPart (p := p) (n := h) hp hh_ne
  have hu_unit : IsUnit ((u : ℕ) : ℤ_[p]) :=
    padicInt_natCast_isUnit_of_not_dvd (p := p) (n := u) hu_not_dvd
  set uInv : ℤ_[p] := (hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hu_mul_inv : ((u : ℕ) : ℤ_[p]) * uInv = 1 := by
    change ((hu_unit.unit * hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  have hu_mul_inv_Qp : ((u : ℕ) : ℚ_[p]) * ((uInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hu_mul_inv
  refine ⟨z * uInv, ?_⟩
  have hh_cast :
      ((h : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ v * ((u : ℕ) : ℚ_[p]) := by
    rw [hv_def, hu_def]
    exact qpadic_natCast_eq_primePow_mul_unitPart (p := p) (n := h) hh_ne
  rw [hh_cast]
  push_cast
  rw [pow_add]
  calc
    (p : ℚ_[p]) ^ v * (p : ℚ_[p]) ^ 3 * (z : ℚ_[p]) =
        (p : ℚ_[p]) ^ v * (u : ℚ_[p]) * (p : ℚ_[p]) ^ 3 *
          ((z : ℚ_[p]) * (uInv : ℚ_[p])) := by
      rw [show (p : ℚ_[p]) ^ v * (u : ℚ_[p]) * (p : ℚ_[p]) ^ 3 *
          ((z : ℚ_[p]) * (uInv : ℚ_[p])) =
          (p : ℚ_[p]) ^ v * (p : ℚ_[p]) ^ 3 * (z : ℚ_[p]) *
            ((u : ℚ_[p]) * (uInv : ℚ_[p])) by ring]
      rw [hu_mul_inv_Qp]
      ring

/-- Cubic-strength version of `binomial_divisor_term_mem_h_p_sq`, used before
the possible single `p` in a Bernoulli denominator is absorbed.-/
theorem binomial_divisor_term_mem_h_p_cubed
    {p h s : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hs_two : 2 ≤ s) (hs_le : s ≤ h) :
    ∃ z : ℤ_[p],
      (((Nat.choose h s : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p])) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 3 * (z : ℚ_[p]) := by
  have hdiv :
      p ^ ((s + 1).factorization p + (h.factorization p + 3)) ∣
        Nat.choose h s * p ^ (s + 1) :=
    primePow_succFactorization_add_indexFactorization_add_three_dvd_choose_mul_primePow
      (p := p) hp_ge_five hs_two hs_le
  obtain ⟨z, hz⟩ :=
    qpadic_natCast_div_natCast_eq_primePow_mul_of_primePow_dvd
      (p := p) (A := Nat.choose h s * p ^ (s + 1)) (q := s + 1)
      (r := h.factorization p + 3) (by omega) hdiv
  obtain ⟨w, hw⟩ :=
    primePow_indexFactorization_add_three_mul_padicInt_eq_natCast_mul_primeCubed
      (p := p) (h := h) hh_pos z
  refine ⟨w, ?_⟩
  calc
    (((Nat.choose h s : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p])) =
        (p : ℚ_[p]) ^ (h.factorization p + 3) * (z : ℚ_[p]) := by
      simpa [Nat.cast_mul, Nat.cast_pow] using hz
    _ = (h : ℚ_[p]) * (p : ℚ_[p]) ^ 3 * (w : ℚ_[p]) := hw

/-- Von Staudt denominator control in the only form needed by the strong
Faulhaber proof: `p*B_n` is always p-adically integral.-/
theorem p_mul_bernoulli_mem_padicInt
    {p n : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2) :
    ∃ z : ℤ_[p],
      (p : ℚ_[p]) * ((bernoulli n : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
  rcases Nat.even_or_odd n with hn_even | hn_odd
  · exact p_mul_bernoulli_mem_padicInt_vonStaudt (p := p) (n := n) hn_even
  · rcases eq_or_ne n 1 with rfl | hn_ne_one
    · have hp : Nat.Prime p := Fact.out
      have h2_unit : IsUnit ((2 : ℕ) : ℤ_[p]) :=
        padicInt_natCast_isUnit_of_not_dvd (p := p) (n := 2) (by
          intro h
          have hp_le_two : p ≤ 2 := Nat.le_of_dvd (by omega) h
          exact hp_odd (le_antisymm hp_le_two hp.two_le))
      set twoInv : ℤ_[p] := (h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val
      have htwo_mul_inv : ((2 : ℕ) : ℤ_[p]) * twoInv = 1 := by
        change ((h2_unit.unit * h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
        simp
      have htwo_mul_inv_Qp : (2 : ℚ_[p]) * ((twoInv : ℤ_[p]) : ℚ_[p]) = 1 := by
        exact_mod_cast congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) htwo_mul_inv
      refine ⟨-((p : ℕ) : ℤ_[p]) * twoInv, ?_⟩
      rw [bernoulli_one]
      have h2Q_ne : (2 : ℚ_[p]) ≠ 0 := by norm_num
      have h_half : ((-1 / 2 : ℚ) : ℚ_[p]) = -((twoInv : ℤ_[p]) : ℚ_[p]) :=
        mul_left_cancel₀ h2Q_ne (by push_cast; linear_combination htwo_mul_inv_Qp)
      rw [h_half]
      push_cast
      ring
    · refine ⟨0, ?_⟩
      have hn_gt : 1 < n := by
        rcases hn_odd with ⟨k, hk⟩
        omega
      rw [bernoulli_eq_zero_of_odd hn_odd hn_gt]
      simp

/-- Shifted higher Faulhaber terms with `s ≥ 2`: after multiplying by the
Bernoulli factor, the cubic coefficient bound loses at most one `p` and still
lands in `h*p^2`.-/
theorem shifted_faulhaber_term_mem_h_p_sq_of_two_le
    {p h s : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hs_two : 2 ≤ s) (hs_le : s ≤ h) :
    ∃ z : ℤ_[p],
      ((bernoulli (h - s) : ℚ) : ℚ_[p]) *
          ((((Nat.choose h s : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p]))) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  have hp_odd : p ≠ 2 := by omega
  obtain ⟨c, hc⟩ :=
    binomial_divisor_term_mem_h_p_cubed (p := p) hp_ge_five hh_pos hs_two hs_le
  obtain ⟨b, hb⟩ := p_mul_bernoulli_mem_padicInt (p := p) (n := h - s) hp_odd
  refine ⟨b * c, ?_⟩
  rw [hc]
  push_cast
  linear_combination ((h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (c : ℚ_[p])) * hb

/-- The exceptional shifted term `s = 1` in the strong Faulhaber proof.  For
`h > 2` it vanishes by odd Bernoulli zeroes; for `h = 2`, the denominator `4`
is a p-adic unit because `p ≥ 5`.-/
theorem shifted_faulhaber_one_term_mem_h_p_sq
    {p h : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hh_even : Even h) :
    ∃ z : ℤ_[p],
      ((bernoulli (h - 1) : ℚ) : ℚ_[p]) *
          ((((Nat.choose h 1 : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ 2) / ((2 : ℕ) : ℚ_[p]))) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  rcases eq_or_ne h 2 with rfl | hh_ne_two
  · have h4_unit : IsUnit ((4 : ℕ) : ℤ_[p]) :=
      padicInt_natCast_isUnit_of_not_dvd (p := p) (n := 4) (by
        intro hdiv
        have hp_le_four : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
        omega)
    set fourInv : ℤ_[p] := (h4_unit.unit⁻¹ : (ℤ_[p])ˣ).val
    have hfour_mul_inv : ((4 : ℕ) : ℤ_[p]) * fourInv = 1 := by
      change ((h4_unit.unit * h4_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
      simp
    have hfour_mul_inv_Qp : (4 : ℚ_[p]) * ((fourInv : ℤ_[p]) : ℚ_[p]) = 1 := by
      exact_mod_cast congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hfour_mul_inv
    refine ⟨-fourInv, ?_⟩
    rw [bernoulli_one, Nat.choose_one_right]
    push_cast
    have h : ((fourInv : ℤ_[p]) : ℚ_[p]) = (4 : ℚ_[p])⁻¹ :=
      (inv_eq_of_mul_eq_one_right hfour_mul_inv_Qp).symm
    rw [h]
    field_simp
    ring
  · refine ⟨0, ?_⟩
    rcases hh_even with ⟨m, hm⟩
    have hm_ge_two : 2 ≤ m := by
      by_contra hlt
      have hm_lt_two : m < 2 := Nat.lt_of_not_ge hlt
      interval_cases m <;> omega
    have h_odd : Odd (h - 1) := by
      refine ⟨m - 1, ?_⟩
      omega
    have h_gt : 1 < h - 1 := by omega
    rw [bernoulli_eq_zero_of_odd h_odd h_gt]
    push_cast
    ring

/-- Algebraic binomial reindexing used to pass from mathlib's Faulhaber
summand indexed by `i` to the TeX summand indexed by `s = h - i`.-/
theorem choose_succ_div_eq_choose_div
    {p h s : ℕ} [Fact p.Prime] (hs : s ≤ h) :
    ((Nat.choose (h + 1) (h - s) : ℕ) : ℚ_[p]) / ((h + 1 : ℕ) : ℚ_[p]) =
      ((Nat.choose h s : ℕ) : ℚ_[p]) / ((s + 1 : ℕ) : ℚ_[p]) := by
  have hsym : Nat.choose (h + 1) (h - s) = Nat.choose (h + 1) (s + 1) := by
    have hs1 : s + 1 ≤ h + 1 := by omega
    have := Nat.choose_symm (n := h + 1) (k := s + 1) hs1
    simpa [Nat.add_sub_cancel_right, Nat.add_sub_assoc hs] using this
  have hmul_nat :
      (h + 1) * Nat.choose h s = Nat.choose (h + 1) (s + 1) * (s + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.add_one_mul_choose_eq h s
  have hmul :
      ((h + 1 : ℕ) : ℚ_[p]) * ((Nat.choose h s : ℕ) : ℚ_[p]) =
        ((Nat.choose (h + 1) (s + 1) : ℕ) : ℚ_[p]) *
          ((s + 1 : ℕ) : ℚ_[p]) := by
    exact_mod_cast hmul_nat
  have hh_ne : ((h + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs_ne : ((s + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hsym]
  field_simp [hh_ne, hs_ne]
  rw [hmul]

/-- Each non-leading Faulhaber summand is an `h*p^2` multiple, after
reindexing `i < h` as `s = h - i`.-/
theorem faulhaber_remainder_term_mem_h_p_sq
    {p h i : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hh_even : Even h) (hi : i < h) :
    ∃ z : ℤ_[p],
      ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (h + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (h + 1 - i)) / ((h + 1 : ℕ) : ℚ_[p]) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  set s : ℕ := h - i with hs_def
  have hs_pos : 0 < s := by omega
  have hs_le : s ≤ h := by omega
  have hi_eq : i = h - s := by omega
  have hexp_hs : h + 1 - (h - s) = s + 1 := by omega
  have hcoef :
      ((Nat.choose (h + 1) (h - s) : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((h + 1 : ℕ) : ℚ_[p]) =
        ((Nat.choose h s : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p]) := by
    have hchoose := choose_succ_div_eq_choose_div (p := p) (h := h) (s := s) hs_le
    calc
      ((Nat.choose (h + 1) (h - s) : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((h + 1 : ℕ) : ℚ_[p]) =
          (((Nat.choose (h + 1) (h - s) : ℕ) : ℚ_[p]) /
              ((h + 1 : ℕ) : ℚ_[p])) * ((p : ℚ_[p]) ^ (s + 1)) := by ring
      _ = (((Nat.choose h s : ℕ) : ℚ_[p]) / ((s + 1 : ℕ) : ℚ_[p])) *
            ((p : ℚ_[p]) ^ (s + 1)) := by rw [hchoose]
      _ = ((Nat.choose h s : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p]) := by ring
  by_cases hs_one : s = 1
  · obtain ⟨z, hz⟩ := shifted_faulhaber_one_term_mem_h_p_sq
      (p := p) (h := h) hp_ge_five hh_pos hh_even
    refine ⟨z, ?_⟩
    calc
      ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (h + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (h + 1 - i)) / ((h + 1 : ℕ) : ℚ_[p]) =
        ((bernoulli (h - s) : ℚ) : ℚ_[p]) *
          (((Nat.choose (h + 1) (h - s) : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ (s + 1)) / ((h + 1 : ℕ) : ℚ_[p])) := by
          rw [hi_eq, hexp_hs]
          ring
      _ = ((bernoulli (h - s) : ℚ) : ℚ_[p]) *
          (((Nat.choose h s : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p])) := by
          rw [hcoef]
      _ = (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
          rw [hs_one]
          simpa using hz
  · have hs_two : 2 ≤ s := by omega
    obtain ⟨z, hz⟩ := shifted_faulhaber_term_mem_h_p_sq_of_two_le
      (p := p) (h := h) (s := s) hp_ge_five hh_pos hs_two hs_le
    refine ⟨z, ?_⟩
    calc
      ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (h + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (h + 1 - i)) / ((h + 1 : ℕ) : ℚ_[p]) =
        ((bernoulli (h - s) : ℚ) : ℚ_[p]) *
          (((Nat.choose (h + 1) (h - s) : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ (s + 1)) / ((h + 1 : ℕ) : ℚ_[p])) := by
          rw [hi_eq, hexp_hs]
          ring
      _ = ((bernoulli (h - s) : ℚ) : ℚ_[p]) *
          (((Nat.choose h s : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p])) := by
          rw [hcoef]
      _ = (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := hz

/-- Sum of all non-leading Faulhaber summands.-/
theorem faulhaber_remainder_sum_mem_h_p_sq
    {p h : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hh_even : Even h) :
    ∃ W : ℤ_[p],
      (∑ i ∈ Finset.range h,
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (h + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (h + 1 - i)) / ((h + 1 : ℕ) : ℚ_[p])) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W : ℚ_[p]) := by
  choose w hw using (fun (i : ℕ) (hi : i < h) =>
    faulhaber_remainder_term_mem_h_p_sq (p := p) (h := h) (i := i)
      hp_ge_five hh_pos hh_even hi)
  set W : ℤ_[p] := ∑ i ∈ Finset.attach (Finset.range h),
    w i.1 (Finset.mem_range.mp i.2) with hW_def
  refine ⟨W, ?_⟩
  rw [← Finset.sum_attach]
  rw [show ((h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W : ℚ_[p])) =
      ∑ i ∈ Finset.attach (Finset.range h),
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 *
          ((w i.1 (Finset.mem_range.mp i.2) : ℤ_[p]) : ℚ_[p]) from ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact hw i.1 (Finset.mem_range.mp i.2)
  · rw [hW_def]
    simp [PadicInt.coe_sum, Finset.mul_sum]

/-- Strong Faulhaber power-sum congruence from the TeX proof: the usual
`S_h(p) - p*B_h` difference carries the stronger modulus `h*p^2`.-/
theorem sum_range_pow_sub_p_mul_bernoulli_strong
    {p h : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hh_even : Even h)
    (_hnot : ¬ (p - 1) ∣ h) :
    ∃ z : ℤ_[p],
      ((∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ h)) -
          (p : ℚ_[p]) * ((bernoulli h : ℚ) : ℚ_[p]) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  obtain ⟨W, hW⟩ := faulhaber_remainder_sum_mem_h_p_sq
    (p := p) (h := h) hp_ge_five hh_pos hh_even
  refine ⟨W, ?_⟩
  have h_faulhaber_Q : (∑ k ∈ Finset.range p, (k : ℚ) ^ h) =
      ∑ i ∈ Finset.range (h + 1),
        bernoulli i * ((Nat.choose (h + 1) i : ℕ) : ℚ) *
          (p : ℚ) ^ (h + 1 - i) / (h + 1 : ℚ) := by
    rw [sum_range_pow p h]
  have h_faulhaber_Qp : (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ h) =
      ∑ i ∈ Finset.range (h + 1),
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (h + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (h + 1 - i)) / ((h + 1 : ℕ) : ℚ_[p]) := by
    have := congrArg (fun q : ℚ => (q : ℚ_[p])) h_faulhaber_Q
    push_cast at this
    push_cast
    exact this
  have hterm_h :
      ((bernoulli h : ℚ) : ℚ_[p]) * ((Nat.choose (h + 1) h : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (h + 1 - h)) / ((h + 1 : ℕ) : ℚ_[p]) =
        (p : ℚ_[p]) * ((bernoulli h : ℚ) : ℚ_[p]) := by
    have hhp1_ne : ((h + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.choose_succ_self_right h, show h + 1 - h = 1 by omega]
    push_cast
    field_simp [hhp1_ne]
  have h_split :
      (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ h) -
          (p : ℚ_[p]) * ((bernoulli h : ℚ) : ℚ_[p]) =
        ∑ i ∈ Finset.range h,
          ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (h + 1) i : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ (h + 1 - i)) / ((h + 1 : ℕ) : ℚ_[p]) := by
    rw [h_faulhaber_Qp, Finset.sum_range_succ, hterm_h]
    ring
  rw [h_split]
  exact hW

/-! ### Strong Voronoi binomial expansion bookkeeping -/

/-- For `p ≥ 5`, every `ν ≥ 2` carries enough p-power to leave two powers
after removing the exact p-part of `ν`.-/
theorem factorization_add_two_le_self
    {p nu : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p) (hnu_two : 2 ≤ nu) :
    nu.factorization p + 2 ≤ nu := by
  have hp : Nat.Prime p := Fact.out
  have hp_pred_ge_four : 4 ≤ p - 1 := by omega
  have hnu_ne : nu ≠ 0 := by omega
  have hfac := Nat.factorization_mul_pred_le_pred (ell := p) (n := nu) hp hnu_ne
  have hfac_four : 4 * nu.factorization p ≤ nu - 1 := by
    calc
      4 * nu.factorization p ≤ (p - 1) * nu.factorization p :=
        Nat.mul_le_mul_right _ hp_pred_ge_four
      _ = nu.factorization p * (p - 1) := by rw [Nat.mul_comm]
      _ ≤ nu - 1 := hfac
  omega

/-- The high-order Voronoi binomial coefficient `choose h ν * p^ν`, with
`ν ≥ 2`, is divisible by the p-part of `h` and two more powers of `p`.-/
theorem primePow_indexFactorization_add_two_dvd_choose_mul_primePow
    {p h nu : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hnu_two : 2 ≤ nu) (hnu_le : nu ≤ h) :
    p ^ (h.factorization p + 2) ∣ Nat.choose h nu * p ^ nu := by
  have hp : Nat.Prime p := Fact.out
  have hchoose_pos : 0 < Nat.choose h nu := Nat.choose_pos hnu_le
  have hchoose_ne : Nat.choose h nu ≠ 0 := hchoose_pos.ne'
  have hpow_ne : p ^ nu ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hprod_ne : Nat.choose h nu * p ^ nu ≠ 0 :=
    Nat.mul_ne_zero hchoose_ne hpow_ne
  have hchoose_lower :
      h.factorization p ≤ (Nat.choose h nu).factorization p + nu.factorization p :=
    Nat.factorization_le_factorization_choose_add (p := p) hnu_le (by omega)
  have hnu_fac : nu.factorization p + 2 ≤ nu :=
    factorization_add_two_le_self (p := p) hp_ge_five hnu_two
  have htarget_le : h.factorization p + 2 ≤ (Nat.choose h nu).factorization p + nu := by
    omega
  refine (hp.pow_dvd_iff_le_factorization hprod_ne).mpr ?_
  calc
    h.factorization p + 2 ≤ (Nat.choose h nu).factorization p + nu := htarget_le
    _ = (Nat.choose h nu * p ^ nu).factorization p := by
      rw [Nat.factorization_mul hchoose_ne hpow_ne]
      simp [Nat.Prime.factorization_self hp]

/-- Convert a `p^(v_p(h)+2)` multiple into the strong Voronoi modulus
`h*p^2`.-/
theorem primePow_indexFactorization_add_two_mul_padicInt_eq_natCast_mul_primeSq
    {p h : ℕ} [Fact p.Prime] (hh_pos : 0 < h) (z : ℤ_[p]) :
    ∃ w : ℤ_[p],
      (p : ℚ_[p]) ^ (h.factorization p + 2) * (z : ℚ_[p]) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (w : ℚ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  set v : ℕ := h.factorization p with hv_def
  set u : ℕ := h / p ^ v with hu_def
  have hh_ne : h ≠ 0 := hh_pos.ne'
  have hu_not_dvd : ¬ p ∣ u := by
    rw [hu_def, hv_def]
    exact prime_not_dvd_factorization_unitPart (p := p) (n := h) hp hh_ne
  have hu_unit : IsUnit ((u : ℕ) : ℤ_[p]) :=
    padicInt_natCast_isUnit_of_not_dvd (p := p) (n := u) hu_not_dvd
  set uInv : ℤ_[p] := (hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hu_mul_inv : ((u : ℕ) : ℤ_[p]) * uInv = 1 := by
    change ((hu_unit.unit * hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  have hu_mul_inv_Qp : ((u : ℕ) : ℚ_[p]) * ((uInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hu_mul_inv
  refine ⟨z * uInv, ?_⟩
  have hh_cast :
      ((h : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ v * ((u : ℕ) : ℚ_[p]) := by
    rw [hv_def, hu_def]
    exact qpadic_natCast_eq_primePow_mul_unitPart (p := p) (n := h) hh_ne
  rw [hh_cast]
  push_cast
  rw [pow_add]
  calc
    (p : ℚ_[p]) ^ v * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) =
        (p : ℚ_[p]) ^ v * (u : ℚ_[p]) * (p : ℚ_[p]) ^ 2 *
          ((z : ℚ_[p]) * (uInv : ℚ_[p])) := by
      rw [show (p : ℚ_[p]) ^ v * (u : ℚ_[p]) * (p : ℚ_[p]) ^ 2 *
          ((z : ℚ_[p]) * (uInv : ℚ_[p])) =
          (p : ℚ_[p]) ^ v * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) *
            ((u : ℚ_[p]) * (uInv : ℚ_[p])) by ring]
      rw [hu_mul_inv_Qp]
      ring

/-- P-adic form of
`primePow_indexFactorization_add_two_dvd_choose_mul_primePow`.-/
theorem choose_mul_primePow_mem_h_p_sq
    {p h nu : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hnu_two : 2 ≤ nu) (hnu_le : nu ≤ h) :
    ∃ z : ℤ_[p],
      ((Nat.choose h nu : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ nu =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  have hdiv : p ^ (h.factorization p + 2) ∣ Nat.choose h nu * p ^ nu :=
    primePow_indexFactorization_add_two_dvd_choose_mul_primePow
      (p := p) hp_ge_five hnu_two hnu_le
  obtain ⟨z, hz⟩ :=
    qpadic_natCast_div_natCast_eq_primePow_mul_of_primePow_dvd
      (p := p) (A := Nat.choose h nu * p ^ nu) (q := 1)
      (r := h.factorization p + 2) (by omega) (by simpa using hdiv)
  obtain ⟨w, hw⟩ :=
    primePow_indexFactorization_add_two_mul_padicInt_eq_natCast_mul_primeSq
      (p := p) (h := h) hh_pos z
  refine ⟨w, ?_⟩
  calc
    ((Nat.choose h nu : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ nu =
        (p : ℚ_[p]) ^ (h.factorization p + 2) * (z : ℚ_[p]) := by
      simpa [Nat.cast_mul, Nat.cast_pow] using hz
    _ = (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (w : ℚ_[p]) := hw

/-- A high-order binomial term in `(X - p*Y)^h`, with order `ν ≥ 2`, is a
multiple of `h*p^2`.-/
theorem binomial_high_term_mem_h_p_sq
    {p h nu X Y : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hnu_two : 2 ≤ nu) (hnu_le : nu ≤ h) :
    ∃ z : ℤ_[p],
      ((X : ℚ_[p]) ^ (h - nu)) * (-(p : ℚ_[p]) * (Y : ℚ_[p])) ^ nu *
          ((Nat.choose h (h - nu) : ℕ) : ℚ_[p]) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  obtain ⟨c, hc⟩ := choose_mul_primePow_mem_h_p_sq
    (p := p) (h := h) (nu := nu) hp_ge_five hh_pos hnu_two hnu_le
  refine ⟨((X : ℕ) : ℤ_[p]) ^ (h - nu) * ((-1 : ℤ_[p]) ^ nu) *
    ((Y : ℕ) : ℤ_[p]) ^ nu * c, ?_⟩
  have hchoose : Nat.choose h (h - nu) = Nat.choose h nu :=
    Nat.choose_symm hnu_le
  rw [hchoose]
  push_cast
  linear_combination
    ((X : ℚ_[p]) ^ (h - nu) * (-1 : ℚ_[p]) ^ nu * (Y : ℚ_[p]) ^ nu) * hc

/-- Pointwise strong Voronoi binomial approximation for one residue.-/
theorem voronoi_term_mod_h_p_sq
    {p a h j : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p) (hh_pos : 0 < h) :
    ∃ z : ℤ_[p],
      ((((j * a) % p : ℕ) : ℚ_[p]) ^ h) =
        ((j * a : ℕ) : ℚ_[p]) ^ h -
          (h : ℚ_[p]) * ((j * a : ℕ) : ℚ_[p]) ^ (h - 1) * (p : ℚ_[p]) *
            (((j * a / p : ℕ)) : ℚ_[p]) +
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  set X : ℕ := j * a with hX_def
  set Y : ℕ := j * a / p with hY_def
  have h_div_mod :
      ((X : ℕ) : ℚ_[p]) =
        (Y : ℚ_[p]) * (p : ℚ_[p]) + (((j * a) % p : ℕ) : ℚ_[p]) := by
    rw [hX_def, hY_def]
    rw [show ((j * a : ℕ) : ℚ_[p]) =
        (((j * a / p) * p + (j * a) % p : ℕ) : ℚ_[p]) from by
      rw [← (Nat.div_add_mod' _ _).symm]]
    push_cast
    ring
  have h_r :
      (((j * a) % p : ℕ) : ℚ_[p]) =
        (X : ℚ_[p]) - (p : ℚ_[p]) * (Y : ℚ_[p]) := by
    linear_combination -h_div_mod
  rcases eq_or_ne h 1 with rfl | hh_ne_one
  · refine ⟨0, ?_⟩
    rw [h_r]
    push_cast
    ring
  · have hh_two : 2 ≤ h := by omega
    choose w hw using (fun (m : ℕ) (hm : m < h - 1) =>
      binomial_high_term_mem_h_p_sq (p := p) (h := h) (nu := h - m)
        (X := X) (Y := Y) hp_ge_five hh_pos (by omega) (by omega))
    set W : ℤ_[p] := ∑ m ∈ Finset.attach (Finset.range (h - 1)),
      w m.1 (Finset.mem_range.mp m.2) with hW_def
    refine ⟨W, ?_⟩
    have h_tail :
        (∑ m ∈ Finset.range (h - 1),
          (X : ℚ_[p]) ^ m * (-(p : ℚ_[p]) * (Y : ℚ_[p])) ^ (h - m) *
            ((Nat.choose h m : ℕ) : ℚ_[p])) =
          (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W : ℚ_[p]) := by
      rw [← Finset.sum_attach]
      rw [show ((h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W : ℚ_[p])) =
          ∑ m ∈ Finset.attach (Finset.range (h - 1)),
            (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 *
              ((w m.1 (Finset.mem_range.mp m.2) : ℤ_[p]) : ℚ_[p]) from ?_]
      · refine Finset.sum_congr rfl fun m _ => ?_
        have hm_lt : m.1 < h - 1 := Finset.mem_range.mp m.2
        have hm_le : m.1 ≤ h := by omega
        have hhm : h - (h - m.1) = m.1 := Nat.sub_sub_self hm_le
        have hwm := hw m.1 hm_lt
        simpa [hhm] using hwm
      · rw [hW_def]
        simp [PadicInt.coe_sum, Finset.mul_sum]
    let term : ℕ → ℚ_[p] := fun m =>
      (X : ℚ_[p]) ^ m * (-(p : ℚ_[p]) * (Y : ℚ_[p])) ^ (h - m) *
        ((Nat.choose h m : ℕ) : ℚ_[p])
    have hsplit_range : (∑ m ∈ Finset.range h, term m) =
        (∑ m ∈ Finset.range (h - 1), term m) + term (h - 1) := by
      simpa [term, show h - 1 + 1 = h by omega] using Finset.sum_range_succ term (h - 1)
    rw [h_r]
    rw [show (X : ℚ_[p]) - (p : ℚ_[p]) * (Y : ℚ_[p]) =
        (X : ℚ_[p]) + (-(p : ℚ_[p]) * (Y : ℚ_[p])) by ring]
    rw [add_pow]
    change (∑ m ∈ Finset.range (h + 1), term m) =
      ((X : ℚ_[p]) ^ h -
          (h : ℚ_[p]) * (X : ℚ_[p]) ^ (h - 1) * (p : ℚ_[p]) * (Y : ℚ_[p]) +
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W : ℚ_[p]))
    rw [Finset.sum_range_succ, hsplit_range]
    change (∑ m ∈ Finset.range (h - 1),
          (X : ℚ_[p]) ^ m * (-(p : ℚ_[p]) * (Y : ℚ_[p])) ^ (h - m) *
            ((Nat.choose h m : ℕ) : ℚ_[p])) +
        ((X : ℚ_[p]) ^ (h - 1) * (-(p : ℚ_[p]) * (Y : ℚ_[p])) ^ (h - (h - 1)) *
            ((Nat.choose h (h - 1) : ℕ) : ℚ_[p])) +
        ((X : ℚ_[p]) ^ h * (-(p : ℚ_[p]) * (Y : ℚ_[p])) ^ (h - h) *
            ((Nat.choose h h : ℕ) : ℚ_[p])) = _
    rw [h_tail]
    rw [show h - (h - 1) = 1 by omega, show h - h = 0 by omega]
    rw [show Nat.choose h (h - 1) = h by
      rw [show h = (h - 1) + 1 by omega]
      exact Nat.choose_succ_self_right (h - 1)]
    rw [Nat.choose_self]
    push_cast
    ring

/-- Strong Voronoi binomial/permutation identity with modulus `h*p^2`.  This
is the side-condition-free replacement for the old `p^2` identity in the
Voronoi route.-/
theorem voronoi_sum_mod_h_p_sq
    {p a h : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (ha_coprime : ¬ p ∣ a) (hh_pos : 0 < h) :
    ∃ W : ℤ_[p],
      ((a : ℚ_[p]) ^ h - 1) * (∑ x ∈ Finset.range p, (x : ℚ_[p]) ^ h) -
        (h : ℚ_[p]) * (p : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) *
          (∑ x ∈ Finset.range p,
            (x : ℚ_[p]) ^ (h - 1) * ((x * a / p : ℕ) : ℚ_[p])) =
      (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W : ℚ_[p]) := by
  choose w hw using (fun (j : ℕ) (_hj : j ∈ Finset.range p) =>
    voronoi_term_mod_h_p_sq (p := p) (a := a) (h := h) (j := j) hp_ge_five hh_pos)
  set wt : ℕ → ℤ_[p] := fun j => if hj : j ∈ Finset.range p then w j hj else 0
    with hwt_def
  have hwt_eq : ∀ (j : ℕ) (hj : j ∈ Finset.range p), wt j = w j hj := by
    intro j hj
    rw [hwt_def]
    simp [hj]
  set W_sum : ℤ_[p] := ∑ j ∈ Finset.range p, wt j with hW_sum_def
  refine ⟨-W_sum, ?_⟩
  set S1 : ℚ_[p] := ∑ x ∈ Finset.range p, (x : ℚ_[p]) ^ h with hS1_def
  set S2 : ℚ_[p] := ∑ x ∈ Finset.range p,
    (x : ℚ_[p]) ^ (h - 1) * ((x * a / p : ℕ) : ℚ_[p]) with hS2_def
  have h_perm :
      (∑ j ∈ Finset.range p, (((j * a) % p : ℕ) : ℚ_[p]) ^ h) = S1 := by
    rw [hS1_def]
    exact voronoi_permutation ha_coprime (fun n : ℕ => (n : ℚ_[p]) ^ h)
  have h_sum_binom :
      (∑ j ∈ Finset.range p, (((j * a) % p : ℕ) : ℚ_[p]) ^ h) =
        ∑ j ∈ Finset.range p,
          (((j * a : ℕ) : ℚ_[p]) ^ h -
            (h : ℚ_[p]) * ((j * a : ℕ) : ℚ_[p]) ^ (h - 1) * (p : ℚ_[p]) *
              (((j * a / p : ℕ)) : ℚ_[p]) +
            (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (wt j : ℚ_[p])) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hwt_eq j hj]
    exact hw j hj
  have h_sum : S1 =
        ∑ j ∈ Finset.range p,
          (((j * a : ℕ) : ℚ_[p]) ^ h -
            (h : ℚ_[p]) * ((j * a : ℕ) : ℚ_[p]) ^ (h - 1) * (p : ℚ_[p]) *
              (((j * a / p : ℕ)) : ℚ_[p]) +
            (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (wt j : ℚ_[p])) := by
    rw [← h_perm, h_sum_binom]
  have h_ja_pow : ∀ j : ℕ, ((j * a : ℕ) : ℚ_[p]) ^ h =
      (a : ℚ_[p]) ^ h * (j : ℚ_[p]) ^ h := by
    intro j
    push_cast
    ring
  have h_ja_pow_sub1 : ∀ j : ℕ, ((j * a : ℕ) : ℚ_[p]) ^ (h - 1) =
      (a : ℚ_[p]) ^ (h - 1) * (j : ℚ_[p]) ^ (h - 1) := by
    intro j
    push_cast
    ring
  have h_sum_rewrite :
        ∑ j ∈ Finset.range p,
          (((j * a : ℕ) : ℚ_[p]) ^ h -
            (h : ℚ_[p]) * ((j * a : ℕ) : ℚ_[p]) ^ (h - 1) * (p : ℚ_[p]) *
              (((j * a / p : ℕ)) : ℚ_[p]) +
            (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (wt j : ℚ_[p])) =
        ∑ j ∈ Finset.range p,
          ((a : ℚ_[p]) ^ h * (j : ℚ_[p]) ^ h -
            (h : ℚ_[p]) * (p : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) *
              ((j : ℚ_[p]) ^ (h - 1) * (((j * a / p : ℕ)) : ℚ_[p])) +
            (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (wt j : ℚ_[p])) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h_ja_pow j, h_ja_pow_sub1 j]
    ring
  rw [h_sum_rewrite] at h_sum
  have h_three :
        ∑ j ∈ Finset.range p,
          ((a : ℚ_[p]) ^ h * (j : ℚ_[p]) ^ h -
            (h : ℚ_[p]) * (p : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) *
              ((j : ℚ_[p]) ^ (h - 1) * (((j * a / p : ℕ)) : ℚ_[p])) +
            (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (wt j : ℚ_[p])) =
        (a : ℚ_[p]) ^ h * S1 -
          (h : ℚ_[p]) * (p : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) * S2 +
          (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W_sum : ℚ_[p]) := by
    simp [hS1_def, hS2_def, hW_sum_def, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.mul_sum, PadicInt.coe_sum]
  rw [h_three] at h_sum
  rw [hS1_def, hS2_def]
  push_cast
  linear_combination -h_sum

/-- Side-condition-free Voronoi congruence modulo `p`, obtained by
substituting the strong Faulhaber congruence into `voronoi_sum_mod_h_p_sq`
and cancelling the nonzero rational factor `h*p` in `ℚ_[p]`.-/
theorem voronoi_congruence_mod_p_strong
    {p a h : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (ha_coprime : ¬ p ∣ a)
    (hh_pos : 0 < h) (hh_even : Even h)
    (hnot : ¬ (p - 1) ∣ h) :
    ∃ z : ℤ_[p],
      ((a : ℚ_[p]) ^ h - 1) *
          (((bernoulli h : ℚ) / (h : ℕ) : ℚ) : ℚ_[p]) -
        (a : ℚ_[p]) ^ (h - 1) *
          (∑ x ∈ Finset.range p,
            (x : ℚ_[p]) ^ (h - 1) * ((x * a / p : ℕ) : ℚ_[p])) =
      (p : ℚ_[p]) * (z : ℚ_[p]) := by
  obtain ⟨Wv, hWv⟩ := voronoi_sum_mod_h_p_sq (p := p) (a := a) (h := h)
    hp_ge_five ha_coprime hh_pos
  obtain ⟨Wf, hWf⟩ := sum_range_pow_sub_p_mul_bernoulli_strong
    (p := p) (h := h) hp_ge_five hh_pos hh_even hnot
  set S : ℚ_[p] := ∑ x ∈ Finset.range p, (x : ℚ_[p]) ^ h with hS_def
  set Q : ℚ_[p] := ∑ x ∈ Finset.range p,
    (x : ℚ_[p]) ^ (h - 1) * ((x * a / p : ℕ) : ℚ_[p]) with hQ_def
  set B : ℚ_[p] := ((bernoulli h : ℚ) : ℚ_[p]) with hB_def
  have hWv' : ((a : ℚ_[p]) ^ h - 1) * S -
        (h : ℚ_[p]) * (p : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) * Q =
      (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (Wv : ℚ_[p]) := by
    simpa [hS_def, hQ_def] using hWv
  have hWf' : S - (p : ℚ_[p]) * B =
      (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (Wf : ℚ_[p]) := by
    simpa [hS_def, hB_def] using hWf
  have hp_ne : (p : ℚ_[p]) ≠ 0 := by
    have hp : Nat.Prime p := Fact.out
    exact_mod_cast hp.ne_zero
  have hh_ne : (h : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hh_pos.ne'
  refine ⟨Wv - ((a : ℤ_[p]) ^ h - 1) * Wf, ?_⟩
  have hp_mul_hmain : (p : ℚ_[p]) *
      (((a : ℚ_[p]) ^ h - 1) * B -
        (h : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) * Q) =
      (p : ℚ_[p]) * ((h : ℚ_[p]) * (p : ℚ_[p]) *
        (((Wv : ℤ_[p]) : ℚ_[p]) - (((a : ℚ_[p]) ^ h - 1) * (Wf : ℚ_[p])))) := by
    linear_combination hWv' - ((a : ℚ_[p]) ^ h - 1) * hWf'
  have hmain : ((a : ℚ_[p]) ^ h - 1) * B -
      (h : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) * Q =
      (h : ℚ_[p]) * (p : ℚ_[p]) *
        (((Wv : ℤ_[p]) : ℚ_[p]) - (((a : ℚ_[p]) ^ h - 1) * (Wf : ℚ_[p]))) :=
    mul_left_cancel₀ hp_ne hp_mul_hmain
  have hdivB : (((bernoulli h : ℚ) / (h : ℕ) : ℚ) : ℚ_[p]) =
      B / (h : ℚ_[p]) := by
    rw [hB_def]
    push_cast
    rfl
  have htarget_mul : (h : ℚ_[p]) *
      (((a : ℚ_[p]) ^ h - 1) * (B / (h : ℚ_[p])) -
        (a : ℚ_[p]) ^ (h - 1) * Q) =
      (h : ℚ_[p]) * ((p : ℚ_[p]) *
        (((Wv : ℤ_[p]) : ℚ_[p]) - (((a : ℚ_[p]) ^ h - 1) * (Wf : ℚ_[p])))) := by
    field_simp [hh_ne]
    linear_combination hmain
  have htarget := mul_left_cancel₀ hh_ne htarget_mul
  rw [hQ_def, hdivB]
  push_cast
  exact htarget

/-- Powers of a chosen unit generator only depend on the exponent modulo
`p - 1`, once the generator order has been identified with `p - 1`.-/
theorem primitiveRoot_unit_pow_eq_of_modEq
    {p m n : ℕ} [Fact p.Prime] {g : (ZMod p)ˣ}
    (hg_order : orderOf g = p - 1)
    (hmn : m ≡ n [MOD p - 1]) :
    g ^ m = g ^ n := by
  rw [pow_eq_pow_iff_modEq, hg_order]
  exact hmn

/-- If two predecessor exponents are congruent modulo `p - 1`, the Voronoi
floor sums differ by a multiple of `p` in `ℚ_[p]`.-/
theorem voronoi_floor_sum_sModEq_of_pred_modEq
    {p a m n : ℕ} [Fact p.Prime]
    (_hm_pos : 0 < m) (_hn_pos : 0 < n)
    (hmn : (m - 1) ≡ (n - 1) [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (∑ x ∈ Finset.range p,
        (x : ℚ_[p]) ^ (m - 1) * ((x * a / p : ℕ) : ℚ_[p])) -
      (∑ x ∈ Finset.range p,
        (x : ℚ_[p]) ^ (n - 1) * ((x * a / p : ℕ) : ℚ_[p])) =
      (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  set SmZ : ℤ_[p] := ∑ x ∈ Finset.range p,
    ((x : ℕ) : ℤ_[p]) ^ (m - 1) * (((x * a / p : ℕ) : ℤ_[p])) with hSmZ_def
  set SnZ : ℤ_[p] := ∑ x ∈ Finset.range p,
    ((x : ℕ) : ℤ_[p]) ^ (n - 1) * (((x * a / p : ℕ) : ℤ_[p])) with hSnZ_def
  have h_pow_pred_ZMod : ∀ j : ℕ, j < p → j ≠ 0 →
      ((j : ℕ) : ZMod p) ^ (m - 1) = ((j : ℕ) : ZMod p) ^ (n - 1) := by
    intro j hjp hj_ne
    have hj_coprime : Nat.Coprime j p :=
      (hp.coprime_iff_not_dvd.mpr
        (fun hdvd => hj_ne (Nat.eq_zero_of_dvd_of_lt hdvd hjp))).symm
    lift (((j : ℕ) : ZMod p)) to (ZMod p)ˣ using
      (ZMod.isUnit_iff_coprime j p).mpr hj_coprime
      with u hu
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
    congr 1
    rw [pow_eq_pow_iff_modEq]
    have h_ord_dvd : orderOf u ∣ (p - 1) := by
      rw [← ZMod.card_units, ← Nat.card_eq_fintype_card]
      exact orderOf_dvd_natCard u
    exact hmn.of_dvd h_ord_dvd
  have h_sum_toZMod : PadicInt.toZMod SmZ = PadicInt.toZMod SnZ := by
    rw [hSmZ_def, hSnZ_def]
    simp only [map_sum, map_mul, map_pow, map_natCast]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    by_cases hj_ne : j = 0
    · subst j
      simp
    · congr 1
      exact h_pow_pred_ZMod j hj hj_ne
  have h_sub_mem : SmZ - SnZ ∈ Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p]) := by
    have h_sub : PadicInt.toZMod (SmZ - SnZ) = 0 := by
      rw [map_sub, h_sum_toZMod, sub_self]
    have h_ker : SmZ - SnZ ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod]
      exact h_sub
    rwa [PadicInt.maximalIdeal_eq_span_p] at h_ker
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp h_sub_mem
  refine ⟨z, ?_⟩
  have hSm_cast :
      (∑ x ∈ Finset.range p,
        (x : ℚ_[p]) ^ (m - 1) * ((x * a / p : ℕ) : ℚ_[p])) = (SmZ : ℚ_[p]) := by
    rw [hSmZ_def]
    simp [PadicInt.coe_sum]
  have hSn_cast :
      (∑ x ∈ Finset.range p,
        (x : ℚ_[p]) ^ (n - 1) * ((x * a / p : ℕ) : ℚ_[p])) = (SnZ : ℚ_[p]) := by
    rw [hSnZ_def]
    simp [PadicInt.coe_sum]
  rw [hSm_cast, hSn_cast]
  have hzQ := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hz
  push_cast at hzQ
  linear_combination hzQ

/-- Full divided-Bernoulli Kummer congruence for primes `p ≥ 5`, proved from
the side-condition-free Voronoi congruence.-/
theorem bernoulli_div_sModEq_of_modEq_full_geFive
    {p m n : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (hnot : ¬ (p - 1) ∣ n)
    (hmn : m ≡ n [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (((bernoulli m : ℚ) / (m : ℕ) : ℚ) : ℚ_[p]) -
        (((bernoulli n : ℚ) / (n : ℕ) : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  have hnot_m : ¬ (p - 1) ∣ m := by
    intro hdvd
    have h_n_mod : n ≡ 0 [MOD p - 1] :=
      hmn.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)
    exact hnot (Nat.modEq_zero_iff_dvd.mp h_n_mod)
  have hmn_pred : (m - 1) ≡ (n - 1) [MOD p - 1] := by
    have h1 : (m - 1) + 1 = m := Nat.succ_pred_eq_of_pos hm_pos
    have h2 : (n - 1) + 1 = n := Nat.succ_pred_eq_of_pos hn_pos
    have h_mod_add1 : (m - 1) + 1 ≡ (n - 1) + 1 [MOD p - 1] := by
      rw [h1, h2]
      exact hmn
    exact Nat.ModEq.add_right_cancel' 1 h_mod_add1
  obtain ⟨g, hg_gen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  set a : ℕ := (g : ZMod p).val with ha_def
  have ha_coprimeZ : Nat.Coprime a p := ZMod.val_coe_unit_coprime g
  have ha_coprime : ¬ p ∣ a := by
    rw [Nat.coprime_comm] at ha_coprimeZ
    exact hp.coprime_iff_not_dvd.mp ha_coprimeZ
  have ha_cast : ((a : ℕ) : ZMod p) = (g : ZMod p) := by
    rw [ha_def]
    exact ZMod.natCast_zmod_val _
  have hg_order : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg_gen, Nat.card_eq_fintype_card,
      ZMod.card_units]
  have h_gmn_eq : g ^ m = g ^ n :=
    primitiveRoot_unit_pow_eq_of_modEq (p := p) (g := g) hg_order hmn
  have h_gmn1_eq : g ^ (m - 1) = g ^ (n - 1) :=
    primitiveRoot_unit_pow_eq_of_modEq (p := p) (g := g) hg_order hmn_pred
  have h_mn_ZMod : ((a : ℕ) : ZMod p) ^ m = ((a : ℕ) : ZMod p) ^ n := by
    rw [ha_cast]
    simpa [Units.val_pow_eq_pow_val] using
      congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h_gmn_eq
  have h_mn1_ZMod : ((a : ℕ) : ZMod p) ^ (m - 1) =
      ((a : ℕ) : ZMod p) ^ (n - 1) := by
    rw [ha_cast]
    simpa [Units.val_pow_eq_pow_val] using
      congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h_gmn1_eq
  obtain ⟨z_m, hz_m⟩ := voronoi_congruence_mod_p_strong
    (p := p) (a := a) (h := m) hp_ge_five ha_coprime hm_pos hm_even hnot_m
  obtain ⟨z_n, hz_n⟩ := voronoi_congruence_mod_p_strong
    (p := p) (a := a) (h := n) hp_ge_five ha_coprime hn_pos hn_even hnot
  set Am : ℤ_[p] := (a : ℤ_[p]) ^ m with hAm_def
  set An : ℤ_[p] := (a : ℤ_[p]) ^ n with hAn_def
  set Am1 : ℤ_[p] := (a : ℤ_[p]) ^ (m - 1) with hAm1_def
  set An1 : ℤ_[p] := (a : ℤ_[p]) ^ (n - 1) with hAn1_def
  set SmZ : ℤ_[p] := ∑ x ∈ Finset.range p,
    ((x : ℕ) : ℤ_[p]) ^ (m - 1) * (((x * a / p : ℕ) : ℤ_[p])) with hSmZ_def
  set SnZ : ℤ_[p] := ∑ x ∈ Finset.range p,
    ((x : ℕ) : ℤ_[p]) ^ (n - 1) * (((x * a / p : ℕ) : ℤ_[p])) with hSnZ_def
  have h_mk_eq_zmod : ∀ {x y : ℤ_[p]}, PadicInt.toZMod x = PadicInt.toZMod y →
      x - y ∈ Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p]) := fun {x y} h => by
    have h_sub : PadicInt.toZMod (x - y) = 0 := by rw [map_sub, h, sub_self]
    have h_ker : x - y ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod]
      exact h_sub
    rwa [PadicInt.maximalIdeal_eq_span_p] at h_ker
  have h_toZMod_a : PadicInt.toZMod (a : ℤ_[p]) = ((a : ℕ) : ZMod p) := by
    rw [map_natCast]
  have h_Am_An_toZMod : PadicInt.toZMod Am = PadicInt.toZMod An := by
    rw [hAm_def, hAn_def, map_pow, map_pow, h_toZMod_a]
    exact h_mn_ZMod
  obtain ⟨d_A, hd_A⟩ := Ideal.mem_span_singleton.mp (h_mk_eq_zmod h_Am_An_toZMod)
  have h_Am1_An1_toZMod : PadicInt.toZMod Am1 = PadicInt.toZMod An1 := by
    rw [hAm1_def, hAn1_def, map_pow, map_pow, h_toZMod_a]
    exact h_mn1_ZMod
  obtain ⟨d_A1, hd_A1⟩ :=
    Ideal.mem_span_singleton.mp (h_mk_eq_zmod h_Am1_An1_toZMod)
  obtain ⟨d_S, hd_S⟩ := voronoi_floor_sum_sModEq_of_pred_modEq
    (p := p) (a := a) (m := m) (n := n) hm_pos hn_pos hmn_pred
  have h_ax_sub_one_unit : ∀ {k : ℕ}, ¬ (p - 1) ∣ k →
      IsUnit ((a : ℤ_[p]) ^ k - 1) := fun {k} hk => by
    rw [PadicInt.isUnit_iff]
    by_contra h_norm
    have h_mem : ((a : ℤ_[p]) ^ k - 1 : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
      PadicInt.mem_nonunits.mpr (lt_of_le_of_ne (PadicInt.norm_le_one _) h_norm)
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at h_mem
    rw [map_sub, map_one, map_pow, map_natCast, ha_cast, sub_eq_zero] at h_mem
    have h_gk : g ^ k = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h_mem)
    exact hk (hg_order ▸ orderOf_dvd_of_pow_eq_one h_gk)
  have h_Am_sub_one_unit : IsUnit (Am - 1) := by
    rw [hAm_def]
    exact h_ax_sub_one_unit hnot_m
  have h_An_sub_one_unit : IsUnit (An - 1) := by
    rw [hAn_def]
    exact h_ax_sub_one_unit hnot
  have hunit_inv : ∀ {x : ℤ_[p]} (hx : IsUnit x),
      x * (hx.unit⁻¹ : (ℤ_[p])ˣ).val = 1 := by
    intro x hx
    change ((hx.unit * hx.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  set AmInv : ℤ_[p] := (h_Am_sub_one_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hAmInv_def
  have hAmInv_mul : (Am - 1) * AmInv = 1 := hunit_inv h_Am_sub_one_unit
  set AnInv : ℤ_[p] := (h_An_sub_one_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hAnInv_def
  have hAnInv_mul : (An - 1) * AnInv = 1 := hunit_inv h_An_sub_one_unit
  set E : ℤ_[p] := (Am - 1) * (d_A1 * SmZ + An1 * d_S) - d_A * Am1 * SmZ
    with hE_def
  refine ⟨AmInv * AnInv * E + AmInv * z_m - AnInv * z_n, ?_⟩
  set Am_Q : ℚ_[p] := (Am : ℚ_[p]) with hAm_Q_def
  set An_Q : ℚ_[p] := (An : ℚ_[p]) with hAn_Q_def
  set Am1_Q : ℚ_[p] := (Am1 : ℚ_[p]) with hAm1_Q_def
  set An1_Q : ℚ_[p] := (An1 : ℚ_[p]) with hAn1_Q_def
  set Sm_Q : ℚ_[p] := (SmZ : ℚ_[p]) with hSm_Q_def
  set Sn_Q : ℚ_[p] := (SnZ : ℚ_[p]) with hSn_Q_def
  set Bm_div : ℚ_[p] := (((bernoulli m : ℚ) / (m : ℕ) : ℚ) : ℚ_[p])
    with hBm_div_def
  set Bn_div : ℚ_[p] := (((bernoulli n : ℚ) / (n : ℕ) : ℚ) : ℚ_[p])
    with hBn_div_def
  have hSm_cast :
      (∑ x ∈ Finset.range p,
        (x : ℚ_[p]) ^ (m - 1) * ((x * a / p : ℕ) : ℚ_[p])) = Sm_Q := by
    rw [hSm_Q_def, hSmZ_def]
    simp [PadicInt.coe_sum]
  have hSn_cast :
      (∑ x ∈ Finset.range p,
        (x : ℚ_[p]) ^ (n - 1) * ((x * a / p : ℕ) : ℚ_[p])) = Sn_Q := by
    rw [hSn_Q_def, hSnZ_def]
    simp [PadicInt.coe_sum]
  have hz_m_Q :
      (Am_Q - 1) * Bm_div - Am1_Q * Sm_Q = (p : ℚ_[p]) * (z_m : ℚ_[p]) := by
    rw [hAm_Q_def, hAm1_Q_def, hAm_def, hAm1_def, hBm_div_def]
    rw [hSm_cast] at hz_m
    convert hz_m using 2 <;> push_cast [hBm_div_def] <;> ring
  have hz_n_Q :
      (An_Q - 1) * Bn_div - An1_Q * Sn_Q = (p : ℚ_[p]) * (z_n : ℚ_[p]) := by
    rw [hAn_Q_def, hAn1_Q_def, hAn_def, hAn1_def, hBn_div_def]
    rw [hSn_cast] at hz_n
    convert hz_n using 2 <;> push_cast [hBn_div_def] <;> ring
  have hS_Q : Sm_Q - Sn_Q = (p : ℚ_[p]) * (d_S : ℚ_[p]) := by
    rw [hSm_cast, hSn_cast] at hd_S
    exact hd_S
  have h_An_eq_Q : An_Q = Am_Q - (p : ℚ_[p]) * (d_A : ℚ_[p]) := by
    have hdAQ := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hd_A
    rw [hAm_Q_def, hAn_Q_def]
    push_cast at hdAQ ⊢
    linear_combination -hdAQ
  have h_An1_eq_Q : An1_Q = Am1_Q - (p : ℚ_[p]) * (d_A1 : ℚ_[p]) := by
    have hdA1Q := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hd_A1
    rw [hAm1_Q_def, hAn1_Q_def]
    push_cast at hdA1Q ⊢
    linear_combination -hdA1Q
  have h_Sn_eq_Q : Sn_Q = Sm_Q - (p : ℚ_[p]) * (d_S : ℚ_[p]) := by
    linear_combination -hS_Q
  have hE_eq_Q :
      (An_Q - 1) * Am1_Q * Sm_Q - (Am_Q - 1) * An1_Q * Sn_Q =
        (p : ℚ_[p]) * ((E : ℤ_[p]) : ℚ_[p]) := by
    rw [hE_def]
    push_cast
    rw [← hAm_Q_def, ← hAm1_Q_def, ← hAn1_Q_def, ← hSm_Q_def]
    rw [h_An_eq_Q, h_An1_eq_Q, h_Sn_eq_Q]
    ring
  set AmInv_Q : ℚ_[p] := ((AmInv : ℤ_[p]) : ℚ_[p]) with hAmInv_Q_def
  set AnInv_Q : ℚ_[p] := ((AnInv : ℤ_[p]) : ℚ_[p]) with hAnInv_Q_def
  set z_m_Q : ℚ_[p] := ((z_m : ℤ_[p]) : ℚ_[p]) with hz_m_Q_def
  set z_n_Q : ℚ_[p] := ((z_n : ℤ_[p]) : ℚ_[p]) with hz_n_Q_def
  set E_Q : ℚ_[p] := ((E : ℤ_[p]) : ℚ_[p]) with hE_Q_def
  have h_Am_AmInv : (Am_Q - 1) * AmInv_Q = 1 := by
    rw [hAmInv_Q_def]
    have := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hAmInv_mul
    rw [hAm_Q_def]
    push_cast at this
    exact this
  have h_An_AnInv : (An_Q - 1) * AnInv_Q = 1 := by
    rw [hAnInv_Q_def]
    have := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hAnInv_mul
    rw [hAn_Q_def]
    push_cast at this
    exact this
  have h_witness_eq :
      (((AmInv * AnInv * E + AmInv * z_m - AnInv * z_n : ℤ_[p]) : ℚ_[p])) =
        AmInv_Q * AnInv_Q * E_Q + AmInv_Q * z_m_Q - AnInv_Q * z_n_Q := by
    rw [hAmInv_Q_def, hAnInv_Q_def, hz_m_Q_def, hz_n_Q_def, hE_Q_def]
    push_cast
    ring
  rw [h_witness_eq]
  have h_Am_sub_one_ne : Am_Q - 1 ≠ 0 := fun h0 => one_ne_zero <| by
    rw [← h_Am_AmInv, h0, zero_mul]
  have h_An_sub_one_ne : An_Q - 1 ≠ 0 := fun h0 => one_ne_zero <| by
    rw [← h_An_AnInv, h0, zero_mul]
  have h_key :
      (Am_Q - 1) * (An_Q - 1) * (Bm_div - Bn_div) =
        (Am_Q - 1) * (An_Q - 1) * ((p : ℚ_[p]) *
          (AmInv_Q * AnInv_Q * E_Q + AmInv_Q * z_m_Q - AnInv_Q * z_n_Q)) := by
    have h_lhs :
        (Am_Q - 1) * (An_Q - 1) * (Bm_div - Bn_div) =
          (An_Q - 1) * ((Am_Q - 1) * Bm_div) -
            (Am_Q - 1) * ((An_Q - 1) * Bn_div) := by ring
    rw [h_lhs]
    have h_Bm_expand :
        (Am_Q - 1) * Bm_div = Am1_Q * Sm_Q + (p : ℚ_[p]) * z_m_Q := by
      rw [hz_m_Q_def]
      linear_combination hz_m_Q
    have h_Bn_expand :
        (An_Q - 1) * Bn_div = An1_Q * Sn_Q + (p : ℚ_[p]) * z_n_Q := by
      rw [hz_n_Q_def]
      linear_combination hz_n_Q
    rw [h_Bm_expand, h_Bn_expand]
    rw [show (An_Q - 1) * (Am1_Q * Sm_Q + (p : ℚ_[p]) * z_m_Q) -
          (Am_Q - 1) * (An1_Q * Sn_Q + (p : ℚ_[p]) * z_n_Q) =
        ((An_Q - 1) * Am1_Q * Sm_Q - (Am_Q - 1) * An1_Q * Sn_Q) +
          (p : ℚ_[p]) * ((An_Q - 1) * z_m_Q - (Am_Q - 1) * z_n_Q) from by ring,
      hE_eq_Q]
    have h_rhs_goal :
        (Am_Q - 1) * (An_Q - 1) * ((p : ℚ_[p]) *
          (AmInv_Q * AnInv_Q * E_Q + AmInv_Q * z_m_Q - AnInv_Q * z_n_Q)) =
        (p : ℚ_[p]) * E_Q +
          (p : ℚ_[p]) * ((An_Q - 1) * z_m_Q - (Am_Q - 1) * z_n_Q) := by
      rw [show (Am_Q - 1) * (An_Q - 1) * ((p : ℚ_[p]) *
          (AmInv_Q * AnInv_Q * E_Q + AmInv_Q * z_m_Q - AnInv_Q * z_n_Q)) =
        (p : ℚ_[p]) * (((Am_Q - 1) * AmInv_Q) * ((An_Q - 1) * AnInv_Q) * E_Q) +
          (p : ℚ_[p]) * (((Am_Q - 1) * AmInv_Q) * (An_Q - 1) * z_m_Q) -
          (p : ℚ_[p]) * (((An_Q - 1) * AnInv_Q) * (Am_Q - 1) * z_n_Q) from by ring]
      rw [h_Am_AmInv, h_An_AnInv]
      ring
    rw [h_rhs_goal]
  have h_cancel_ne : (Am_Q - 1) * (An_Q - 1) ≠ 0 :=
    mul_ne_zero h_Am_sub_one_ne h_An_sub_one_ne
  exact mul_left_cancel₀ h_cancel_ne h_key

/-- **Standard Kummer congruence for divided Bernoulli numbers.**

This is the public full congruence used by the Carlitz route.  The odd-prime
case reduces to `p ≥ 5`: if `p = 3`, then `p - 1 = 2` divides every even
non-boundary exponent, contradicting the hypotheses.-/
theorem bernoulli_div_sModEq_of_modEq_full
    {p m n : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (hnot : ¬ (p - 1) ∣ n)
    (hmn : m ≡ n [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (((bernoulli m : ℚ) / (m : ℕ) : ℚ) : ℚ_[p]) -
        (((bernoulli n : ℚ) / (n : ℕ) : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp_ge_five : 5 ≤ p :=
    five_le_of_odd_prime_and_even_nonboundary (p := p) hp_odd hn_even hnot
  exact bernoulli_div_sModEq_of_modEq_full_geFive hp_ge_five hm_pos hn_pos
    hm_even hn_even hnot hmn

end KummerCriterion
