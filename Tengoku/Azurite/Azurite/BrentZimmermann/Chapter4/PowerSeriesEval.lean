/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BrentZimmermann.Chapter4.RepeatedDoubling
import Tengoku.Seed.Analysis.SpecialFunctions.Exponential
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Base
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brent–Zimmermann §4.4: Power series (introduction)

After argument reduction one evaluates a power series, such as `exp x = ∑ x^j/j!` or
`ln(1 + x) = ∑ (−1)^j x^(j+1)/(j+1)`.  Notation: `x` the point, `n` the target precision, `d` the
number of terms.  The instructive example is `exp x` for `|x| ≤ 1`:

  `exp x = ∑_{j<d} x^j/j! + R_d(x)`,  `|R_d(x)| ≤ |x|^d exp|x| / d! ≤ e / d!`,            (4.21)

so `d ~ n / lg n` terms suffice (Stirling) and Horner costs `O(n M(n) / log n)`.  Forward summation
generates `t_j = x t_{j−1} / j`, `S_j = S_{j−1} + t_j` and stops when `|t_d| < 2^(−n) / e`, so `d`
need not be known in advance (unlike backward summation).  With correctly rounded operations,
`◦(x op y) = (x op y)(1 + δ)`, `|δ| ≤ ε = 2^(−n)`: `|tc_j − t_j| / |t_j| ≤ 2jε + O(ε²)` and
`|Ŝ_d − S_d| ≤ (d + 2) e ε + O(ε²) = O(nε)`, so `ε = O(2^(−n)/n)` suffices: about `lg n` guard
digits.  The working precision can be reduced for small terms.  For large `x > 0` the terms grow
until `j ≈ |x|`, so `Ω(|x|)` terms are needed; for large negative `x` the largest term is
`≈ exp|x| / √(2π|x|)` against a result `exp(−|x|)`: about `2|x| / log 2` guard digits
("catastrophic cancellation"), avoided by `exp x = 1/exp(−x)`.  For `erf` the two series (4.22)
and (4.23) are mathematically but not numerically equivalent — (4.23) has no cancellation; for
large `|x|` both need `Ω(x²)` terms and the asymptotic expansion of `erfc` (§4.5) is preferable.

What is formalized:

* `hasSum_exp_series`, `hasSum_log_one_add_series` — the expansions of `exp` and `ln(1 + x)`
  (`|x| < 1`) from Mathlib.
* `abs_exp_sub_sum_le` — the remainder bound of (4.21), `|R_d(x)| ≤ |x|^d/d! · exp|x|`, for every
  `x`; `abs_exp_sub_sum_le_of_abs_le_one` (`≤ e/d!`), `exp_series_terms_suffice`
  (`2^n e ≤ d!` gives `|R_d| ≤ 2^(−n)`), `exp_series_stop` (the stopping rule: `|t_d| < 2^(−n)/e`
  gives `|R_d| < 2^(−n)`).
* `expPartial`, `expPartial_succ` — the forward recurrence (`expTerm_succ` is in §4.3.2).
* `roundedExpTerm`, `roundedExpTerm_eq`, `abs_roundedExpTerm_sub_le` — the terms computed with
  a relative rounding error `θ_j` per step (`|θ_j| ≤ 3ε` covers the multiplication and the
  division): `|tc_j − t_j| ≤ 6jε |t_j|` for `3jε ≤ 1`.
* `roundedSum`, `roundedSum_sub_le` — forward summation with a relative error `σ_j` per
  addition: the generic bound `|Ŝ_d − S_d| ≤ (1+ε)^d (η ∑|t_j| + d ε (M + (1+η) T))`.
* `exp_roundedSum_error` — for `|x| ≤ 1`: `|Ŝ_d − S_d| ≤ 46 d ε` once `6dε ≤ 1`, and
  `exp_guard_digits`: `ε ≤ 2^(−n) / (46 d)` gives `|Ŝ_d − S_d| ≤ 2^(−n)` — the `lg n` guard digits.
* `guard_digits_of_neg` — `logb 2 (exp (2|x|)) = 2|x| / log 2`, the bits lost to cancellation
  (§4.3.2 gave the factor).

Not formalized: Stirling (`d ~ n/lg n`), the Horner cost, the Stirling estimate of the largest
term, the `erf` series (no `erf` in Mathlib; (4.22)/(4.23) await the asymptotic-expansion
section), the arctan and sinh expansions (not in Mathlib).
-/

namespace Azurite

namespace BZ

open Finset Real

/-! ### The expansions -/

/-- `exp x = ∑ x^j / j!`.
@isnad1 id=hassum.0h1v.s5.2478f7ade1d5 from=translated src=- shape=63bf745d vocab=827d1423
-/
theorem hasSum_exp_series (x : ℝ) : HasSum (fun j : ℕ => x ^ j / j.factorial) (exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-! ### The remainder of the exponential series, (4.21) -/

/-- The remainder bound `|exp x − ∑_{j<d} x^j/j!| ≤ |x|^d / d! · exp |x|`, for every `x`.
@isnad1 id=le.0h2v.s6.3ff3f415a5d0 from=translated src=- shape=9f01ab06 vocab=7d3ec52a
-/
theorem abs_exp_sub_sum_le (x : ℝ) (d : ℕ) :
    |exp x - ∑ j ∈ range d, x ^ j / j.factorial| ≤ |x| ^ d / d.factorial * exp |x| := by
  have hs := hasSum_exp_series x
  have hsum := hs.summable
  have hsh : Summable (fun n : ℕ => x ^ (n + d) / (n + d).factorial) :=
    hsum.comp_injective (add_left_injective d)
  have hsplit := Summable.sum_add_tsum_nat_add' (f := fun n : ℕ => x ^ n / n.factorial) (k := d) hsh
  rw [hs.tsum_eq] at hsplit
  have htail : exp x - ∑ j ∈ range d, x ^ j / j.factorial
      = ∑' n : ℕ, x ^ (n + d) / (n + d).factorial := by
    linarith
  have hsa := hasSum_exp_series |x|
  have hsabs : Summable (fun n : ℕ => |x| ^ n / n.factorial) := hsa.summable
  have hb : ∀ n : ℕ, |x ^ (n + d) / (n + d).factorial|
      ≤ |x| ^ d / d.factorial * (|x| ^ n / n.factorial) := by
    intro n
    have hfpos : (0 : ℝ) < (n + d).factorial := by exact_mod_cast (n + d).factorial_pos
    rw [abs_div, abs_pow, abs_of_pos hfpos, pow_add, div_le_iff₀ hfpos]
    have hdiv : (d.factorial * n.factorial : ℝ) ≤ (n + d).factorial := by
      have := Nat.factorial_mul_factorial_dvd_factorial_add d n
      rw [add_comm] at this
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) this
    have hd : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
    have hn : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    calc |x| ^ n * |x| ^ d
        = |x| ^ d / d.factorial * (|x| ^ n / n.factorial) * (d.factorial * n.factorial) := by
          field_simp
      _ ≤ |x| ^ d / d.factorial * (|x| ^ n / n.factorial) * (n + d).factorial := by
          gcongr
  have hsb : Summable (fun n : ℕ => |x| ^ d / d.factorial * (|x| ^ n / n.factorial)) :=
    hsabs.mul_left _
  rw [htail]
  calc |∑' n : ℕ, x ^ (n + d) / (n + d).factorial|
      ≤ ∑' n : ℕ, |x ^ (n + d) / (n + d).factorial| := by
        have := norm_tsum_le_tsum_norm hsh.norm
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' n : ℕ, |x| ^ d / d.factorial * (|x| ^ n / n.factorial) :=
        hsh.abs.tsum_le_tsum hb hsb
    _ = |x| ^ d / d.factorial * exp |x| := by rw [tsum_mul_left, hsa.tsum_eq]

/-- For `|x| ≤ 1`, `|R_d(x)| ≤ e / d!`.
@isnad1 id=le.1h2v.s6.201930922610 from=translated src=- shape=64bfe1e6 vocab=99e81f53
-/
theorem abs_exp_sub_sum_le_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) (d : ℕ) :
    |exp x - ∑ j ∈ range d, x ^ j / j.factorial| ≤ exp 1 / d.factorial := by
  refine (abs_exp_sub_sum_le x d).trans ?_
  have hd : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  calc |x| ^ d / d.factorial * exp |x| ≤ 1 ^ d / d.factorial * exp 1 := by gcongr
    _ = exp 1 / d.factorial := by ring

/-- `d` terms suffice for `n` bits as soon as `2^n e ≤ d!`.
@isnad1 id=le.2h3v.s7.0d2ef3cfb4e8 from=translated src=- shape=0fa60e12 vocab=bf9a3929
-/
theorem exp_series_terms_suffice {x : ℝ} (hx : |x| ≤ 1) {d n : ℕ}
    (hd : (2 : ℝ) ^ n * exp 1 ≤ d.factorial) :
    |exp x - ∑ j ∈ range d, x ^ j / j.factorial| ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
  refine (abs_exp_sub_sum_le_of_abs_le_one hx d).trans ?_
  have hdpos : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  rw [zpow_neg, zpow_natCast, div_le_iff₀ hdpos]
  calc exp 1 = (2 : ℝ) ^ n * exp 1 / 2 ^ n := by field_simp
    _ ≤ d.factorial / 2 ^ n := by gcongr
    _ = ((2 : ℝ) ^ n)⁻¹ * d.factorial := by ring

/-- The stopping rule of forward summation: for `|x| ≤ 1`, once the next term satisfies
`|t_d| < 2^(−n) / e`, the remainder is below `2^(−n)`.
@isnad1 id=lt.2h3v.s7.9867d10f3f7f from=translated src=- shape=9d824f00 vocab=0cf41f6f
-/
theorem exp_series_stop {x : ℝ} (hx : |x| ≤ 1) {d n : ℕ}
    (ht : |expTerm x d| < (2 : ℝ) ^ (-(n : ℤ)) / exp 1) :
    |exp x - ∑ j ∈ range d, x ^ j / j.factorial| < (2 : ℝ) ^ (-(n : ℤ)) := by
  have h := abs_exp_sub_sum_le x d
  have hdpos : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have ht' : |expTerm x d| = |x| ^ d / d.factorial := by
    unfold expTerm; rw [abs_div, abs_pow, abs_of_pos hdpos]
  rw [ht'] at ht
  calc |exp x - ∑ j ∈ range d, x ^ j / j.factorial| ≤ |x| ^ d / d.factorial * exp |x| := h
    _ ≤ |x| ^ d / d.factorial * exp 1 := by gcongr
    _ < (2 : ℝ) ^ (-(n : ℤ)) / exp 1 * exp 1 :=
        mul_lt_mul_of_pos_right ht (exp_pos 1)
    _ = (2 : ℝ) ^ (-(n : ℤ)) := div_mul_cancel₀ _ (exp_pos 1).ne'

/-! ### Forward summation and its rounding errors -/

/-- The partial sums `S_j = ∑_{i≤j} t_i`.-/
noncomputable def expPartial (x : ℝ) (j : ℕ) : ℝ := ∑ i ∈ range (j + 1), expTerm x i

/--
@isnad1 id=eq.0h2v.s5.41b430212c83 from=translated src=- shape=3fcbc603 vocab=dbdae342
-/
theorem expPartial_succ (x : ℝ) (j : ℕ) :
    expPartial x (j + 1) = expPartial x j + expTerm x (j + 1) := by
  unfold expPartial; rw [sum_range_succ]

/-- The terms as computed, `tc_0 = 1` and `tc_j = (tc_{j−1} x / j)(1 + θ_j)`, where `θ_j` is the
relative error of the multiplication and the division together.-/
noncomputable def roundedExpTerm (x : ℝ) (θ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => roundedExpTerm x θ j * x / (j + 1) * (1 + θ (j + 1))

/-- `tc_j = t_j ∏_{i<j} (1 + θ_{i+1})`.
@isnad1 id=eq.0h3v.s5.368e57e92e6f from=translated src=- shape=e9e33be3 vocab=3e44e29c
-/
theorem roundedExpTerm_eq (x : ℝ) (θ : ℕ → ℝ) (j : ℕ) :
    roundedExpTerm x θ j = expTerm x j * ∏ i ∈ range j, (1 + θ (i + 1)) := by
  induction j with
  | zero => simp [roundedExpTerm, expTerm]
  | succ j ih =>
    rw [roundedExpTerm, ih, expTerm_succ, prod_range_succ]
    ring

/-- Forward summation as computed: `Ŝ_0 = tc_0`, `Ŝ_{j+1} = (Ŝ_j + tc_{j+1})(1 + σ_{j+1})`.-/
noncomputable def roundedSum (tc σ : ℕ → ℝ) : ℕ → ℝ
  | 0 => tc 0
  | j + 1 => (roundedSum tc σ j + tc (j + 1)) * (1 + σ (j + 1))

/-- The generic forward-summation error: with `|σ_j| ≤ ε`, `|tc_j − t_j| ≤ η |t_j|`,
`|∑_{i≤j} t_i| ≤ M` and `|t_j| ≤ T` for all `j`,
`|Ŝ_d − S_d| ≤ (1 + ε)^d (η ∑_{j≤d} |t_j| + d ε (M + (1 + η) T))`.
@isnad1 id=le.5h8v.s8.d70aa9bd771b from=translated src=- shape=62391c27 vocab=1f63f446
-/
theorem roundedSum_sub_le (t tc σ : ℕ → ℝ) {ε η M T : ℝ} (hη0 : 0 ≤ η) (hσ : ∀ j, |σ j| ≤ ε)
    (htc : ∀ j, |tc j - t j| ≤ η * |t j|) (hM : ∀ j, |∑ i ∈ range (j + 1), t i| ≤ M)
    (hT : ∀ j, |t j| ≤ T) (d : ℕ) :
    |roundedSum tc σ d - ∑ i ∈ range (d + 1), t i|
      ≤ (1 + ε) ^ d * (η * ∑ i ∈ range (d + 1), |t i| + d * ε * (M + (1 + η) * T)) := by
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hσ 0)
  have hT0 : 0 ≤ T := le_trans (abs_nonneg _) (hT 0)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  induction d with
  | zero =>
    simp only [roundedSum, zero_add, sum_range_one, pow_zero, one_mul, Nat.cast_zero, zero_mul,
      add_zero]
    exact htc 0
  | succ d ih =>
    set A := roundedSum tc σ d - ∑ i ∈ range (d + 1), t i with hA
    set X := η * ∑ i ∈ range (d + 1), |t i| + d * ε * (M + (1 + η) * T) with hX
    have hX0 : 0 ≤ X := by positivity
    -- the recurrence for the error
    have hrec : roundedSum tc σ (d + 1) - ∑ i ∈ range (d + 1 + 1), t i
        = A + (tc (d + 1) - t (d + 1))
          + σ (d + 1) * (∑ i ∈ range (d + 1), t i + A + tc (d + 1)) := by
      rw [roundedSum, sum_range_succ _ (d + 1), hA]; ring
    have htcb : |tc (d + 1)| ≤ (1 + η) * T := by
      calc |tc (d + 1)| = |t (d + 1) + (tc (d + 1) - t (d + 1))| := by ring_nf
        _ ≤ |t (d + 1)| + |tc (d + 1) - t (d + 1)| := abs_add_le _ _
        _ ≤ T + η * T := by
            gcongr
            · exact hT _
            · exact (htc _).trans (by gcongr; exact hT _)
        _ = (1 + η) * T := by ring
    have hstep : |roundedSum tc σ (d + 1) - ∑ i ∈ range (d + 1 + 1), t i|
        ≤ (1 + ε) * |A| + η * |t (d + 1)| + ε * (M + (1 + η) * T) := by
      rw [hrec]
      calc |A + (tc (d + 1) - t (d + 1)) + σ (d + 1) * (∑ i ∈ range (d + 1), t i + A + tc (d + 1))|
          ≤ |A| + |tc (d + 1) - t (d + 1)|
            + |σ (d + 1)| * (|∑ i ∈ range (d + 1), t i| + |A| + |tc (d + 1)|) := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            · exact abs_add_le _ _
            · rw [abs_mul]
              gcongr
              exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
        _ ≤ |A| + η * |t (d + 1)| + ε * (M + |A| + (1 + η) * T) := by
            gcongr
            · exact htc _
            · exact hσ _
            · exact hM _
        _ = (1 + ε) * |A| + η * |t (d + 1)| + ε * (M + (1 + η) * T) := by ring
    have hpow : (1 : ℝ) ≤ (1 + ε) ^ (d + 1) := one_le_pow₀ (by linarith)
    calc |roundedSum tc σ (d + 1) - ∑ i ∈ range (d + 1 + 1), t i|
        ≤ (1 + ε) * |A| + η * |t (d + 1)| + ε * (M + (1 + η) * T) := hstep
      _ ≤ (1 + ε) * ((1 + ε) ^ d * X) + η * |t (d + 1)| + ε * (M + (1 + η) * T) := by
          gcongr
      _ ≤ (1 + ε) ^ (d + 1) * X
          + (1 + ε) ^ (d + 1) * (η * |t (d + 1)| + ε * (M + (1 + η) * T)) := by
          have h0 : 0 ≤ η * |t (d + 1)| + ε * (M + (1 + η) * T) := by positivity
          have h2 := le_mul_of_one_le_left h0 hpow
          have h1 : (1 + ε) * ((1 + ε) ^ d * X) = (1 + ε) ^ (d + 1) * X := by ring
          linarith
      _ = (1 + ε) ^ (d + 1) * (η * ∑ i ∈ range (d + 1 + 1), |t i|
            + (d + 1 : ℕ) * ε * (M + (1 + η) * T)) := by
          rw [sum_range_succ _ (d + 1), hX]; push_cast; ring

/-- The guard digits lost to cancellation for negative `x` (§4.3.2): the factor `exp (2|x|)` is
`2|x| / log 2` bits.
@isnad1 id=eq.0h1v.s6.eb4dbddfdc83 from=translated src=- shape=20b81df4 vocab=8419b314
-/
theorem guard_digits_of_neg (x : ℝ) : Real.logb 2 (exp (2 * |x|)) = 2 * |x| / Real.log 2 := by
  rw [Real.logb, Real.log_exp]

end BZ

end Azurite
