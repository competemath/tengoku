/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.Seed.Algebra.Order.BigOperators.Ring.Finset
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Analysis.Complex.Exponential
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Engel-form (Titu) inequalities under the division convention

The Cauchy–Schwarz quotient inequality
`(∑ f)² / (∑ g) ≤ ∑ f² / g` in the form used by the energy calculus: denominators are
only assumed **nonnegative**, with the convention hypothesis `g i = 0 → f i = 0` making
the `x / 0 = 0` cases degenerate rather than false.

Mathlib proves the strictly-positive-denominator form
(`Finset.sq_sum_div_le_sum_sq_div`); this file wraps it, splitting off the
zero-denominator indices. The two- and three-term forms are instantiations.
-/

namespace RegularityLemmata

/-- Engel form / Titu's lemma over a finset, with nonnegative denominators and the
`x / 0 = 0` convention hypothesis.
@isnad1 id=le.2h4v.s7.d17e3f93d252 from=translated src=- shape=f859e410 vocab=6c53dc37
-/
theorem titu_finset {ι : Type*} [DecidableEq ι] (f g : ι → ℝ) (I : Finset ι)
    (hg : ∀ i ∈ I, 0 ≤ g i) (hfg : ∀ i ∈ I, g i = 0 → f i = 0) :
    (∑ i ∈ I, f i) ^ 2 / (∑ i ∈ I, g i) ≤ ∑ i ∈ I, f i ^ 2 / g i := by
  set P := I.filter fun i => 0 < g i with hP
  have hzero : ∀ i ∈ I, ¬ 0 < g i → g i = 0 := fun i hi hng =>
    le_antisymm (not_lt.mp hng) (hg i hi)
  have hsumf : ∑ i ∈ I, f i = ∑ i ∈ P, f i := by
    rw [hP]
    refine (Finset.sum_filter_of_ne fun i hi hfi => ?_).symm
    by_contra hng
    exact hfi (hfg i hi (hzero i hi hng))
  have hsumg : ∑ i ∈ I, g i = ∑ i ∈ P, g i := by
    rw [hP]
    refine (Finset.sum_filter_of_ne fun i hi hgi => ?_).symm
    by_contra hng
    exact hgi (hzero i hi hng)
  calc (∑ i ∈ I, f i) ^ 2 / ∑ i ∈ I, g i
      = (∑ i ∈ P, f i) ^ 2 / ∑ i ∈ P, g i := by rw [hsumf, hsumg]
    _ ≤ ∑ i ∈ P, f i ^ 2 / g i :=
        Finset.sq_sum_div_le_sum_sq_div P f fun i hi => (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i ∈ I, f i ^ 2 / g i := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i hi _ => ?_
        exact div_nonneg (sq_nonneg _) (hg i hi)

/-- **Mass-weighted Cauchy–Schwarz.** A mass-weighted average is dominated by the
mass-weighted mean square, in the denominator-free form the energy calculus wants:
`(∑ aᵢ mᵢ)² ≤ (∑ mᵢ) · ∑ aᵢ² mᵢ`.

Only nonnegativity of the masses is assumed — no positivity, and no convention hypothesis,
because the `mᵢ = 0` indices drop from both sides on their own. This is the form that turns a
large rectangle error into an energy increment.
@isnad1 id=le.1h4v.s7.b21ffa3df14d from=translated src=- shape=955685fa vocab=5aa34ec3
-/
theorem sq_sum_mul_le_sum_mul_sum_sq_mul {ι : Type*} [DecidableEq ι] (a m : ι → ℝ)
    (I : Finset ι) (hm : ∀ i ∈ I, 0 ≤ m i) :
    (∑ i ∈ I, a i * m i) ^ 2 ≤ (∑ i ∈ I, m i) * ∑ i ∈ I, a i ^ 2 * m i := by
  have hterm : ∀ i ∈ I, (a i * m i) ^ 2 / m i = a i ^ 2 * m i := by
    intro i _
    rcases eq_or_ne (m i) 0 with h | h
    · rw [h, div_zero, mul_zero]
    · field_simp
  have htitu := titu_finset (fun i => a i * m i) m I hm (fun i _ h => by rw [h, mul_zero])
  rw [Finset.sum_congr rfl hterm] at htitu
  rcases eq_or_lt_of_le (Finset.sum_nonneg hm) with h0 | hpos
  · -- Total mass zero: every mass vanishes, so both sides are `0`.
    have hz : ∀ i ∈ I, m i = 0 := by
      intro i hi
      by_contra hne
      exact absurd h0.symm (ne_of_gt (Finset.sum_pos' hm
        ⟨i, hi, lt_of_le_of_ne (hm i hi) (Ne.symm hne)⟩))
    rw [Finset.sum_eq_zero fun i hi => by rw [hz i hi, mul_zero], ← h0]
    norm_num
  · rw [div_le_iff₀ hpos] at htitu
    calc (∑ i ∈ I, a i * m i) ^ 2 ≤ (∑ i ∈ I, a i ^ 2 * m i) * ∑ i ∈ I, m i := htitu
      _ = (∑ i ∈ I, m i) * ∑ i ∈ I, a i ^ 2 * m i := by ring

/-- Two-term Engel form with the division convention.
@isnad1 id=le.4h4v.s7.dac49ce75144 from=translated src=- shape=aa4bc034 vocab=d8071e98
-/
theorem titu_two {a b p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (ha : p = 0 → a = 0) (hb : q = 0 → b = 0) :
    (a + b) ^ 2 / (p + q) ≤ a ^ 2 / p + b ^ 2 / q := by
  have := titu_finset (![a, b]) (![p, q]) Finset.univ
    (fun i _ => by fin_cases i <;> assumption)
    (fun i _ => by fin_cases i <;> assumption)
  simpa [Fin.sum_univ_two] using this

/-- Three-term Engel form with the division convention.
@isnad1 id=le.6h6v.s8.1413efad5196 from=translated src=- shape=2bb63ea4 vocab=d8071e98
-/
theorem titu_three {a b c p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (ha : p = 0 → a = 0) (hb : q = 0 → b = 0) (hc : r = 0 → c = 0) :
    (a + b + c) ^ 2 / (p + q + r) ≤ a ^ 2 / p + b ^ 2 / q + c ^ 2 / r := by
  have := titu_finset (![a, b, c]) (![p, q, r]) Finset.univ
    (fun i _ => by fin_cases i <;> assumption)
    (fun i _ => by fin_cases i <;> assumption)
  simpa [Fin.sum_univ_three, add_assoc] using this

/-- Engel form with an explicit defect: the two-term inequality improves by the
weighted squared deviation of the first cell's ratio from the pooled ratio.
@isnad1 id=le.2h4v.s7.a3b0b343d0d9 from=translated src=- shape=ed14150d vocab=762a6581
-/
theorem engel_defect_lower {a b p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (a + b) ^ 2 / (p + q) + p * (a / p - (a + b) / (p + q)) ^ 2 ≤ a ^ 2 / p + b ^ 2 / q := by
  have hpq : (0 : ℝ) < p + q := by linarith
  have key : a ^ 2 / p + b ^ 2 / q
      - ((a + b) ^ 2 / (p + q) + p * (a / p - (a + b) / (p + q)) ^ 2)
      = (a * q - b * p) ^ 2 / (q * (p + q) ^ 2) := by
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ (a * q - b * p) ^ 2 / (q * (p + q) ^ 2) := by positivity
  linarith

/-- Two-factor perturbation bound: replacing each factor of a product by a nearby
value perturbs the product by at most the sum of the factor errors, provided the
retained factors `x` and `e` have absolute value at most one (densities are in `[0,1]`).
Consumed by path and triangle counting.
@isnad1 id=le.2h4v.s6.4f3753ab6c8f from=translated src=- shape=820674b7 vocab=7729d30c
-/
theorem abs_mul_sub_mul_le {x y d e : ℝ} (hx : |x| ≤ 1) (he : |e| ≤ 1) :
    |x * y - d * e| ≤ |x - d| + |y - e| := by
  have key : x * y - d * e = x * (y - e) + e * (x - d) := by ring
  rw [key]
  calc |x * (y - e) + e * (x - d)|
      ≤ |x * (y - e)| + |e * (x - d)| := abs_add_le _ _
    _ = |x| * |y - e| + |e| * |x - d| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * |y - e| + 1 * |x - d| :=
        add_le_add (mul_le_mul_of_nonneg_right hx (abs_nonneg _))
          (mul_le_mul_of_nonneg_right he (abs_nonneg _))
    _ = |x - d| + |y - e| := by ring

/-- Three-factor perturbation bound: replacing each factor of a triple product by a nearby
value perturbs the product by at most the sum of the three factor errors, given the
retained factors have absolute value at most one. Consumed by strong three-vertex
counting.
@isnad1 id=le.4h6v.s7.277a6647c919 from=translated src=- shape=1cea4a6b vocab=7729d30c
-/
theorem abs_mul_mul_sub_mul_mul_le {a b c a' b' c' : ℝ}
    (hb : |b| ≤ 1) (hc : |c| ≤ 1) (ha' : |a'| ≤ 1) (hb' : |b'| ≤ 1) :
    |a * b * c - a' * b' * c'| ≤ |a - a'| + |b - b'| + |c - c'| := by
  have key : a * b * c - a' * b' * c'
      = (a - a') * b * c + a' * (b - b') * c + a' * b' * (c - c') := by ring
  rw [key]
  have h1 : |(a - a') * b * c| ≤ |a - a'| := by
    rw [abs_mul, abs_mul]
    calc |a - a'| * |b| * |c| ≤ |a - a'| * 1 * 1 := by gcongr
      _ = |a - a'| := by ring
  have h2 : |a' * (b - b') * c| ≤ |b - b'| := by
    rw [abs_mul, abs_mul]
    calc |a'| * |b - b'| * |c| ≤ 1 * |b - b'| * 1 := by gcongr
      _ = |b - b'| := by ring
  have h3 : |a' * b' * (c - c')| ≤ |c - c'| := by
    rw [abs_mul, abs_mul]
    calc |a'| * |b'| * |c - c'| ≤ 1 * 1 * |c - c'| := by gcongr
      _ = |c - c'| := by ring
  have hstep : |(a - a') * b * c + a' * (b - b') * c + a' * b' * (c - c')|
      ≤ |(a - a') * b * c| + |a' * (b - b') * c| + |a' * b' * (c - c')| := by
    have hxy := abs_add_le ((a - a') * b * c) (a' * (b - b') * c)
    have hxyz := abs_add_le ((a - a') * b * c + a' * (b - b') * c) (a' * b' * (c - c'))
    linarith
  linarith [hstep, h1, h2, h3]

/-! ### Bilinear domination by 0/1 rectangles

A `[0,1]`-weighted bilinear combination of a matrix's entries is bounded by the largest
**0/1** combination — that is, by the sup over genuine sub-rectangles. Stated abstractly
here because the hypotheses mention only a real matrix and two coefficient vectors.

This is the load-bearing step behind contraction of a stepped rectangle sum, where the
coefficients are relative cell masses. Note the constant: the bound is `ε`, **not** `2ε` —
no extreme-point machinery is needed, because `cᵢ * yᵢ ≤ max yᵢ 0` holds pointwise. -/

/-- A `[0,1]`-weighted sum is dominated by the sum over its nonnegative part — the 0/1
choice `cᵢ = 1 ↔ 0 ≤ yᵢ`.
@isnad1 id=le.2h4v.s7.4ff202f676d9 from=translated src=- shape=6c943635 vocab=de056eee
-/
theorem sum_mul_le_sum_filter_nonneg {ι : Type*} [DecidableEq ι] {c : ι → ℝ} (I : Finset ι)
    (hc0 : ∀ i ∈ I, 0 ≤ c i) (hc1 : ∀ i ∈ I, c i ≤ 1) (y : ι → ℝ) :
    ∑ i ∈ I, c i * y i ≤ ∑ i ∈ I.filter (fun i => 0 ≤ y i), y i := by
  classical
  calc ∑ i ∈ I, c i * y i
      ≤ ∑ i ∈ I, max (y i) 0 := by
        refine Finset.sum_le_sum fun i hi => ?_
        rcases le_or_gt 0 (y i) with h | h
        · calc c i * y i ≤ 1 * y i := mul_le_mul_of_nonneg_right (hc1 i hi) h
            _ = y i := one_mul _
            _ ≤ max (y i) 0 := le_max_left _ _
        · calc c i * y i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hc0 i hi) h.le
            _ ≤ max (y i) 0 := le_max_right _ _
    _ = ∑ i ∈ I.filter (fun i => 0 ≤ y i), y i := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : 0 ≤ y i
        · simp [h]
        · simp [h, max_eq_right (not_le.mp h).le]

/-- The mirror bound, with the 0/1 choice `cᵢ = 1 ↔ yᵢ < 0`.
@isnad1 id=le.2h4v.s7.496045ce7608 from=translated src=- shape=cb0a18b5 vocab=a7704ea5
-/
theorem sum_filter_neg_le_sum_mul {ι : Type*} [DecidableEq ι] {c : ι → ℝ} (I : Finset ι)
    (hc0 : ∀ i ∈ I, 0 ≤ c i) (hc1 : ∀ i ∈ I, c i ≤ 1) (y : ι → ℝ) :
    ∑ i ∈ I.filter (fun i => y i < 0), y i ≤ ∑ i ∈ I, c i * y i := by
  classical
  calc ∑ i ∈ I.filter (fun i => y i < 0), y i
      = ∑ i ∈ I, min (y i) 0 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : y i < 0
        · simp [h, min_eq_left h.le]
        · simp [h, min_eq_right (not_lt.mp h)]
    _ ≤ ∑ i ∈ I, c i * y i := by
        refine Finset.sum_le_sum fun i hi => ?_
        rcases le_or_gt 0 (y i) with h | h
        · calc min (y i) 0 ≤ 0 := min_le_right _ _
            _ ≤ c i * y i := mul_nonneg (hc0 i hi) h
        · calc min (y i) 0 = y i := min_eq_left h.le
            _ = 1 * y i := (one_mul _).symm
            _ ≤ c i * y i := mul_le_mul_of_nonpos_right (hc1 i hi) h.le

/-- **Bilinear domination, at constant `1`.** If every sub-rectangle sum of `x` is within
`ε`, then so is every `[0,1]`-weighted bilinear combination.

The `1` here is what keeps the downstream common-refinement constant at `2` rather than
`4`: contraction is free, and the only factor of two comes from a triangle inequality.
@isnad1 id=le.5h8v.s7.d582e68fbb70 from=translated src=- shape=ade36a23 vocab=9a05ebea
-/
theorem abs_sum_bilinear_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {c : ι → ℝ}
    {d : κ → ℝ} (I : Finset ι) (J : Finset κ)
    (hc0 : ∀ i ∈ I, 0 ≤ c i) (hc1 : ∀ i ∈ I, c i ≤ 1)
    (hd0 : ∀ j ∈ J, 0 ≤ d j) (hd1 : ∀ j ∈ J, d j ≤ 1) (x : ι → κ → ℝ) {ε : ℝ}
    (hrect : ∀ I' ⊆ I, ∀ J' ⊆ J, |∑ i ∈ I', ∑ j ∈ J', x i j| ≤ ε) :
    |∑ i ∈ I, c i * ∑ j ∈ J, d j * x i j| ≤ ε := by
  classical
  have hswap : ∀ I' ⊆ I, ∑ i ∈ I', (∑ j ∈ J, d j * x i j)
      = ∑ j ∈ J, d j * (∑ i ∈ I', x i j) := by
    intro I' _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  set y : ι → ℝ := fun i => ∑ j ∈ J, d j * x i j with hy
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- Lower bound: choose the negative parts on both sides.
    set I' : Finset ι := I.filter (fun i => y i < 0) with hI'
    have hI'sub : I' ⊆ I := Finset.filter_subset _ _
    have h1 : ∑ i ∈ I', y i ≤ ∑ i ∈ I, c i * y i :=
      sum_filter_neg_le_sum_mul I hc0 hc1 y
    set z : κ → ℝ := fun j => ∑ i ∈ I', x i j with hz
    set J' : Finset κ := J.filter (fun j => z j < 0) with hJ'
    have h2 : ∑ j ∈ J', z j ≤ ∑ j ∈ J, d j * z j :=
      sum_filter_neg_le_sum_mul J hd0 hd1 z
    have h3 : ∑ i ∈ I', y i = ∑ j ∈ J, d j * z j := by rw [hy, hswap I' hI'sub]
    have h4 : ∑ j ∈ J', z j = ∑ i ∈ I', ∑ j ∈ J', x i j := by
      rw [hz]; exact (Finset.sum_comm).symm
    have h5 : -ε ≤ ∑ i ∈ I', ∑ j ∈ J', x i j :=
      (abs_le.mp (hrect I' hI'sub J' (Finset.filter_subset _ _))).1
    linarith [h1, h2, h3 ▸ h2, h4 ▸ h5]
  · -- Upper bound: choose the nonnegative parts on both sides.
    set I' : Finset ι := I.filter (fun i => 0 ≤ y i) with hI'
    have hI'sub : I' ⊆ I := Finset.filter_subset _ _
    have h1 : ∑ i ∈ I, c i * y i ≤ ∑ i ∈ I', y i :=
      sum_mul_le_sum_filter_nonneg I hc0 hc1 y
    set z : κ → ℝ := fun j => ∑ i ∈ I', x i j with hz
    set J' : Finset κ := J.filter (fun j => 0 ≤ z j) with hJ'
    have h2 : ∑ j ∈ J, d j * z j ≤ ∑ j ∈ J', z j :=
      sum_mul_le_sum_filter_nonneg J hd0 hd1 z
    have h3 : ∑ i ∈ I', y i = ∑ j ∈ J, d j * z j := by rw [hy, hswap I' hI'sub]
    have h4 : ∑ j ∈ J', z j = ∑ i ∈ I', ∑ j ∈ J', x i j := by
      rw [hz]; exact (Finset.sum_comm).symm
    have h5 : ∑ i ∈ I', ∑ j ∈ J', x i j ≤ ε :=
      (abs_le.mp (hrect I' hI'sub J' (Finset.filter_subset _ _))).2
    linarith [h1, h2, h3, h4 ▸ h5]

/-! ### Tests and adversarial examples -/

-- **Contraction is not vacuous**: at all-ones coefficients the bilinear sum *is* a
-- rectangle sum, so the bound is attained rather than merely implied.

/-! ### The exponential inequality behind multiplicative weights -/

/-- **`exp (−x) ≤ 1 − x + x²/2` for `x ≥ 0`.** The reverse-direction companion of Mathlib's
series bound `Real.quadratic_le_exp_of_nonneg` (`1 + x + x²/2 ≤ exp x`), from which it follows
since `(1 − x + x²/2)·(1 + x + x²/2) = 1 + x⁴/4 ≥ 1`. This is the single analytic ingredient of
the Hedge regret bound (`RegularityLemmata/Finite/Hedge.lean`); Mathlib's pin has only the forward
bound. Recorded
on the plausibly-Mathlib-shaped list (#54).
@isnad1 id=le.1h1v.s6.3e5149f28210 from=translated src=- shape=b77fa57d vocab=8aeb8a51
-/
theorem exp_neg_le_one_sub_add_sq_half {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hq : 0 ≤ 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (x - 1)]
  have hexp := Real.quadratic_le_exp_of_nonneg hx
  have hpos : 0 < Real.exp x := Real.exp_pos x
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hpos]
  calc (1 : ℝ) ≤ (1 - x + x ^ 2 / 2) * (1 + x + x ^ 2 / 2) := by nlinarith [sq_nonneg (x ^ 2)]
    _ ≤ (1 - x + x ^ 2 / 2) * Real.exp x := mul_le_mul_of_nonneg_left hexp hq

-- The inequality is tight at `x = 0` (both sides `1`) and holds at `x = 1`, statement-level.

end RegularityLemmata
