/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.BigOperators.Field
public import Tengoku.Seed.Analysis.Convex.Deriv
public import Tengoku.Seed.Analysis.Convex.Piecewise
public import Tengoku.Seed.Analysis.Convex.Jensen
public import Tengoku.Seed.RingTheory.Polynomial.Pochhammer

/-!
# Pochhammer polynomials

This file proves analysis theorems for Pochhammer polynomials.

## Main statements

* `Differentiable.descPochhammer_eval` is the proof that the descending Pochhammer polynomial
  `descPochhammer ℝ n` is differentiable.

* `ConvexOn.descPochhammer_eval` is the proof that the descending Pochhammer polynomial
  `descPochhammer ℝ n` is convex on `[n-1, ∞)`.

* `descPochhammer_eval_le_sum_descFactorial` is a special case of **Jensen's inequality**
  for `Nat.descFactorial`.

* `descPochhammer_eval_div_factorial_le_sum_choose` is a special case of **Jensen's inequality**
  for `Nat.choose`.
-/

public section


section DescPochhammer

variable {n : ℕ} {𝕜 : Type*} {k : 𝕜} [NontriviallyNormedField 𝕜]

/-- `descPochhammer 𝕜 n` is differentiable.
@isnad1 id=differen.0h2v.s6.05b7b96ec3ba from=seed src=0 shape=b5ed03d5 vocab=2475fd84
-/
theorem differentiable_descPochhammer_eval : Differentiable 𝕜 (descPochhammer 𝕜 n).eval := by
  simp [descPochhammer_eval_eq_prod_range, Differentiable.fun_finsetProd]

/-- `descPochhammer 𝕜 n` is continuous.
@isnad1 id=continuo.0h2v.s6.22cff9115b54 from=seed src=0 shape=7af1abc3 vocab=4e5b1e04
-/
theorem continuous_descPochhammer_eval : Continuous (descPochhammer 𝕜 n).eval := by
  exact differentiable_descPochhammer_eval.continuous

/--
@isnad1 id=eq.0h3v.s7.6f98d21021e1 from=seed src=0 shape=4a9cb9fb vocab=d3db5224
-/
lemma deriv_descPochhammer_eval_eq_sum_prod_range_erase (n : ℕ) (k : 𝕜) :
    deriv (descPochhammer 𝕜 n).eval k
      = ∑ i ∈ Finset.range n, ∏ j ∈ (Finset.range n).erase i, (k - j) := by
  simp [descPochhammer_eval_eq_prod_range, deriv_fun_finsetProd]

/-- `deriv (descPochhammer ℝ n)` is monotone on `(n-1, ∞)`.
@isnad1 id=monotone.0h1v.s6.0e00443833e0 from=seed src=0 shape=3ad5ff7e vocab=cf1f3bce
-/
lemma monotoneOn_deriv_descPochhammer_eval (n : ℕ) :
    MonotoneOn (deriv (descPochhammer ℝ n).eval) (Set.Ioi (n - 1 : ℝ)) := by
  induction n with
  | zero => simp [monotoneOn_const]
  | succ n ih =>
    intro a ha b hb hab
    rw [Set.mem_Ioi, Nat.cast_add_one, add_sub_cancel_right] at ha hb
    simp_rw [deriv_descPochhammer_eval_eq_sum_prod_range_erase]
    gcongr with i hi
    intro j hj
    rw [Finset.mem_erase, Finset.mem_range] at hj
    apply sub_nonneg_of_le
    exact ha.le.trans' (mod_cast Nat.le_pred_of_lt hj.2)

/-- `descPochhammer ℝ n` is convex on `[n-1, ∞)`.
@isnad1 id=convexon.0h1v.s5.f74369154485 from=seed src=0 shape=d7bd5bed vocab=91f6da20
-/
theorem convexOn_descPochhammer_eval (n : ℕ) :
    ConvexOn ℝ (Set.Ici (n - 1 : ℝ)) (descPochhammer ℝ n).eval := by
  rcases n.eq_zero_or_pos with h_eq | _
  · simp [h_eq, convexOn_const, convex_Ici]
  · apply MonotoneOn.convexOn_of_deriv (convex_Ici (n - 1 : ℝ))
      continuous_descPochhammer_eval.continuousOn
      differentiable_descPochhammer_eval.differentiableOn
    rw [interior_Ici]
    exact monotoneOn_deriv_descPochhammer_eval n

private lemma piecewise_Ici_descPochhammer_eval_zero_eq_descFactorial (k n : ℕ) :
    (Set.Ici (n - 1 : ℝ)).piecewise (descPochhammer ℝ n).eval 0 k
      = k.descFactorial n := by
  rw [Set.piecewise, descPochhammer_eval_eq_descFactorial, ite_eq_left_iff, Set.mem_Ici, not_le,
    eq_comm, Pi.zero_apply, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt, ← @Nat.cast_lt ℝ]
  exact (sub_lt_self (n : ℝ) zero_lt_one).trans'

private lemma convexOn_piecewise_Ici_descPochhammer_eval_zero (hn : n ≠ 0) :
    ConvexOn ℝ Set.univ ((Set.Ici (n - 1 : ℝ)).piecewise (descPochhammer ℝ n).eval 0) := by
  rw [← Nat.pos_iff_ne_zero] at hn
  apply convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic
    (convexOn_descPochhammer_eval n) (convexOn_const 0 (convex_Iic (n - 1 : ℝ)))
    (monotoneOn_descPochhammer_eval n) antitoneOn_const
  simpa [← Nat.cast_pred hn] using descPochhammer_eval_coe_nat_of_lt (Nat.sub_one_lt_of_lt hn)

/-- Special case of **Jensen's inequality** for `Nat.descFactorial`.
@isnad1 id=le.4h5v.s7.acb8e6a1eded from=seed src=0 shape=dabac79d vocab=7815e174
-/
theorem descPochhammer_eval_le_sum_descFactorial
    (hn : n ≠ 0) {ι : Type*} {t : Finset ι} (p : ι → ℕ) (w : ι → ℝ)
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (h_avg : n - 1 ≤ ∑ i ∈ t, w i * p i) :
    (descPochhammer ℝ n).eval (∑ i ∈ t, w i * p i)
      ≤ ∑ i ∈ t, w i * (p i).descFactorial n := by
  let f : ℝ → ℝ := (Set.Ici (n - 1 : ℝ)).piecewise (descPochhammer ℝ n).eval 0
  suffices h_jensen : f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i) by
    simpa only [smul_eq_mul, f, Set.piecewise_eq_of_mem (Set.Ici (n - 1 : ℝ)) _ _ h_avg,
      piecewise_Ici_descPochhammer_eval_zero_eq_descFactorial] using h_jensen
  exact ConvexOn.map_sum_le (convexOn_piecewise_Ici_descPochhammer_eval_zero hn) h₀ h₁ (by simp)

/-- Special case of **Jensen's inequality** for `Nat.choose`.
@isnad1 id=le.4h5v.s7.2b8ab407ee58 from=seed src=0 shape=f1c72687 vocab=08ea56c9
-/
theorem descPochhammer_eval_div_factorial_le_sum_choose
    (hn : n ≠ 0) {ι : Type*} {t : Finset ι} (p : ι → ℕ) (w : ι → ℝ)
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (h_avg : n - 1 ≤ ∑ i ∈ t, w i * p i) :
    (descPochhammer ℝ n).eval (∑ i ∈ t, w i * p i) / n.factorial
      ≤ ∑ i ∈ t, w i * (p i).choose n := by
  simp_rw [Nat.cast_choose_eq_descPochhammer_div,
    mul_div, ← Finset.sum_div, descPochhammer_eval_eq_descFactorial]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact descPochhammer_eval_le_sum_descFactorial hn p w h₀ h₁ h_avg

end DescPochhammer
