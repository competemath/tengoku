/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.ChernoffTransform
import Tengoku.Randomsettheory.RandomSetTheory.ExponentialTaylor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Chernoff transform of the exact strong-moment tail

This file evaluates the exact exponential-series tail which occurs after
upper truncation in the Rio--Marchina argument.  If

`Q * exp x <= y ^ q`,

then evaluation at the Laplace parameter `x / y`, together with
`psi_q(x) <= (x / q) * exp x`, gives

`T (fun t => Q / y^q * psi_q(t*y)) x <= (1 + 1/q) * y`.

Unlike the Lagrange remainder, this estimate has no factor growing like
`x^(q-1)`.
-/

open Real Set

noncomputable section

namespace ProbabilityTheory

/-- The exact order-`q` exponential tail with moment proxy `Q` and
truncation height `y`.-/
def exactStrongMomentTailExponent
    (q : ℕ) (Q y t : ℝ) : ℝ :=
  Q / y ^ q * expSeriesTail q (t * y)

@[simp] theorem exactStrongMomentTailExponent_zero
    {q : ℕ} (hq : q ≠ 0) (Q y : ℝ) :
    exactStrongMomentTailExponent q Q y 0 = 0 := by
  simp [exactStrongMomentTailExponent, hq]

theorem exactStrongMomentTailExponent_nonneg
    (q : ℕ) {Q y t : ℝ} (hQ : 0 ≤ Q) (hy : 0 < y)
    (ht : 0 ≤ t) :
    0 ≤ exactStrongMomentTailExponent q Q y t := by
  unfold exactStrongMomentTailExponent
  exact mul_nonneg (div_nonneg hQ (pow_nonneg hy.le q))
    (expSeriesTail_nonneg (mul_nonneg ht hy.le) q)

/-- Exact evaluation of the polynomial tail component of Rio's Chernoff
transform.-/
theorem chernoffTransform_exactStrongMomentTailExponent_le
    (q : ℕ) (hq : 1 ≤ q) {Q y x : ℝ}
    (hQ : 0 ≤ Q) (hy : 0 < y) (hx : 0 < x)
    (hscale : Q * Real.exp x ≤ y ^ q) :
    chernoffTransform (exactStrongMomentTailExponent q Q y) x ≤
      (1 + 1 / (q : ℝ)) * y := by
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  have hyq : 0 < y ^ q := pow_pos hy q
  have hcoef : 0 ≤ Q / y ^ q := div_nonneg hQ hyq.le
  have hcoefExp : (Q / y ^ q) * Real.exp x ≤ 1 := by
    calc
      (Q / y ^ q) * Real.exp x =
          (Q * Real.exp x) / y ^ q := by ring
      _ ≤ 1 := (div_le_one hyq).2 hscale
  have htail := expSeriesTail_le_div_mul_exp q hq x hx.le
  have hscaledTail :
      (Q / y ^ q) * expSeriesTail q x ≤ x / (q : ℝ) := by
    calc
      (Q / y ^ q) * expSeriesTail q x ≤
          (Q / y ^ q) * ((x / (q : ℝ)) * Real.exp x) :=
        mul_le_mul_of_nonneg_left htail hcoef
      _ = (x / (q : ℝ)) *
          ((Q / y ^ q) * Real.exp x) := by ring
      _ ≤ (x / (q : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hcoefExp (div_nonneg hx.le (by positivity))
      _ = x / (q : ℝ) := by ring
  have hnonneg : ∀ t : ℝ, 0 < t →
      0 ≤ exactStrongMomentTailExponent q Q y t := by
    intro t ht
    exact exactStrongMomentTailExponent_nonneg q hQ hy ht.le
  have hb : BddBelow
      (Set.range (chernoffObjective
        (exactStrongMomentTailExponent q Q y) x)) :=
    bddBelow_range_chernoffObjective hx.le hnonneg
  have heval := chernoffTransform_le_objective
    (psi := exactStrongMomentTailExponent q Q y) (x := x)
    (t := x / y) (div_pos hx hy) hb
  have harg : (x / y) * y = x := by field_simp
  unfold exactStrongMomentTailExponent at heval
  rw [harg] at heval
  calc
    chernoffTransform (exactStrongMomentTailExponent q Q y) x ≤
        ((Q / y ^ q) * expSeriesTail q x + x) / (x / y) := heval
    _ ≤ (x / (q : ℝ) + x) / (x / y) := by
      exact div_le_div_of_nonneg_right
        (add_le_add hscaledTail le_rfl) (div_pos hx hy).le
    _ = (1 + 1 / (q : ℝ)) * y := by
      field_simp [hx.ne', hy.ne', hq0]
      ring

end ProbabilityTheory
