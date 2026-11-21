/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.ChernoffTransform

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Optimization of a Bernstein rational exponent

The standard exponent

`V * t^2 / (2 * (1 - c*t/3))`

evaluated at its canonical parameter yields the inverse-Legendre bound
`sqrt (2*V*x) + c*x/3`.  The endpoint below only requires another exponent
to be bounded by the Bernstein exponent at that one parameter.  This is
particularly convenient for finite Taylor polynomials.
-/

open Real Set

noncomputable section

namespace ProbabilityTheory

/-- Rational Bernstein exponent, meaningful below its pole.-/
def bernsteinRationalExponent (V c t : ℝ) : ℝ :=
  V * t ^ 2 / (2 * (1 - c * t / 3))

/-- The Laplace parameter which gives the Gaussian-plus-linear Bernstein
bound.-/
def bernsteinOptimalParameter (V c x : ℝ) : ℝ :=
  let a := Real.sqrt (2 * x / V)
  a / (1 + c * a / 3)

theorem bernsteinOptimalParameter_pos
    {V c x : ℝ} (hV : 0 < V) (hc : 0 ≤ c) (hx : 0 < x) :
    0 < bernsteinOptimalParameter V c x := by
  let a := Real.sqrt (2 * x / V)
  have ha : 0 < a := Real.sqrt_pos.2 (div_pos (by positivity) hV)
  have hden : 0 < 1 + c * a / 3 := by positivity
  exact div_pos ha hden

/-- Exact objective value of the rational Bernstein exponent at its
canonical parameter.-/
theorem bernsteinRationalObjective_optimal
    {V c x : ℝ} (hV : 0 < V) (hc : 0 ≤ c) (hx : 0 < x) :
    (bernsteinRationalExponent V c
          (bernsteinOptimalParameter V c x) + x) /
        bernsteinOptimalParameter V c x =
      Real.sqrt (2 * V * x) + c * x / 3 := by
  let a : ℝ := Real.sqrt (2 * x / V)
  let d : ℝ := 1 + c * a / 3
  have haArg : 0 < 2 * x / V := div_pos (by positivity) hV
  have ha : 0 < a := Real.sqrt_pos.2 haArg
  have haSq : a ^ 2 = 2 * x / V := by
    dsimp only [a]
    exact Real.sq_sqrt haArg.le
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  have hsqrtSq : Real.sqrt (2 * V * x) ^ 2 = 2 * V * x :=
    Real.sq_sqrt (by positivity)
  have hrootProduct : a * Real.sqrt (2 * V * x) = 2 * x := by
    have hsq : (a * Real.sqrt (2 * V * x)) ^ 2 = (2 * x) ^ 2 := by
      rw [mul_pow, haSq, hsqrtSq]
      field_simp [hV.ne']
    have hleft : 0 ≤ a * Real.sqrt (2 * V * x) := by positivity
    have hright : 0 ≤ 2 * x := by positivity
    nlinarith
  have hpole : 1 - c * (a / d) / 3 = 1 / d := by
    dsimp only [d]
    field_simp [hd.ne']
    ring
  have hbern : bernsteinRationalExponent V c (a / d) = x / d := by
    unfold bernsteinRationalExponent
    rw [hpole, div_pow]
    field_simp [hV.ne', hd.ne']
    nlinarith [haSq]
  have ht : bernsteinOptimalParameter V c x = a / d := by rfl
  rw [ht, hbern]
  dsimp only [d]
  field_simp [ha.ne', hd.ne']
  ring_nf at hrootProduct ⊢
  nlinarith [hrootProduct]

/-- Any nonnegative exponent which is bounded by the rational Bernstein
exponent at the canonical parameter has the usual
Gaussian-plus-linear Chernoff transform.-/
theorem chernoffTransform_le_sqrt_add_linear_of_le_bernsteinOptimal
    {psi : ℝ → ℝ} {V c x : ℝ}
    (hV : 0 < V) (hc : 0 ≤ c) (hx : 0 < x)
    (hnonneg : ∀ t, 0 < t → 0 ≤ psi t)
    (hbound : psi (bernsteinOptimalParameter V c x) ≤
      bernsteinRationalExponent V c
        (bernsteinOptimalParameter V c x)) :
    chernoffTransform psi x ≤
      Real.sqrt (2 * V * x) + c * x / 3 := by
  have ht := bernsteinOptimalParameter_pos hV hc hx
  have hb := bddBelow_range_chernoffObjective hx.le hnonneg
  have heval := chernoffTransform_le_objective
    (psi := psi) (x := x) ht hb
  calc
    chernoffTransform psi x ≤
        (psi (bernsteinOptimalParameter V c x) + x) /
          bernsteinOptimalParameter V c x := heval
    _ ≤ (bernsteinRationalExponent V c
          (bernsteinOptimalParameter V c x) + x) /
          bernsteinOptimalParameter V c x :=
      div_le_div_of_nonneg_right (add_le_add hbound le_rfl) ht.le
    _ = Real.sqrt (2 * V * x) + c * x / 3 :=
      bernsteinRationalObjective_optimal hV hc hx

end ProbabilityTheory
