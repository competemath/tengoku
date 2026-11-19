/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.PortalPolynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Monotonicity of portal polynomials

A portal polynomial with nondecreasing coefficients is nondecreasing on the
unit interval.  The factorial normalization makes its derivative exactly the
portal polynomial of the forward differences.
-/

open Set
open scoped BigOperators Polynomial

namespace HansenCograph

private noncomputable def bernsteinCombination (n : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), a k • bernsteinPolynomial ℝ n k

private theorem bernsteinCombination_eval (n : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    (bernsteinCombination n a).eval x = (n.factorial : ℝ) * portalPolynomial n a x := by
  classical
  unfold bernsteinCombination portalPolynomial
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul, bernsteinPolynomial,
    Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hfac := Nat.choose_mul_factorial_mul_factorial hkn
  have hfacR : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ) =
      (n.factorial : ℝ) := by
    exact_mod_cast hfac
  rw [← hfacR]
  field_simp

private theorem sum_shift_smul_eq_sub
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (n : ℕ) (c : ℕ → ℝ) (q : ℕ → M) (hq : q (n + 1) = 0) :
    (∑ k ∈ Finset.range (n + 1), c (k + 1) • q (k + 1)) =
      (∑ k ∈ Finset.range (n + 1), c k • q k) - c 0 • q 0 := by
  have hfirst := Finset.sum_range_succ' (fun k ↦ c k • q k) (n + 1)
  have hlast := Finset.sum_range_succ (fun k ↦ c k • q k) (n + 1)
  rw [hq, smul_zero, add_zero] at hlast
  rw [hfirst] at hlast
  rw [← hlast]
  abel

private theorem bernsteinCombination_derivative_succ (n : ℕ) (a : ℕ → ℝ) :
    Polynomial.derivative (bernsteinCombination (n + 1) a) =
      (n + 1 : ℝ) • bernsteinCombination n (fun k ↦ a (k + 1) - a k) := by
  classical
  unfold bernsteinCombination
  rw [Polynomial.derivative_sum, Finset.sum_range_succ']
  simp only [Polynomial.derivative_smul, bernsteinPolynomial.derivative_zero,
    bernsteinPolynomial.derivative_succ_aux, Nat.add_sub_cancel]
  have hterminal : bernsteinPolynomial ℝ n (n + 1) = 0 :=
    bernsteinPolynomial.eq_zero_of_lt ℝ (Nat.lt_succ_self n)
  have hshift := sum_shift_smul_eq_sub n a (bernsteinPolynomial ℝ n) hterminal
  have hinner :
      (∑ k ∈ Finset.range (n + 1),
          a (k + 1) • (bernsteinPolynomial ℝ n k - bernsteinPolynomial ℝ n (k + 1))) +
          a 0 • (-bernsteinPolynomial ℝ n 0) =
        ∑ k ∈ Finset.range (n + 1),
          (a (k + 1) - a k) • bernsteinPolynomial ℝ n k := by
    simp only [smul_sub, Finset.sum_sub_distrib, smul_neg, sub_smul]
    rw [hshift]
    module
  calc
    _ = ((n + 1 : ℕ) : ℝ[X]) *
        ((∑ k ∈ Finset.range (n + 1),
            a (k + 1) • (bernsteinPolynomial ℝ n k - bernsteinPolynomial ℝ n (k + 1))) +
          a 0 • (-bernsteinPolynomial ℝ n 0)) := by
      rw [mul_add, Finset.mul_sum]
      apply congrArg₂ (fun p q ↦ p + q)
      · apply Finset.sum_congr rfl
        intro k hk
        rw [Polynomial.smul_eq_C_mul]
        simp only [Polynomial.smul_eq_C_mul]
        push_cast
        ring
      · rw [Polynomial.smul_eq_C_mul]
        simp only [Polynomial.smul_eq_C_mul]
        ring
    _ = ((n + 1 : ℕ) : ℝ[X]) *
        (∑ k ∈ Finset.range (n + 1),
          (a (k + 1) - a k) • bernsteinPolynomial ℝ n k) := by rw [hinner]
    _ = (n + 1 : ℝ) •
        (∑ k ∈ Finset.range (n + 1),
          (a (k + 1) - a k) • bernsteinPolynomial ℝ n k) := by
      rw [Polynomial.smul_eq_C_mul]
      congr 1
      ext
      simp [Nat.cast_add]

/-- The derivative of a positive-degree portal polynomial is the portal
polynomial of its forward differences.-/
theorem portalPolynomial_hasDerivAt_succ (n : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    HasDerivAt (portalPolynomial (n + 1) a)
      (portalPolynomial n (fun k ↦ a (k + 1) - a k) x) x := by
  let p := ((n + 1).factorial : ℝ)⁻¹ • bernsteinCombination (n + 1) a
  have hp : p.eval = portalPolynomial (n + 1) a := by
    funext y
    simp only [p, Polynomial.eval_smul, bernsteinCombination_eval, smul_eq_mul,
      Nat.factorial_succ]
    field_simp
  rw [← hp]
  have hderiv :
      portalPolynomial n (fun k ↦ a (k + 1) - a k) x =
        p.derivative.eval x := by
    symm
    simp only [p, Polynomial.derivative_smul, Polynomial.eval_smul,
      bernsteinCombination_derivative_succ, smul_smul, bernsteinCombination_eval,
      smul_eq_mul, Nat.factorial_succ]
    field_simp
    push_cast
    rfl
  rw [hderiv]
  exact p.hasDerivAt x

private theorem portalPolynomial_nonneg_of_coeff_nonneg
    (n : ℕ) (a : ℕ → ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (ha : ∀ k < n + 1, 0 ≤ a k) :
    0 ≤ portalPolynomial n a x := by
  classical
  unfold portalPolynomial
  apply Finset.sum_nonneg
  intro k hk
  have hklt : k < n + 1 := Finset.mem_range.mp hk
  have hx0 : 0 ≤ x := hx.1
  have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have hak : 0 ≤ a k := ha k hklt
  positivity

/-- A portal polynomial whose coefficients are nondecreasing is nondecreasing
on the unit interval.-/
theorem portalPolynomial_monotoneOn_of_coeff_monotone
    {n : ℕ} {a : ℕ → ℝ}
    (ha : ∀ k < n, a k ≤ a (k + 1)) :
    MonotoneOn (portalPolynomial n a) (Icc (0 : ℝ) 1) := by
  cases n with
  | zero =>
      intro x hx y hy hxy
      simp [portalPolynomial]
  | succ n =>
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
        (portalPolynomial_continuous (n + 1) a).continuousOn
        (f' := portalPolynomial n (fun k ↦ a (k + 1) - a k))
      · intro x hx
        exact (portalPolynomial_hasDerivAt_succ n a x).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        apply portalPolynomial_nonneg_of_coeff_nonneg n _ ⟨hx.1.le, hx.2.le⟩
        intro k hk
        exact sub_nonneg.mpr (ha k hk)

end HansenCograph
