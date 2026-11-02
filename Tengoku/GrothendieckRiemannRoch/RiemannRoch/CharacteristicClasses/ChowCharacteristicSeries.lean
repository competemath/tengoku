/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.Formal
import Tengoku.Seed.RingTheory.PowerSeries.Inverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Chern character and Todd coefficients from Chern operators

Newton power sums and the truncated Todd exponential are constructed in the
endomorphism ring of a rational module. Their single-root formulas follow from
the geometric inverse series and the scalar Bernoulli Todd identity.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace AlgebraicGeometry.Chow.M7

section Series

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

/-- Newton power sums from Chern operators: `Σ_{m≥0} (-1)^m p_{m+1} t^m = c'(t) c(t)⁻¹`.-/
def psumOp (c : ℕ → Module.End ℚ M) : ℕ → Module.End ℚ M
  | 0 => 0
  | m + 1 => ((-1 : ℚ) ^ m) • PowerSeries.coeff m
      (PowerSeries.mk (fun n ↦ ((n + 1 : ℕ) : ℚ) • c (n + 1)) *
        PowerSeries.invOfUnit (PowerSeries.mk c) 1)

/-- `ch_0 = rk`, `ch_m = p_m / m!`.-/
def chOfChern (r : ℕ) (c : ℕ → Module.End ℚ M) : ℕ → Module.End ℚ M
  | 0 => (r : ℚ) • 1
  | m + 1 => (1 / ((m + 1).factorial : ℚ)) • psumOp c (m + 1)

/-- Coefficients of `log (x / (1 - e^{-x})) = x/2 - Σ_{k≥1} B_{2k} x^{2k} / (2k (2k)!)`.-/
def toddLogCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else -(bernoulli n) / ((n : ℚ) * n.factorial)

/-- `td = exp(Σ_n toddLogCoeff n · p_n)`, coefficientwise (the exponential series truncates).-/
def tdOfChern (c : ℕ → Module.End ℚ M) (m : ℕ) : Module.End ℚ M :=
  ∑ j ∈ Finset.range (m + 1), (1 / (j.factorial : ℚ)) •
    PowerSeries.coeff m ((PowerSeries.mk fun n ↦ toddLogCoeff n • psumOp c n) ^ j)

/-! ### helpers -/

open PowerSeries in
/-- One-root Chern series `1 + x t` has inverse `Σ (-x)^n t^n`.-/
theorem invOfUnit_line (x : Module.End ℚ M) :
    invOfUnit (mk (fun i ↦ if i = 0 then (1 : Module.End ℚ M) else if i = 1 then x else 0)) 1 =
      mk (fun n ↦ (-x) ^ n) := by
  set φ : PowerSeries (Module.End ℚ M) :=
    mk (fun i ↦ if i = 0 then (1 : Module.End ℚ M) else if i = 1 then x else 0)
  set ψ : PowerSeries (Module.End ℚ M) := mk (fun n ↦ (-x) ^ n)
  have hφ : φ = 1 + C x * PowerSeries.X := by
    ext n
    rcases n with _ | _ | n
    · simp [φ]
    · simp [φ, coeff_one]
    · simp [φ, coeff_one, coeff_succ_mul_X]
  have hψφ : ψ * φ = 1 := by
    rw [hφ, mul_add, mul_one]
    ext n
    rcases n with _ | n
    · simp [ψ]
    · rw [map_add, ← mul_assoc, coeff_succ_mul_X, coeff_mul_C]
      simp [ψ, coeff_one, pow_succ]
  have h1 : constantCoeff φ = ((1 : (Module.End ℚ M)ˣ) : Module.End ℚ M) := by
    simp [φ]
  have := mul_invOfUnit φ 1 h1
  calc invOfUnit φ 1 = (ψ * φ) * invOfUnit φ 1 := by rw [hψφ, one_mul]
    _ = ψ := by rw [mul_assoc, this, mul_one]

open PowerSeries in
/-- Newton power sums for a single operator root are its ordinary powers.-/
theorem psumOp_line (x : Module.End ℚ M) (m : ℕ) :
    psumOp (fun i ↦ if i = 0 then 1 else if i = 1 then x else 0) (m + 1) = x ^ (m + 1) := by
  simp only [psumOp]
  rw [invOfUnit_line]
  have hC : (mk (fun n ↦ ((n + 1 : ℕ) : ℚ) •
      (fun i ↦ if i = 0 then (1 : Module.End ℚ M) else if i = 1 then x else 0) (n + 1))) =
      C x := by
    ext n
    rcases n with _ | n
    · simp
    · simp
  rw [hC, coeff_C_mul, coeff_mk]
  rcases Nat.even_or_odd m with h | h
  · rw [Even.neg_pow h x, Even.neg_one_pow h, one_smul, pow_succ']
  · rw [Odd.neg_pow h x, Odd.neg_one_pow h, pow_succ', mul_neg, neg_smul, one_smul, neg_neg]

/-! ### TD-ALG helpers: `exp (Σ aₙ tⁿ) = t/(1-e^{-t})` over `ℚ` -/

open PowerSeries in
/-- The one-root log-Todd series `L = Σ aₙ tⁿ`.-/
private def toddLogSeries : PowerSeries ℚ := mk toddLogCoeff

/-- LEAF CH-ALG (pure algebra): for one root, `c = 1 + x t`, `ch_m = x^m / m!`.-/
theorem chOfChern_line (x : Module.End ℚ M) (m : ℕ) :
    chOfChern 1 (fun i ↦ if i = 0 then 1 else if i = 1 then x else 0) m =
      (1 / (m.factorial : ℚ)) • x ^ m := by
  rcases m with _ | m
  · simp [chOfChern]
  · simp only [chOfChern]
    rw [psumOp_line]

end Series
end AlgebraicGeometry.Chow.M7
