/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Arctan
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Sinc
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Arsinh
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.NumberTheory.Harmonic.EulerMascheroni
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unified Expression AST

This file defines the unified AST for real expressions (`Expr`) and its
evaluation semantics. All numerical algorithms in LeanCert operate on this
single expression type.

## Main definitions

* `LeanCert.Core.Expr` - The expression AST supporting algebraic and transcendental operations
* `LeanCert.Core.Expr.eval` - Evaluation of expressions given a variable assignment

## Design notes

The expression type uses natural number indices for variables. This simplifies
the interval evaluation and automatic differentiation implementations.
-/

namespace LeanCert.Core

/-! ## Auxiliary definition for atanh

Since Mathlib doesn't provide `Real.atanh`, we define it here using the
standard formula: `atanh x = (1/2) * log((1+x)/(1-x))` for `|x| < 1`.
-/

/-- The inverse hyperbolic tangent function.
    Defined as `atanh x = (1/2) * log((1+x)/(1-x))` for `|x| < 1`. -/
noncomputable def Real.atanh (x : ℝ) : ℝ :=
  (1 / 2) * Real.log ((1 + x) / (1 - x))

/-- For |x| < 1, the argument (1+x)/(1-x) is positive.
@isnad1 id=lt.1h1v.s5.63f4e1895683 from=translated src=- shape=7a7f3841 vocab=6f27e6e0
-/
theorem Real.atanh_arg_pos {x : ℝ} (hx : |x| < 1) : 0 < (1 + x) / (1 - x) := by
  have h1 : -1 < x := by linarith [abs_lt.mp hx]
  have h2 : x < 1 := (abs_lt.mp hx).2
  have hnum : 0 < 1 + x := by linarith
  have hdenom : 0 < 1 - x := by linarith
  exact div_pos hnum hdenom

/-- atanh(0) = 0
@isnad1 id=eq.0h0v.s3.9d2e9925590a from=translated src=- shape=3c26ae4f vocab=ebfc4d35
-/
@[simp]
theorem Real.atanh_zero : Real.atanh 0 = 0 := by
  simp only [Real.atanh, add_zero, sub_zero, div_one, Real.log_one, mul_zero]

/-- atanh(-x) = -atanh(x) for |x| < 1
@isnad1 id=eq.1h1v.s4.375a95b02553 from=translated src=- shape=854ff378 vocab=8ebe579d
-/
theorem Real.atanh_neg {x : ℝ} (hx : |x| < 1) : Real.atanh (-x) = -Real.atanh x := by
  simp only [Real.atanh]
  have hlo : -1 < x := (abs_lt.mp hx).1
  have hhi : x < 1 := (abs_lt.mp hx).2
  have hpos1 : 0 < 1 + x := by linarith
  have hpos2 : 0 < 1 - x := by linarith
  have h1 : 1 + -x = 1 - x := by ring
  have h2 : 1 - -x = 1 + x := by ring
  rw [h1, h2]
  rw [Real.log_div (ne_of_gt hpos2) (ne_of_gt hpos1)]
  rw [Real.log_div (ne_of_gt hpos1) (ne_of_gt hpos2)]
  ring

/-- atanh is strictly monotone on (-1, 1)
@isnad1 id=strictmo.0h0v.s4.3fe5326c6cd2 from=translated src=- shape=c86032c6 vocab=0d1aabe9
-/
theorem Real.atanh_strictMonoOn : StrictMonoOn Real.atanh (Set.Ioo (-1) 1) := by
  intro x hx y hy hxy
  simp only [Real.atanh]
  have hx1 : 0 < 1 + x := by linarith [hx.1]
  have hx2 : 0 < 1 - x := by linarith [hx.2]
  have hy1 : 0 < 1 + y := by linarith [hy.1]
  have hy2 : 0 < 1 - y := by linarith [hy.2]
  have hargx : 0 < (1 + x) / (1 - x) := div_pos hx1 hx2
  have hargy : 0 < (1 + y) / (1 - y) := div_pos hy1 hy2
  gcongr 1
  rw [Real.log_lt_log_iff hargx hargy]
  -- Need (1+x)/(1-x) < (1+y)/(1-y) when x < y
  rw [div_lt_div_iff₀ hx2 hy2]
  ring_nf
  linarith

/-- atanh is monotone on (-1, 1): if x ≤ y then atanh x ≤ atanh y
@isnad1 id=le.3h2v.s5.35d168c1462c from=translated src=- shape=a08d7a86 vocab=e1aac04a
-/
theorem Real.atanh_mono {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) (hxy : x ≤ y) :
    Real.atanh x ≤ Real.atanh y := by
  rcases hxy.lt_or_eq with hlt | heq
  · have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨(abs_lt.mp hx).1, (abs_lt.mp hx).2⟩
    have hy' : y ∈ Set.Ioo (-1 : ℝ) 1 := ⟨(abs_lt.mp hy).1, (abs_lt.mp hy).2⟩
    exact le_of_lt (Real.atanh_strictMonoOn hx' hy' hlt)
  · rw [heq]

/-- The error function: erf(x) = (2/√π) ∫₀ˣ exp(-t²) dt.
    Essential for statistical and financial modeling (normal distribution CDF).
    Uses interval integral notation (∫ t in 0..x) which handles negative x correctly. -/
noncomputable def Real.erf (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in (0:ℝ)..x, Real.exp (-(t^2))

/-- The Gaussian function exp(-t²) is always positive. -/
private theorem exp_neg_sq_pos (t : ℝ) : 0 < Real.exp (-(t^2)) :=
  Real.exp_pos _

/-- Helper: The interval integral of a positive function over [0, x] is bounded by the
    half-Gaussian integral when x ≥ 0. -/
private theorem integral_exp_neg_sq_le_half_gaussian (x : ℝ) (hx : 0 ≤ x) :
    ∫ t in (0:ℝ)..x, Real.exp (-(t^2)) ≤ Real.sqrt Real.pi / 2 := by
  have hgauss : ∫ t in Set.Ioi 0, Real.exp (-(1:ℝ) * t^2) = Real.sqrt (Real.pi / 1) / 2 :=
    integral_gaussian_Ioi 1
  simp only [div_one] at hgauss
  -- The interval integral equals the set integral on Ioc when x ≥ 0
  rw [intervalIntegral.integral_of_le hx]
  -- Need: ∫ t in Ioc 0 x, ... ≤ ∫ t in Ioi 0, ...
  -- We have Ioc 0 x ⊆ Ioi 0 for x ≥ 0
  have hint : MeasureTheory.Integrable (fun t => Real.exp (-(1:ℝ) * t^2)) MeasureTheory.volume :=
    integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
  have hint_Ioi : MeasureTheory.Integrable (fun t => Real.exp (-(t^2))) (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have heq : (fun t : ℝ => Real.exp (-(t^2))) = (fun t => Real.exp (-(1:ℝ) * t^2)) := by
      funext t; ring_nf
    rw [heq]
    exact hint.restrict
  calc ∫ t in Set.Ioc 0 x, Real.exp (-(t^2))
      ≤ ∫ t in Set.Ioi 0, Real.exp (-(t^2)) := by
        apply MeasureTheory.setIntegral_mono_set hint_Ioi
        · -- Nonnegativity
          filter_upwards with t using le_of_lt (exp_neg_sq_pos t)
        · -- Set inclusion: Ioc 0 x ⊆ Ioi 0 (need to convert to ae form)
          exact Filter.Eventually.of_forall (fun t ht => Set.Ioc_subset_Ioi_self ht)
      _ = Real.sqrt Real.pi / 2 := by
        have heq : (fun t : ℝ => Real.exp (-(t^2))) = (fun t => Real.exp (-(1:ℝ) * t^2)) := by
          funext t; ring_nf
        rw [heq, hgauss]

/-- Helper: The interval integral of a positive function over [0, x] is nonneg when x ≥ 0. -/
private theorem integral_exp_neg_sq_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ ∫ t in (0:ℝ)..x, Real.exp (-(t^2)) := by
  rw [intervalIntegral.integral_of_le hx]
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc
  intro t _
  exact le_of_lt (exp_neg_sq_pos t)

/-- The error function is bounded above by 1.
@isnad1 id=le.0h1v.s3.a3aa1fb0e4b0 from=translated src=- shape=b14ee516 vocab=7ff87737
-/
theorem Real.erf_le_one (x : ℝ) : Real.erf x ≤ 1 := by
  unfold Real.erf
  by_cases! hx : 0 ≤ x
  · -- Case x ≥ 0: Use that integral is bounded by √π/2
    have h1 : Real.sqrt Real.pi > 0 := Real.sqrt_pos.mpr Real.pi_pos
    have h2 : ∫ t in (0:ℝ)..x, Real.exp (-(t^2)) ≤ Real.sqrt Real.pi / 2 :=
      integral_exp_neg_sq_le_half_gaussian x hx
    calc (2 / Real.sqrt Real.pi) * ∫ t in (0:ℝ)..x, Real.exp (-(t^2))
        ≤ (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) := by
          apply mul_le_mul_of_nonneg_left h2
          exact div_nonneg (by norm_num) (le_of_lt h1)
        _ = 1 := by field_simp
  · -- Case x < 0: Integral is negative (∫ 0..x = -∫ x..0), so erf(x) ≤ 0 ≤ 1
    have h1 : Real.sqrt Real.pi > 0 := Real.sqrt_pos.mpr Real.pi_pos
    have hxle : x ≤ 0 := le_of_lt hx
    -- For x < 0: ∫ 0..x = -∫ x..0, and ∫ x..0 ≥ 0 since we integrate a positive function
    have h2 : ∫ t in (0:ℝ)..x, Real.exp (-(t^2)) ≤ 0 := by
      rw [intervalIntegral.integral_symm]
      apply neg_nonpos.mpr
      -- ∫ x..0 for x < 0 means integrating from x to 0, i.e., over [x, 0]
      rw [intervalIntegral.integral_of_le hxle]
      apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      intro t _
      exact le_of_lt (exp_neg_sq_pos t)
    calc (2 / Real.sqrt Real.pi) * ∫ t in (0:ℝ)..x, Real.exp (-(t^2))
        ≤ (2 / Real.sqrt Real.pi) * 0 := by
          apply mul_le_mul_of_nonneg_left h2
          exact div_nonneg (by norm_num) (le_of_lt h1)
        _ = 0 := by ring
        _ ≤ 1 := by norm_num

/-- Helper: The integral ∫ x..0 exp(-t²) for x ≤ 0 is bounded by √π/2. -/
private theorem integral_exp_neg_sq_le_half_gaussian' (x : ℝ) (hx : x ≤ 0) :
    ∫ t in x..(0:ℝ), Real.exp (-(t^2)) ≤ Real.sqrt Real.pi / 2 := by
  -- Use substitution: the function is even, so ∫ x..0 = ∫ 0..-x
  have heq : ∀ t : ℝ, Real.exp (-(t^2)) = Real.exp (-((-t)^2)) := fun t => by ring_nf
  have hsub : ∫ t in x..(0:ℝ), Real.exp (-(t^2)) = ∫ t in (0:ℝ)..(-x), Real.exp (-(t^2)) := by
    calc ∫ t in x..(0:ℝ), Real.exp (-(t^2))
        = ∫ t in x..(0:ℝ), Real.exp (-((-t)^2)) := by simp only [neg_sq]
      _ = ∫ t in (-0:ℝ)..(-x), Real.exp (-(t^2)) := by
          rw [intervalIntegral.integral_comp_neg (fun t => Real.exp (-(t^2)))]
      _ = ∫ t in (0:ℝ)..(-x), Real.exp (-(t^2)) := by simp only [neg_zero]
  rw [hsub]
  exact integral_exp_neg_sq_le_half_gaussian (-x) (by linarith)

/-- The error function is bounded below by -1.
@isnad1 id=le.0h1v.s4.a627f0925a84 from=translated src=- shape=18c18b5c vocab=4b0b848d
-/
theorem Real.neg_one_le_erf (x : ℝ) : -1 ≤ Real.erf x := by
  unfold Real.erf
  by_cases! hx : 0 ≤ x
  · -- Case x ≥ 0: Integral is nonneg, so erf(x) ≥ 0 > -1
    have h1 : Real.sqrt Real.pi > 0 := Real.sqrt_pos.mpr Real.pi_pos
    have h2 : 0 ≤ ∫ t in (0:ℝ)..x, Real.exp (-(t^2)) := integral_exp_neg_sq_nonneg x hx
    have h3 : 0 ≤ (2 / Real.sqrt Real.pi) * ∫ t in (0:ℝ)..x, Real.exp (-(t^2)) := by
      apply mul_nonneg
      · exact div_nonneg (by norm_num) (le_of_lt h1)
      · exact h2
    linarith
  · -- Case x < 0: ∫ 0..x = -∫ x..0, and ∫ x..0 ≤ √π/2
    have h1 : Real.sqrt Real.pi > 0 := Real.sqrt_pos.mpr Real.pi_pos
    have hxle : x ≤ 0 := le_of_lt hx
    -- ∫ 0..x = -∫ x..0
    rw [intervalIntegral.integral_symm]
    have h2 : ∫ t in x..(0:ℝ), Real.exp (-(t^2)) ≤ Real.sqrt Real.pi / 2 :=
      integral_exp_neg_sq_le_half_gaussian' x hxle
    -- Need: -1 ≤ (2/√π) * (-∫ x..0 f)
    -- i.e., -1 ≤ -(2/√π) * ∫ x..0 f
    -- i.e., (2/√π) * ∫ x..0 f ≤ 1
    -- From h2: ∫ x..0 f ≤ √π/2, so (2/√π) * ∫ x..0 f ≤ (2/√π) * (√π/2) = 1
    have h3 : (2 / Real.sqrt Real.pi) * ∫ t in x..(0:ℝ), Real.exp (-(t^2)) ≤ 1 := by
      calc (2 / Real.sqrt Real.pi) * ∫ t in x..(0:ℝ), Real.exp (-(t^2))
          ≤ (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) := by
            apply mul_le_mul_of_nonneg_left h2
            exact div_nonneg (by norm_num) (le_of_lt h1)
          _ = 1 := by field_simp
    linarith

/-- The error function always lies in `[-1, 1]`.
@isnad1 id=mem.0h1v.s4.3cff531534f6 from=translated src=- shape=79c0dbe3 vocab=b747eaef
-/
theorem Real.erf_mem_Icc (x : ℝ) : Real.erf x ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨Real.neg_one_le_erf x, Real.erf_le_one x⟩

/-- The normalized sinc function always lies in `[-1, 1]`.
@isnad1 id=mem.0h1v.s4.57e52de07519 from=translated src=- shape=79c0dbe3 vocab=b1140b28
-/
theorem Real.sinc_mem_Icc (x : ℝ) : Real.sinc x ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨Real.neg_one_le_sinc x, Real.sinc_le_one x⟩

/-- Named mathematical constants with known interval bounds.
    Adding a new constant (e.g., Catalan's) only requires extending this enum
    and its lookup tables — zero evaluator files need updating. -/
inductive MathConst where
  | pi
  | eulerMascheroni
  deriving Repr, DecidableEq, Inhabited

/-- The real value of a named mathematical constant. -/
noncomputable def MathConst.toReal : MathConst → ℝ
  | .pi => Real.pi
  | .eulerMascheroni => Real.eulerMascheroniConstant

/-- Float approximation for heuristic evaluation (unverified). -/
def MathConst.toFloat : MathConst → Float
  | .pi => 3.141592653589793
  | .eulerMascheroni => 0.5772156649015329

/-- Rational approximation for display/debugging (unverified). -/
def MathConst.toRatApprox : MathConst → ℚ
  | .pi => 157 / 50
  | .eulerMascheroni => 577 / 1000

/-- Unified AST for real-valued expressions. -/
inductive Expr where
  /-- Rational constant -/
  | const (q : ℚ)
  /-- Variable with de Bruijn-style index -/
  | var (idx : Nat)
  /-- Addition -/
  | add (e₁ e₂ : Expr)
  /-- Multiplication -/
  | mul (e₁ e₂ : Expr)
  /-- Negation -/
  | neg (e : Expr)
  /-- Multiplicative inverse (partial: undefined at 0) -/
  | inv (e : Expr)
  /-- Exponential function -/
  | exp (e : Expr)
  /-- Sine function -/
  | sin (e : Expr)
  /-- Cosine function -/
  | cos (e : Expr)
  /-- Natural logarithm (partial: undefined for x ≤ 0) -/
  | log (e : Expr)
  /-- Arctangent function -/
  | atan (e : Expr)
  /-- Inverse hyperbolic sine (arsinh) -/
  | arsinh (e : Expr)
  /-- Inverse hyperbolic tangent (partial: undefined for |x| ≥ 1) -/
  | atanh (e : Expr)
  /-- Sinc function: sinc(x) = sin(x)/x for x ≠ 0, sinc(0) = 1 -/
  | sinc (e : Expr)
  /-- Error function: erf(x) = (2/√π) ∫₀ˣ exp(-t²) dt -/
  | erf (e : Expr)
  /-- Hyperbolic sine: sinh(x) = (exp(x) - exp(-x)) / 2 -/
  | sinh (e : Expr)
  /-- Hyperbolic cosine: cosh(x) = (exp(x) + exp(-x)) / 2 -/
  | cosh (e : Expr)
  /-- Hyperbolic tangent: tanh(x) = sinh(x) / cosh(x) ∈ (-1, 1) -/
  | tanh (e : Expr)
  /-- Square root (partial: undefined for x < 0) -/
  | sqrt (e : Expr)
  /-- A named mathematical constant (π, γ, …) looked up from a table. -/
  | namedConst (c : MathConst)
  deriving Repr, DecidableEq, Inhabited

namespace Expr

/-- Subtraction as a derived operation -/
def sub (e₁ e₂ : Expr) : Expr := add e₁ (neg e₂)

/-- Division as a derived operation -/
def div (e₁ e₂ : Expr) : Expr := mul e₁ (inv e₂)

/-- Integer power (non-negative exponent) -/
def pow (e : Expr) : Nat → Expr
  | 0 => const 1
  | n + 1 => mul e (pow e n)

/-- Absolute value as a derived operation: |x| = sqrt(x²)
    This gives correct results for all real x (except at 0 for interval purposes) -/
def abs (e : Expr) : Expr := sqrt (mul e e)

/-- Evaluate an expression given a variable assignment ρ : Nat → ℝ -/
noncomputable def eval (ρ : Nat → ℝ) : Expr → ℝ
  | const q => (q : ℝ)
  | var idx => ρ idx
  | add e₁ e₂ => eval ρ e₁ + eval ρ e₂
  | mul e₁ e₂ => eval ρ e₁ * eval ρ e₂
  | neg e => -(eval ρ e)
  | inv e => (eval ρ e)⁻¹
  | exp e => Real.exp (eval ρ e)
  | sin e => Real.sin (eval ρ e)
  | cos e => Real.cos (eval ρ e)
  | log e => Real.log (eval ρ e)
  | atan e => Real.arctan (eval ρ e)
  | arsinh e => Real.arsinh (eval ρ e)
  | atanh e => Real.atanh (eval ρ e)
  | sinc e => Real.sinc (eval ρ e)
  | erf e => Real.erf (eval ρ e)
  | sinh e => Real.sinh (eval ρ e)
  | cosh e => Real.cosh (eval ρ e)
  | tanh e => Real.tanh (eval ρ e)
  | sqrt e => Real.sqrt (eval ρ e)
  | namedConst c => c.toReal

/-- Update variable assignment at a specific index -/
def updateVar (ρ : Nat → ℝ) (idx : Nat) (x : ℝ) : Nat → ℝ :=
  fun i => if i = idx then x else ρ i

scoped notation ρ "[" idx " ↦ " x "]" => updateVar ρ idx x

/--
@isnad1 id=eq.0h3v.s4.6b378b4974c8 from=translated src=- shape=f46a3c01 vocab=1232586c
-/
@[simp]
theorem updateVar_same (ρ : Nat → ℝ) (idx : Nat) (x : ℝ) :
    updateVar ρ idx x idx = x := by simp [updateVar]

/--
@isnad1 id=eq.1h4v.s4.67c59ac736d3 from=translated src=- shape=22d521a2 vocab=1232586c
-/
@[simp]
theorem updateVar_other (ρ : Nat → ℝ) (idx i : Nat) (x : ℝ) (h : i ≠ idx) :
    updateVar ρ idx x i = ρ i := by simp [updateVar, h]

/--
@isnad1 id=eq.0h2v.s4.ee26c6d59778 from=translated src=- shape=dd32f0ae vocab=1232586c
-/
theorem updateVar_self (ρ : Nat → ℝ) (idx : Nat) :
    updateVar ρ idx (ρ idx) = ρ := by
  funext i
  simp only [updateVar]
  split_ifs with h
  · rw [h]
  · rfl

/-- Evaluate `e` as a scalar function of variable `idx`, with all other
    variables fixed by `ρ`. This represents the map t ↦ eval ρ[idx ↦ t] e. -/
noncomputable abbrev evalAlong (e : Expr) (ρ : Nat → ℝ) (idx : Nat) : ℝ → ℝ :=
  fun t => eval (updateVar ρ idx t) e

/-- The set of free variable indices in an expression -/
def freeVars : Expr → Finset Nat
  | const _ => ∅
  | var idx => {idx}
  | add e₁ e₂ => freeVars e₁ ∪ freeVars e₂
  | mul e₁ e₂ => freeVars e₁ ∪ freeVars e₂
  | neg e => freeVars e
  | inv e => freeVars e
  | exp e => freeVars e
  | sin e => freeVars e
  | cos e => freeVars e
  | log e => freeVars e
  | atan e => freeVars e
  | arsinh e => freeVars e
  | atanh e => freeVars e
  | sinc e => freeVars e
  | erf e => freeVars e
  | sinh e => freeVars e
  | cosh e => freeVars e
  | tanh e => freeVars e
  | sqrt e => freeVars e
  | namedConst _ => ∅

/-- An expression is closed if it has no free variables -/
def isClosed (e : Expr) : Prop := freeVars e = ∅

-- Basic lemmas about eval

/--
@isnad1 id=eq.0h2v.s4.745ad8112c1f from=translated src=- shape=d817fcc1 vocab=21ec4052
-/
@[simp]
theorem eval_const (ρ : Nat → ℝ) (q : ℚ) : eval ρ (const q) = q := rfl

/--
@isnad1 id=eq.0h2v.s3.17af5ca836dc from=translated src=- shape=02ea90bc vocab=9eb71465
-/
@[simp]
theorem eval_var (ρ : Nat → ℝ) (idx : Nat) : eval ρ (var idx) = ρ idx := rfl

/--
@isnad1 id=eq.0h3v.s4.069c0a492abb from=translated src=- shape=0a17062c vocab=bd25ec4d
-/
@[simp]
theorem eval_add (ρ : Nat → ℝ) (e₁ e₂ : Expr) :
    eval ρ (add e₁ e₂) = eval ρ e₁ + eval ρ e₂ := rfl

/--
@isnad1 id=eq.0h3v.s4.456dab748fd8 from=translated src=- shape=0a17062c vocab=c6f484ca
-/
@[simp]
theorem eval_mul (ρ : Nat → ℝ) (e₁ e₂ : Expr) :
    eval ρ (mul e₁ e₂) = eval ρ e₁ * eval ρ e₂ := rfl

/--
@isnad1 id=eq.0h2v.s4.c3f84ad16a92 from=translated src=- shape=07892c53 vocab=e7de0e13
-/
@[simp]
theorem eval_neg (ρ : Nat → ℝ) (e : Expr) : eval ρ (neg e) = -(eval ρ e) := rfl

/--
@isnad1 id=eq.0h2v.s4.6fb88c0d6da6 from=translated src=- shape=07892c53 vocab=0c502a9f
-/
@[simp]
theorem eval_inv (ρ : Nat → ℝ) (e : Expr) : eval ρ (inv e) = (eval ρ e)⁻¹ := rfl

/--
@isnad1 id=eq.0h2v.s4.5592f30aeeff from=translated src=- shape=06185ba2 vocab=ed2db389
-/
@[simp]
theorem eval_exp (ρ : Nat → ℝ) (e : Expr) : eval ρ (exp e) = Real.exp (eval ρ e) := rfl

/--
@isnad1 id=eq.0h2v.s4.9f56fea0d62b from=translated src=- shape=06185ba2 vocab=81a224c4
-/
@[simp]
theorem eval_sin (ρ : Nat → ℝ) (e : Expr) : eval ρ (sin e) = Real.sin (eval ρ e) := rfl

/--
@isnad1 id=eq.0h2v.s4.25a1a8c654b0 from=translated src=- shape=06185ba2 vocab=917e9366
-/
@[simp]
theorem eval_cos (ρ : Nat → ℝ) (e : Expr) : eval ρ (cos e) = Real.cos (eval ρ e) := rfl

/--
@isnad1 id=eq.0h2v.s4.b5cdff01b51d from=translated src=- shape=06185ba2 vocab=5f45c79c
-/
@[simp]
theorem eval_log (ρ : Nat → ℝ) (e : Expr) : eval ρ (log e) = Real.log (eval ρ e) := rfl

/--
@isnad1 id=eq.0h2v.s4.a135275db0e7 from=translated src=- shape=06185ba2 vocab=699880ba
-/
@[simp]
theorem eval_atan (ρ : Nat → ℝ) (e : Expr) : eval ρ (atan e) = Real.arctan (eval ρ e) := rfl

/--
@isnad1 id=eq.0h2v.s4.15fc23b2c608 from=translated src=- shape=06185ba2 vocab=454136a3
-/
@[simp]
theorem eval_arsinh (ρ : Nat → ℝ) (e : Expr) : eval ρ (arsinh e) = Real.arsinh (eval ρ e) := rfl

/--
@isnad1 id=eq.0h2v.s4.1ef5978159ae from=translated src=- shape=06185ba2 vocab=2c67d645
-/
@[simp]
theorem eval_atanh (ρ : Nat → ℝ) (e : Expr) : eval ρ (atanh e) = Real.atanh (eval ρ e) := rfl

/--
@isnad1 id=eq.0h2v.s4.3eb9ed4ed3f3 from=translated src=- shape=06185ba2 vocab=9a242563
-/
@[simp]
theorem eval_sinc (ρ : Nat → ℝ) (e : Expr) : eval ρ (sinc e) = Real.sinc (eval ρ e) := rfl

/--
@isnad1 id=eq.0h2v.s4.7900e24db554 from=translated src=- shape=06185ba2 vocab=1ed68a1c
-/
@[simp]
theorem eval_erf (ρ : Nat → ℝ) (e : Expr) : eval ρ (erf e) = Real.erf (eval ρ e) := rfl

/--
@isnad1 id=eq.0h2v.s4.25dbc0c9bafb from=translated src=- shape=06185ba2 vocab=4a3af38b
-/
@[simp]
theorem eval_sinh (ρ : Nat → ℝ) (e : Expr) : eval ρ (sinh e) = Real.sinh (eval ρ e) := rfl

/--
@isnad1 id=eq.0h2v.s4.dd1a1bbc9022 from=translated src=- shape=06185ba2 vocab=f030dc40
-/
@[simp]
theorem eval_cosh (ρ : Nat → ℝ) (e : Expr) : eval ρ (cosh e) = Real.cosh (eval ρ e) := rfl

/--
@isnad1 id=eq.0h2v.s4.4645201a5a09 from=translated src=- shape=06185ba2 vocab=5217dcb4
-/
@[simp]
theorem eval_tanh (ρ : Nat → ℝ) (e : Expr) : eval ρ (tanh e) = Real.tanh (eval ρ e) := rfl

/--
@isnad1 id=eq.0h2v.s4.e7ff00723432 from=translated src=- shape=06185ba2 vocab=a50f7a81
-/
@[simp]
theorem eval_sqrt (ρ : Nat → ℝ) (e : Expr) : eval ρ (sqrt e) = Real.sqrt (eval ρ e) := rfl

/--
@isnad1 id=eq.0h2v.s3.6b010edb9ce5 from=translated src=- shape=f0c8d852 vocab=61669826
-/
@[simp]
theorem eval_namedConst (ρ : Nat → ℝ) (c : MathConst) :
    eval ρ (namedConst c) = c.toReal := rfl

/--
@isnad1 id=eq.0h1v.s3.c199f56dd6cf from=translated src=- shape=b6cbb328 vocab=5c63e2e7
-/
theorem eval_eulerMascheroni (ρ : Nat → ℝ) :
    eval ρ (namedConst .eulerMascheroni) = Real.eulerMascheroniConstant := rfl

/--
@isnad1 id=eq.0h3v.s4.08248a35797d from=translated src=- shape=0a17062c vocab=45d7ca16
-/
@[simp]
theorem eval_sub (ρ : Nat → ℝ) (e₁ e₂ : Expr) :
    eval ρ (sub e₁ e₂) = eval ρ e₁ - eval ρ e₂ := by simp [sub, sub_eq_add_neg]

/--
@isnad1 id=eq.0h3v.s4.3c94467bf1eb from=translated src=- shape=0a17062c vocab=dc653f96
-/
@[simp]
theorem eval_div (ρ : Nat → ℝ) (e₁ e₂ : Expr) :
    eval ρ (div e₁ e₂) = eval ρ e₁ / eval ρ e₂ := by simp [div, div_eq_mul_inv]

/--
@isnad1 id=eq.0h3v.s4.86e37f4cc5cb from=translated src=- shape=1eb8cefd vocab=1576a001
-/
@[simp]
theorem eval_pow (ρ : Nat → ℝ) (e : Expr) (n : ℕ) :
    eval ρ (pow e n) = (eval ρ e) ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp only [pow, eval_mul, ih, pow_succ']

/-- Evaluation of abs for any argument: |x| = sqrt(x²)
@isnad1 id=eq.0h2v.s4.615d60a79673 from=translated src=- shape=07892c53 vocab=eae45334
-/
theorem eval_abs (ρ : Nat → ℝ) (e : Expr) :
    eval ρ (abs e) = |eval ρ e| := by
  simp only [abs, eval_sqrt, eval_mul, ← sq, Real.sqrt_sq_eq_abs]

/-- Evaluation of sqrt(x * x) = |x| (unfolded form of `abs`).
@isnad1 id=eq.0h2v.s4.0f8eedb7f7a8 from=translated src=- shape=3b95c81b vocab=54758b32
-/
theorem eval_sqrt_mul_self_eq_abs (ρ : Nat → ℝ) (e : Expr) :
    eval ρ (sqrt (mul e e)) = |eval ρ e| := eval_abs ρ e

/-- `√(x * x) = |x|` — LeanCert-namespaced alias of `Real.sqrt_mul_self_eq_abs`.
@isnad1 id=eq.0h1v.s4.5334b82ecc24 from=translated src=- shape=0cd1df8f vocab=047fd1c5
-/
theorem sqrt_mul_self_eq_abs (x : ℝ) : Real.sqrt (x * x) = |x| :=
  Real.sqrt_mul_self_eq_abs x

/-- For positive x, sqrt(x²) = x
@isnad1 id=eq.1h2v.s4.5efad2385d24 from=translated src=- shape=13ad2e62 vocab=8b7a0e09
-/
theorem eval_sqrt_sq_of_pos (ρ : Nat → ℝ) (e : Expr) (hpos : 0 < eval ρ e) :
    eval ρ (sqrt (mul e e)) = eval ρ e := by
  simp only [eval_sqrt, eval_mul, ← sq, Real.sqrt_sq (le_of_lt hpos)]

/-- Abs correctly computes absolute value for positive inputs
@isnad1 id=eq.1h2v.s4.7e908a059453 from=translated src=- shape=c980dcf4 vocab=bc7f4b56
-/
theorem eval_abs_of_pos (ρ : Nat → ℝ) (e : Expr) (hpos : 0 < eval ρ e) :
    eval ρ (abs e) = eval ρ e := by
  rw [eval_abs, abs_of_pos hpos]

/-- Abs correctly computes absolute value for negative inputs
@isnad1 id=eq.1h2v.s4.c56fd20c9e65 from=translated src=- shape=e31995ff vocab=871a4560
-/
theorem eval_abs_of_neg (ρ : Nat → ℝ) (e : Expr) (hneg : eval ρ e < 0) :
    eval ρ (abs e) = -(eval ρ e) := by
  rw [eval_abs, abs_of_neg hneg]

-- Lemmas about evalAlong

/--
@isnad1 id=eq.0h4v.s4.c25aaf9d6b8c from=translated src=- shape=bae81796 vocab=a5614301
-/
theorem evalAlong_eq (e : Expr) (ρ : Nat → ℝ) (idx : Nat) (t : ℝ) :
    evalAlong e ρ idx t = eval (ρ[idx ↦ t]) e := rfl

/--
@isnad1 id=eq.0h3v.s4.5987045ff201 from=translated src=- shape=f9132f05 vocab=71915483
-/
theorem evalAlong_at_ρ (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong e ρ idx (ρ idx) = eval ρ e := by
  simp only [evalAlong, updateVar_self]

/-- evalAlong for a constant is constant
@isnad1 id=eq.0h3v.s4.0e42fba5ba7c from=translated src=- shape=61bdf578 vocab=b04500f9
-/
theorem evalAlong_const' (ρ : Nat → ℝ) (idx : Nat) (q : ℚ) :
    evalAlong (const q) ρ idx = fun _ => (q : ℝ) := rfl

/-- evalAlong for the active variable is the identity
@isnad1 id=eq.0h2v.s4.810eb8948277 from=translated src=- shape=a8040cbf vocab=344fb4aa
-/
theorem evalAlong_var_active (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (var idx) ρ idx = id := by
  funext t
  simp only [evalAlong, eval_var, updateVar_same, id_eq]

/-- evalAlong for a passive variable is constant
@isnad1 id=eq.1h3v.s4.e887fac3eaa6 from=translated src=- shape=52fd0de7 vocab=4179968d
-/
theorem evalAlong_var_passive (ρ : Nat → ℝ) (idx i : Nat) (h : i ≠ idx) :
    evalAlong (var i) ρ idx = fun _ => ρ i := by
  funext t
  simp only [evalAlong, eval_var, updateVar_other _ _ _ _ h]

/-- evalAlong for addition
@isnad1 id=eq.0h4v.s5.7b5d41b3ecf9 from=translated src=- shape=f7300076 vocab=6efdfbe6
-/
theorem evalAlong_add (e₁ e₂ : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (add e₁ e₂) ρ idx = fun t => evalAlong e₁ ρ idx t + evalAlong e₂ ρ idx t := by
  funext t
  simp only [evalAlong, eval_add]

/-- evalAlong for addition (Pi form for compatibility with deriv_add)
@isnad1 id=eq.0h4v.s5.b108b493fdad from=translated src=- shape=0b195cf0 vocab=6efdfbe6
-/
theorem evalAlong_add_pi (e₁ e₂ : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (add e₁ e₂) ρ idx = evalAlong e₁ ρ idx + evalAlong e₂ ρ idx := rfl

/-- evalAlong for multiplication
@isnad1 id=eq.0h4v.s5.2e8b7f519469 from=translated src=- shape=f7300076 vocab=e15681b8
-/
theorem evalAlong_mul (e₁ e₂ : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (mul e₁ e₂) ρ idx = fun t => evalAlong e₁ ρ idx t * evalAlong e₂ ρ idx t := by
  funext t
  simp only [evalAlong, eval_mul]

/-- evalAlong for multiplication (Pi form for compatibility with deriv_mul)
@isnad1 id=eq.0h4v.s5.5639e4a52295 from=translated src=- shape=0b195cf0 vocab=e15681b8
-/
theorem evalAlong_mul_pi (e₁ e₂ : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (mul e₁ e₂) ρ idx = evalAlong e₁ ρ idx * evalAlong e₂ ρ idx := rfl

/-- evalAlong for negation
@isnad1 id=eq.0h3v.s4.b7415bab84da from=translated src=- shape=985c21bd vocab=80b68549
-/
theorem evalAlong_neg (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (neg e) ρ idx = fun t => -(evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_neg]

/-- evalAlong for negation (Pi form for compatibility with deriv.neg)
@isnad1 id=eq.0h3v.s5.902ed46d9c66 from=translated src=- shape=2390a6e7 vocab=80b68549
-/
theorem evalAlong_neg_pi (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (neg e) ρ idx = -evalAlong e ρ idx := rfl

/-- evalAlong for sin
@isnad1 id=eq.0h3v.s4.302bd97fb564 from=translated src=- shape=9896c634 vocab=3be22ffe
-/
theorem evalAlong_sin (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (sin e) ρ idx = fun t => Real.sin (evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_sin]

/-- evalAlong for cos
@isnad1 id=eq.0h3v.s4.d8118043cad2 from=translated src=- shape=9896c634 vocab=c7faad5f
-/
theorem evalAlong_cos (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (cos e) ρ idx = fun t => Real.cos (evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_cos]

/-- evalAlong for exp
@isnad1 id=eq.0h3v.s4.b09500d85569 from=translated src=- shape=9896c634 vocab=ec6c3d9a
-/
theorem evalAlong_exp (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (exp e) ρ idx = fun t => Real.exp (evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_exp]

/-- evalAlong for inv
@isnad1 id=eq.0h3v.s4.2186e2bfc008 from=translated src=- shape=985c21bd vocab=e7621b9b
-/
theorem evalAlong_inv (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (inv e) ρ idx = fun t => (evalAlong e ρ idx t)⁻¹ := by
  funext t
  simp only [evalAlong, eval_inv]

/-- evalAlong for log
@isnad1 id=eq.0h3v.s4.c712f3800d4f from=translated src=- shape=9896c634 vocab=e977112d
-/
theorem evalAlong_log (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (log e) ρ idx = fun t => Real.log (evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_log]

/-- evalAlong for atan
@isnad1 id=eq.0h3v.s4.c2448d62d103 from=translated src=- shape=9896c634 vocab=248bf03f
-/
theorem evalAlong_atan (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (atan e) ρ idx = fun t => Real.arctan (evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_atan]

/-- evalAlong for arsinh
@isnad1 id=eq.0h3v.s4.7582fb01ee2f from=translated src=- shape=9896c634 vocab=da74a63d
-/
theorem evalAlong_arsinh (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (arsinh e) ρ idx = fun t => Real.arsinh (evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_arsinh]

/-- evalAlong for atanh
@isnad1 id=eq.0h3v.s4.25bfe9682294 from=translated src=- shape=9896c634 vocab=7c9f1fc3
-/
theorem evalAlong_atanh (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (atanh e) ρ idx = fun t => Real.atanh (evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_atanh]

/-! ## Single-variable expressions

For 1D optimization and root finding, we often work with expressions that only use variable 0.
These lemmas establish that such expressions can be evaluated equivalently with different
environment representations.
-/

/-- Check if an expression only uses variable 0 (computable) -/
def usesOnlyVar0 : Expr → Bool
  | const _ => true
  | var n => n == 0
  | add e₁ e₂ => e₁.usesOnlyVar0 && e₂.usesOnlyVar0
  | mul e₁ e₂ => e₁.usesOnlyVar0 && e₂.usesOnlyVar0
  | neg e => e.usesOnlyVar0
  | inv e => e.usesOnlyVar0
  | exp e => e.usesOnlyVar0
  | sin e => e.usesOnlyVar0
  | cos e => e.usesOnlyVar0
  | log e => e.usesOnlyVar0
  | atan e => e.usesOnlyVar0
  | arsinh e => e.usesOnlyVar0
  | atanh e => e.usesOnlyVar0
  | sinc e => e.usesOnlyVar0
  | erf e => e.usesOnlyVar0
  | sinh e => e.usesOnlyVar0
  | cosh e => e.usesOnlyVar0
  | tanh e => e.usesOnlyVar0
  | sqrt e => e.usesOnlyVar0
  | namedConst _ => true

/-- If two environments agree on variable 0, then a usesOnlyVar0 expression evaluates the same
@isnad1 id=eq.2h3v.s5.dc7097472e51 from=translated src=- shape=f23e3dd4 vocab=d1bd89ae
-/
theorem eval_usesOnlyVar0_eq (e : Expr) (he : e.usesOnlyVar0 = true)
    (ρ₁ ρ₂ : Nat → ℝ) (h0 : ρ₁ 0 = ρ₂ 0) :
    eval ρ₁ e = eval ρ₂ e := by
  induction e with
  | const q => rfl
  | var n =>
    simp only [usesOnlyVar0, beq_iff_eq] at he
    simp only [eval_var, he, h0]
  | add e₁ e₂ ih1 ih2 =>
    simp only [usesOnlyVar0, Bool.and_eq_true] at he
    simp only [eval_add, ih1 he.1, ih2 he.2]
  | mul e₁ e₂ ih1 ih2 =>
    simp only [usesOnlyVar0, Bool.and_eq_true] at he
    simp only [eval_mul, ih1 he.1, ih2 he.2]
  | neg e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_neg, ih he]
  | inv e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_inv, ih he]
  | exp e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_exp, ih he]
  | sin e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_sin, ih he]
  | cos e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_cos, ih he]
  | log e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_log, ih he]
  | atan e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_atan, ih he]
  | arsinh e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_arsinh, ih he]
  | atanh e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_atanh, ih he]
  | sinc e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_sinc, ih he]
  | erf e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_erf, ih he]
  | sinh e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_sinh, ih he]
  | cosh e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_cosh, ih he]
  | tanh e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_tanh, ih he]
  | sqrt e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_sqrt, ih he]
  | namedConst _ => rfl

/-- For single-variable expressions, `fun n => if n = 0 then x else 0` and `fun _ => x`
    give the same evaluation result.
@isnad1 id=eq.1h2v.s5.69cf85e06590 from=translated src=- shape=a6017fae vocab=5255ee95
-/
theorem eval_1d_equiv (e : Expr) (he : e.usesOnlyVar0 = true) (x : ℝ) :
    eval (fun n => if n = 0 then x else 0) e = eval (fun _ => x) e := by
  apply eval_usesOnlyVar0_eq e he
  simp

/-- Alternative: evaluation with Box-style environment equals 1D evaluation
@isnad1 id=eq.1h2v.s5.69cf85e06590 from=translated src=- shape=a6017fae vocab=5255ee95
-/
theorem eval_box1d_eq_eval1d (e : Expr) (he : e.usesOnlyVar0 = true) (x : ℝ) :
    eval (fun n => if n = 0 then x else 0) e = eval (fun _ => x) e :=
  eval_1d_equiv e he x

end Expr

end LeanCert.Core
-- Tengoku: 1 notation(s) of this module made scoped so they do not change other libraries (generated)
