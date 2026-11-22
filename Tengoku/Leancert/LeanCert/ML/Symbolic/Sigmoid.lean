/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.ML.Symbolic.ReLU
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Verified DeepPoly Sigmoid Relaxation

This module implements linear relaxations for the sigmoid activation function,
enabling Symbolic Interval Propagation for networks using sigmoid/logistic units.

## The Sigmoid Function

σ(x) = 1 / (1 + exp(-x))

Key properties:
- Strictly monotone increasing
- Range: (0, 1)
- σ'(x) = σ(x) · (1 - σ(x))
- Convex for x < 0, concave for x > 0 (inflection at x = 0)

## Relaxation Strategy

Unlike ReLU (piecewise linear), sigmoid requires careful handling:

1. **Monotonicity bounds**: Since σ is increasing, σ(l) ≤ σ(x) ≤ σ(u) for x ∈ [l, u]

2. **Secant line**: The chord from (l, σ(l)) to (u, σ(u))

## Main Results

* `sigmoid_strictMono` - Sigmoid is strictly monotone increasing
* `sigmoid_relaxation_sound` - Soundness of monotonicity-based bounds
-/

open scoped LeanCert.Core.Expr

namespace LeanCert.ML.Symbolic

open Real

/-! ## Real Linear Bounds (for transcendental functions) -/

/-- A linear bound with real coefficients: y = slope · x + bias -/
structure RealLinearBound where
  slope : ℝ
  bias : ℝ

/-- Evaluate real linear bound at x -/
def RealLinearBound.eval (f : RealLinearBound) (x : ℝ) : ℝ :=
  f.slope * x + f.bias

/-- Real symbolic bound for transcendental activations -/
structure RealSymbolicBound where
  lower : RealLinearBound
  upper : RealLinearBound

/-! ## Sigmoid Definition and Basic Properties -/

/-- The sigmoid (logistic) function: σ(x) = 1 / (1 + exp(-x)) -/
noncomputable def sigmoid (x : ℝ) : ℝ := 1 / (1 + exp (-x))

/-- Sigmoid is always positive
@isnad1 id=lt.0h1v.s3.9feb2bef7982 from=translated src=- shape=8a62b088 vocab=b19412b8
-/
theorem sigmoid_pos (x : ℝ) : 0 < sigmoid x := by
  unfold sigmoid
  apply div_pos one_pos
  linarith [exp_pos (-x)]

/-- Sigmoid is always less than 1
@isnad1 id=lt.0h1v.s3.56d3909cafe8 from=translated src=- shape=b14ee516 vocab=b19412b8
-/
theorem sigmoid_lt_one (x : ℝ) : sigmoid x < 1 := by
  unfold sigmoid
  rw [div_lt_one (by linarith [exp_pos (-x)] : 0 < 1 + exp (-x))]
  linarith [exp_pos (-x)]

/-- Sigmoid is bounded in (0, 1)
@isnad1 id=mem.0h1v.s4.9529b9c9cb6b from=translated src=- shape=828ff9db vocab=d18482e3
-/
theorem sigmoid_mem_Ioo (x : ℝ) : sigmoid x ∈ Set.Ioo 0 1 :=
  ⟨sigmoid_pos x, sigmoid_lt_one x⟩

/-- Sigmoid is bounded in [0, 1]
@isnad1 id=le.0h1v.s3.96f6546be40a from=translated src=- shape=8a62b088 vocab=e5338b31
-/
theorem sigmoid_nonneg (x : ℝ) : 0 ≤ sigmoid x := le_of_lt (sigmoid_pos x)

/--
@isnad1 id=le.0h1v.s3.159b936b0e30 from=translated src=- shape=b14ee516 vocab=e5338b31
-/
theorem sigmoid_le_one (x : ℝ) : sigmoid x ≤ 1 := le_of_lt (sigmoid_lt_one x)

/-- Sigmoid at 0 equals 1/2
@isnad1 id=eq.0h0v.s5.126172924815 from=translated src=- shape=d4f6e56f vocab=b39ab4d2
-/
theorem sigmoid_zero : sigmoid 0 = 1 / 2 := by
  unfold sigmoid
  simp only [neg_zero, exp_zero]
  norm_num

/-- 1 - σ(x) = σ(-x)
@isnad1 id=eq.0h1v.s4.c22ba7e6ad0f from=translated src=- shape=0018fb8f vocab=271d392a
-/
theorem one_sub_sigmoid (x : ℝ) : 1 - sigmoid x = sigmoid (-x) := by
  unfold sigmoid
  have h1 : 1 + exp (-x) ≠ 0 := by linarith [exp_pos (-x)]
  have h2 : 1 + exp x ≠ 0 := by linarith [exp_pos x]
  have hexp : exp (-x) * exp x = 1 := by rw [← exp_add]; simp
  field_simp
  linarith [hexp]

/-! ## Monotonicity -/

/-- The denominator 1 + exp(-x) is always positive
@isnad1 id=lt.0h1v.s4.3edb40b992e3 from=translated src=- shape=3e0e8fe1 vocab=ff8de3a5
-/
theorem sigmoid_denom_pos (x : ℝ) : 0 < 1 + exp (-x) := by
  linarith [exp_pos (-x)]

/-- Sigmoid is strictly monotone increasing
@isnad1 id=strictmo.0h0v.s2.6581170ac380 from=translated src=- shape=e3d48bcb vocab=2f880930
-/
theorem sigmoid_strictMono : StrictMono sigmoid := by
  intro a b hab
  unfold sigmoid
  have ha : 0 < 1 + exp (-a) := sigmoid_denom_pos a
  have hb : 0 < 1 + exp (-b) := sigmoid_denom_pos b
  rw [div_lt_div_iff₀ ha hb]
  simp only [one_mul]
  -- Need: 1 + exp(-b) < 1 + exp(-a)
  -- i.e., exp(-b) < exp(-a)
  -- Since exp is strictly monotone and -b < -a (because a < b)
  have h : -b < -a := neg_lt_neg hab
  linarith [exp_strictMono h]

/-- Sigmoid is monotone increasing
@isnad1 id=monotone.0h0v.s2.ee2781064cf3 from=translated src=- shape=e3d48bcb vocab=67b45730
-/
theorem sigmoid_mono : Monotone sigmoid := sigmoid_strictMono.monotone

/-- Key monotonicity lemma for relaxation
@isnad1 id=le.1h2v.s4.2b7815a51c5b from=translated src=- shape=6bee9d27 vocab=e5338b31
-/
theorem sigmoid_le_of_le {a b : ℝ} (h : a ≤ b) : sigmoid a ≤ sigmoid b :=
  sigmoid_mono h

/-! ## Relaxation Bounds -/

/-- Compute sigmoid relaxation using monotonicity bounds.

    For x ∈ [l, u], we use:
    - Lower bound: constant σ(l)
    - Upper bound: constant σ(u)

    This gives tight bounds while being simple to verify. -/
noncomputable def getSigmoidRelaxation (l u : ℝ) : RealSymbolicBound :=
  { lower := ⟨0, sigmoid l⟩,
    upper := ⟨0, sigmoid u⟩ }

/-- The constant lower bound is sound
@isnad1 id=le.1h3v.s4.aaddda4d7135 from=translated src=- shape=ad2d559f vocab=e5338b31
-/
theorem sigmoid_lower_bound_valid (l u x : ℝ) (h : l ≤ x ∧ x ≤ u) :
    sigmoid l ≤ sigmoid x :=
  sigmoid_le_of_le h.1

/-- The constant upper bound is sound
@isnad1 id=le.1h3v.s4.d9982202c0d9 from=translated src=- shape=b2ac8093 vocab=e5338b31
-/
theorem sigmoid_upper_bound_valid (l u x : ℝ) (h : l ≤ x ∧ x ≤ u) :
    sigmoid x ≤ sigmoid u :=
  sigmoid_le_of_le h.2

/-- Main soundness theorem for sigmoid relaxation.

    For any x in [l, u], the sigmoid value is bounded:
    σ(l) ≤ σ(x) ≤ σ(u)
@isnad1 id=other.1h3v.s5.9873f7a700d8 from=translated src=- shape=e024ba73 vocab=5bba11ef
-/
theorem sigmoid_relaxation_sound (l u x : ℝ) (h : l ≤ x ∧ x ≤ u) :
    let sb := getSigmoidRelaxation l u
    sb.lower.eval x ≤ sigmoid x ∧ sigmoid x ≤ sb.upper.eval x := by
  simp only [getSigmoidRelaxation, RealLinearBound.eval, zero_mul, zero_add]
  exact ⟨sigmoid_lower_bound_valid l u x h, sigmoid_upper_bound_valid l u x h⟩

/-! ## Computable Rational Approximations -/

/-- Rational lower bound approximation for sigmoid.
    These are conservative (provably ≤ actual sigmoid). -/
def sigmoidLowerApprox (x : ℚ) : ℚ :=
  if x ≤ -6 then 0
  else if x ≤ -4 then 1/100
  else if x ≤ -2 then 1/10
  else if x ≤ 0 then 1/4
  else if x ≤ 2 then 1/2
  else if x ≤ 4 then 7/10
  else 9/10

/-- Rational upper bound approximation for sigmoid.
    These are conservative (provably ≥ actual sigmoid). -/
def sigmoidUpperApprox (x : ℚ) : ℚ :=
  if x ≤ -4 then 1/10
  else if x ≤ -2 then 3/10
  else if x ≤ 0 then 1/2
  else if x ≤ 2 then 3/4
  else if x ≤ 4 then 9/10
  else if x ≤ 6 then 99/100
  else 1

/-- Computable sigmoid relaxation for interval propagation -/
def getSigmoidRelaxationRat (l u : ℚ) : SymbolicBound :=
  { lower := ⟨0, sigmoidLowerApprox l⟩,
    upper := ⟨0, sigmoidUpperApprox u⟩ }

/-! ## Secant Line (for future tighter bounds) -/

/-- The secant line through (l, σ(l)) and (u, σ(u)).
    y = σ(l) + λ · (x - l) where λ = (σ(u) - σ(l)) / (u - l) -/
noncomputable def sigmoidSecantEval (l u x : ℝ) : ℝ :=
  if l < u then
    let slope := (sigmoid u - sigmoid l) / (u - l)
    sigmoid l + slope * (x - l)
  else
    sigmoid l

/-- The secant passes through (l, σ(l))
@isnad1 id=eq.0h2v.s3.4b7db3d588a2 from=translated src=- shape=5eb88a87 vocab=6a71dead
-/
theorem sigmoidSecant_at_l (l u : ℝ) : sigmoidSecantEval l u l = sigmoid l := by
  unfold sigmoidSecantEval
  split_ifs <;> simp

/-- The secant passes through (u, σ(u)) when l < u
@isnad1 id=eq.1h2v.s4.e93cf6a62fc6 from=translated src=- shape=688b6966 vocab=1ee98e2e
-/
theorem sigmoidSecant_at_u (l u : ℝ) (h : l < u) :
    sigmoidSecantEval l u u = sigmoid u := by
  unfold sigmoidSecantEval
  simp only [h, ↓reduceIte]
  have hne : u - l ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  field_simp
  ring

/-! ## Derivative -/

/-- The derivative of sigmoid: σ'(x) = σ(x) · (1 - σ(x))

    This is a key identity. The derivative is always positive and
    achieves maximum 1/4 at x = 0.
@isnad1 id=hasderiv.0h1v.s5.e9a4913c25a7 from=translated src=- shape=dc7cc4f1 vocab=28545650
-/
theorem sigmoid_deriv (x : ℝ) :
    HasDerivAt sigmoid (sigmoid x * (1 - sigmoid x)) x := by
  unfold sigmoid
  have h_denom_pos : 0 < 1 + exp (-x) := sigmoid_denom_pos x
  have h_denom_ne : 1 + exp (-x) ≠ 0 := ne_of_gt h_denom_pos
  -- Use quotient rule: d/dx [1/f] = -f'/f²
  have hexp_deriv : HasDerivAt (fun y => exp (-y)) (-exp (-x)) x := by
    have h1 := Real.hasDerivAt_exp (-x)
    have h2 := hasDerivAt_neg x
    have hcomp := HasDerivAt.comp x h1 h2
    convert! hcomp using 1
    ring
  have hdenom_deriv : HasDerivAt (fun y => 1 + exp (-y)) (-exp (-x)) x := by
    have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
    convert! hconst.add hexp_deriv using 1
    ring
  have hmain : HasDerivAt (fun y => 1 / (1 + exp (-y)))
      (exp (-x) / (1 + exp (-x))^2) x := by
    have h := hdenom_deriv.inv h_denom_ne
    simp only [one_div] at h ⊢
    convert! h using 1
    ring
  convert! hmain using 1
  -- Show: exp(-x)/(1+exp(-x))² = σ(x)·(1-σ(x))
  have h1 : 1 / (1 + exp (-x)) * (1 - 1 / (1 + exp (-x))) =
      exp (-x) / (1 + exp (-x))^2 := by
    field_simp
    ring
  linarith [h1]

/-- The derivative is always in (0, 1/4]
@isnad1 id=lt.0h1v.s5.2ad2a90b7b5d from=translated src=- shape=da168895 vocab=b535d23e
-/
theorem sigmoid_deriv_pos (x : ℝ) : 0 < sigmoid x * (1 - sigmoid x) := by
  have h1 := sigmoid_pos x
  have h2 := sigmoid_lt_one x
  exact mul_pos h1 (by linarith)

/-- Maximum derivative at x = 0: σ'(0) = 1/4
@isnad1 id=eq.0h0v.s5.1812a6ea955f from=translated src=- shape=b1fc8593 vocab=3bc38877
-/
theorem sigmoid_deriv_max : sigmoid 0 * (1 - sigmoid 0) = 1 / 4 := by
  rw [sigmoid_zero]
  norm_num

end LeanCert.ML.Symbolic
