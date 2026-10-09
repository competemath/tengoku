/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Patrick Massot, Floris van Doorn, Jireh Loreaux, Eric Wieser,
Yongxi Lin, Louis (Yiyang) Liu
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.Deriv.MeanValue
public import Tengoku.Seed.Order.Interval.Set.Basic
public import Tengoku.Seed.LinearAlgebra.AffineSpace.Ordered

/-!
# The First- and Second-Derivative Tests

We prove the first-derivative test from calculus, in the strong form given on [Wikipedia](https://en.wikipedia.org/wiki/Derivative_test#First-derivative_test).

The test is proved over the real numbers ℝ
using `monotoneOn_of_deriv_nonneg` from `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`.

We prove the second-derivative test using the first-derivative test.
Source: [Wikipedia](https://en.wikipedia.org/wiki/Derivative_test#Proof_of_the_second-derivative_test).

## Main results

* `isLocalMax_of_deriv_Ioo`: Suppose `f` is a real-valued function of a real variable
  defined on some interval containing the point `a`.
  Further suppose that `f` is continuous at `a` and differentiable on some open interval
  containing `a`, except possibly at `a` itself.

  If there exists a positive number `r > 0` such that for every `x` in `Ioo (a − r) a`
  we have `f′(x) ≥ 0`, and for every `x` in `Ioo a (a + r)` we have `f′(x) ≤ 0`,
  then `f` has a local maximum at `a`.

* `isLocalMin_of_deriv_Ioo`: The dual of `first_derivative_max`, for minima.

* `isLocalMax_of_deriv`: 1st derivative test for maxima using filters.

* `isLocalMin_of_deriv`: 1st derivative test for minima using filters.

* `isLocalMin_of_deriv_deriv_pos`: The second-derivative test, minimum version.


## Tags

derivative test, first-derivative test, second-derivative test, calculus
-/

public section


open Set Topology

/-- If `f` is continuous at `b` and differentiable on `Ioo a b`, then `f` is continuous on
`Ioc a b`. -/
private lemma continuousOn_Ioc {f : ℝ → ℝ} {a b : ℝ} (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) : ContinuousOn f (Ioc a b) := by
  by_cases! g₀ : a < b
  · exact Ioo_union_right g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Ioc_eq_empty_of_le g₀]

/-- If `f` is continuous at `a` and differentiable on `Ioo a b`, then `f` is continuous on
`Ico a b`. -/
private lemma continuousOn_Ico {f : ℝ → ℝ} {a b : ℝ} (h : ContinuousAt f a)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) : ContinuousOn f (Ico a b) := by
  by_cases! g₀ : a < b
  · exact Ioo_union_left g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Ico_eq_empty_of_le g₀]

/-- If `f` is continuous at `a, b` and differentiable on `Ioo a b`, then `f` is continuous on
`Icc a b`. -/
private lemma continuousOn_Icc {f : ℝ → ℝ} {a b : ℝ} (ha : ContinuousAt f a)
    (hb : ContinuousAt f b) (hd₀ : DifferentiableOn ℝ f (Ioo a b)) : ContinuousOn f (Icc a b) := by
  by_cases! g₀ : a ≤ b
  · exact Ioo_union_both g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Icc_eq_empty_of_lt g₀]

/-- If `f` is continuous at `b` and differentiable on `Iio b`, then `f` is continuous on
`Iic b`. -/
private lemma continuousOn_Iic {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Iio b)) : ContinuousOn f (Iic b) := by
  simp_rw [← Iio_union_right]
  apply hd₀.continuousOn.union_continuousAt isOpen_Iio (by simp [h])

/-- If `f` is continuous at `a` and differentiable on `Ioi a`, then `f` is continuous on
`Ici a`. -/
private lemma continuousOn_Ici {f : ℝ → ℝ} {a : ℝ} (h : ContinuousAt f a)
    (hd₀ : DifferentiableOn ℝ f (Ioi a)) : ContinuousOn f (Ici a) := by
  rw [← Ioi_union_left]
  exact hd₀.continuousOn.union_continuousAt isOpen_Ioi (by simp [h])

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonnegative on `Ioo a b` and
nonpositive on `Ioo b c`. Then `f` attains its maximum on `Ioo a c` at `b`.
@isnad1 id=ismaxon.5h4v.s8.b89cb7c1db58 from=seed src=0 shape=15f4343c vocab=40b14184
-/
lemma isMaxOn_Ioo_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) :
    IsMaxOn f (Ioo a c) b := by
  refine isMaxOn_Ioo_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc h hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico h hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b` and `c`, the derivative `f'` is nonnegative on
`Ioo a b` and nonpositive on `Ioo b c`. Then `f` attains its maximum on `Ioc a c` at `b`.
@isnad1 id=ismaxon.6h4v.s8.91efa17789d6 from=seed src=0 shape=91c14912 vocab=94933928
-/
lemma isMaxOn_Ioc_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) :
    IsMaxOn f (Ioc a c) b := by
  refine isMaxOn_Ioc_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `a` and `b`, the derivative `f'` is nonnegative on
`Ioo a b` and nonpositive on `Ioo b c`. Then `f` attains its maximum on `Ico a c` at `b`.
@isnad1 id=ismaxon.6h4v.s8.6448981ab86f from=seed src=0 shape=fa23a245 vocab=37a64353
-/
lemma isMaxOn_Ico_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) :
    IsMaxOn f (Ico a c) b := by
  refine isMaxOn_Ico_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `a`, `b`, and `c`, the derivative `f'` is nonnegative on
`Ioo a b` and nonpositive on `Ioo b c`. Then `f` attains its maximum on `Icc a c` at `b`.
@isnad1 id=ismaxon.7h4v.s8.f2938af93235 from=seed src=0 shape=929123b6 vocab=7abeae50
-/
lemma isMaxOn_Icc_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hc : ContinuousAt f c) (hd₀ : DifferentiableOn ℝ f (Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Ioo b c)) (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x)
    (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) : IsMaxOn f (Icc a c) b := by
  refine isMaxOn_Icc_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonnegative on `Ioo a b` and
nonpositive on `Ioi b`. Then `f` attains its maximum on `Ioi a` at `b`.
@isnad1 id=ismaxon.5h3v.s7.d614b9e6226e from=seed src=0 shape=b258bebc vocab=4c7d7a37
-/
lemma isMaxOn_Ioi_of_deriv {f : ℝ → ℝ} {a b : ℝ} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioi b))
    (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioi b, deriv f x ≤ 0) :
    IsMaxOn f (Ioi a) b := by
  refine isMaxOn_Ioi_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `a` and `b`, the derivative `f'` is nonnegative on
`Ioo a b` and nonpositive on `Ioi b`. Then `f` attains its maximum on `Ici a` at `b`.
@isnad1 id=ismaxon.6h3v.s8.a62261a71ecb from=seed src=0 shape=6f170532 vocab=fe84f0a3
-/
lemma isMaxOn_Ici_of_deriv {f : ℝ → ℝ} {a b : ℝ} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioi b))
    (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioi b, deriv f x ≤ 0) :
    IsMaxOn f (Ici a) b := by
  refine isMaxOn_Ici_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonnegative on `Iio b` and
nonpositive on `Ioo b c`. Then `f` attains its maximum on `Iio c` at `b`.
@isnad1 id=ismaxon.5h3v.s7.d73dd9700f61 from=seed src=0 shape=f599fef5 vocab=3c2dda4b
-/
lemma isMaxOn_Iio_of_deriv {f : ℝ → ℝ} {b c : ℝ} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Iio b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Iio b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) :
    IsMaxOn f (Iio c) b := by
  refine isMaxOn_Iio_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b` and `c`, the derivative `f'` is nonnegative on
`Iio b` and nonpositive on `Ioo b c`. Then `f` attains its maximum on `Iic c` at `b`.
@isnad1 id=ismaxon.6h3v.s8.4ea2ccb05331 from=seed src=0 shape=4b12c2c6 vocab=56144afa
-/
lemma isMaxOn_Iic_of_deriv {f : ℝ → ℝ} {b c : ℝ} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
    (hd₀ : DifferentiableOn ℝ f (Iio b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Iio b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) :
    IsMaxOn f (Iic c) b := by
  refine isMaxOn_Iic_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonnegative on `Iio b` and
nonpositive on `Ioi b`. Then `f` attains its maximum on `ℝ` at `b`.
@isnad1 id=ismaxon.5h2v.s7.f6d7e3d087db from=seed src=0 shape=a7faefa0 vocab=98a54a9e
-/
lemma isMaxOn_univ_of_deriv {f : ℝ → ℝ} {b : ℝ} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Iio b)) (hd₁ : DifferentiableOn ℝ f (Ioi b))
    (h₀ : ∀ x ∈ Iio b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioi b, deriv f x ≤ 0) :
    IsMaxOn f univ b := by
  refine isMaxOn_univ_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/-- The First-Derivative Test from calculus, maxima version.
Suppose `a < b < c`, `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonnegative on
`Ioo a b` and nonpositive on `Ioo b c`. Then `f` has a local maximum at `b`.
@isnad1 id=islocalm.7h4v.s8.8ce87c259c82 from=seed src=0 shape=4d40c8f5 vocab=f29f86df
-/
lemma isLocalMax_of_deriv_Ioo {f : ℝ → ℝ} {a b c : ℝ} (g₀ : a < b) (g₁ : b < c)
    (h : ContinuousAt f b) (hd₀ : DifferentiableOn ℝ f (Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Ioo b c)) (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x)
    (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) : IsLocalMax f b :=
  (isMaxOn_Ioo_of_deriv h hd₀ hd₁ h₀ h₁).isLocalMax (Ioo_mem_nhds g₀ g₁)

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonpositive on `Ioo a b` and
nonnegative on `Ioo b c`. Then `f` attains its minimum on `Ioo a c` at `b`.
@isnad1 id=isminon.5h4v.s8.5866f0e1a206 from=seed src=0 shape=ed7f053a vocab=a84e61d2
-/
lemma isMinOn_Ioo_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) :
    IsMinOn f (Ioo a c) b := by
  refine isMinOn_Ioo_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc h hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico h hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b` and `c`, the derivative `f'` is nonpositive on
`Ioo a b` and nonnegative on `Ioo b c`. Then `f` attains its minimum on `Ioc a c` at `b`.
@isnad1 id=isminon.6h4v.s8.12a49fe55fbd from=seed src=0 shape=2c5b4cbb vocab=e8e235d6
-/
lemma isMinOn_Ioc_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) :
    IsMinOn f (Ioc a c) b := by
  refine isMinOn_Ioc_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `a` and `b`, the derivative `f'` is nonpositive on
`Ioo a b` and nonnegative on `Ioo b c`. Then `f` attains its minimum on `Ico a c` at `b`.
@isnad1 id=isminon.6h4v.s8.85e9696165da from=seed src=0 shape=84da51d0 vocab=2d2ae54a
-/
lemma isMinOn_Ico_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) :
    IsMinOn f (Ico a c) b := by
  refine isMinOn_Ico_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `a`, `b`, and `c`, the derivative `f'` is nonpositive on
`Ioo a b` and nonnegative on `Ioo b c`. Then `f` attains its minimum on `Icc a c` at `b`.
@isnad1 id=isminon.7h4v.s8.1f75e46c8f92 from=seed src=0 shape=e14180d8 vocab=23d8de7e
-/
lemma isMinOn_Icc_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hc : ContinuousAt f c) (hd₀ : DifferentiableOn ℝ f (Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Ioo b c)) (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0)
    (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) : IsMinOn f (Icc a c) b := by
  refine isMinOn_Icc_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonpositive on `Ioo a b` and
nonnegative on `Ioi b`. Then `f` attains its minimum on `Ioi a` at `b`.
@isnad1 id=isminon.5h3v.s7.546716281a65 from=seed src=0 shape=80e5c4e5 vocab=e46478c9
-/
lemma isMinOn_Ioi_of_deriv {f : ℝ → ℝ} {a b : ℝ} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioi b))
    (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioi b, 0 ≤ deriv f x) :
    IsMinOn f (Ioi a) b := by
  refine isMinOn_Ioi_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `a` and `b`, the derivative `f'` is nonpositive on
`Ioo a b` and nonnegative on `Ioi b`. Then `f` attains its minimum on `Ici a` at `b`.
@isnad1 id=isminon.6h3v.s8.ab1ae8a7e1af from=seed src=0 shape=c199b047 vocab=29e19ca8
-/
lemma isMinOn_Ici_of_deriv {f : ℝ → ℝ} {a b : ℝ} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioi b))
    (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioi b, 0 ≤ deriv f x) :
    IsMinOn f (Ici a) b := by
  refine isMinOn_Ici_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonpositive on `Iio b` and
nonnegative on `Ioo b c`. Then `f` attains its minimum on `Iio c` at `b`.
@isnad1 id=isminon.5h3v.s7.baab9263f597 from=seed src=0 shape=99ce0d67 vocab=6bdd172a
-/
lemma isMinOn_Iio_of_deriv {f : ℝ → ℝ} {b c : ℝ} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Iio b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Iio b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) :
    IsMinOn f (Iio c) b := by
  refine isMinOn_Iio_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b` and `c`, the derivative `f'` is nonpositive on
`Iio b` and nonnegative on `Ioo b c`. Then `f` attains its minimum on `Iic c` at `b`.
@isnad1 id=isminon.6h3v.s8.851a6193c2b2 from=seed src=0 shape=86a7a5a7 vocab=281a6a3b
-/
lemma isMinOn_Iic_of_deriv {f : ℝ → ℝ} {b c : ℝ} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
    (hd₀ : DifferentiableOn ℝ f (Iio b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Iio b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) :
    IsMinOn f (Iic c) b := by
  refine isMinOn_Iic_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonpositive on `Iio b` and
nonnegative on `Ioi b`. Then `f` attains its minimum on `ℝ` at `b`.
@isnad1 id=isminon.5h2v.s7.5afd09c704f8 from=seed src=0 shape=aa9cdc6c vocab=7762e864
-/
lemma isMinOn_univ_of_deriv {f : ℝ → ℝ} {b : ℝ} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Iio b)) (hd₁ : DifferentiableOn ℝ f (Ioi b))
    (h₀ : ∀ x ∈ Iio b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioi b, 0 ≤ deriv f x) :
    IsMinOn f univ b := by
  refine isMinOn_univ_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/-- The First-Derivative Test from calculus, minima version.
@isnad1 id=islocalm.7h4v.s8.ea0b0ce7a0b2 from=seed src=0 shape=804eca90 vocab=1c1aa969
-/
lemma isLocalMin_of_deriv_Ioo {f : ℝ → ℝ} {a b c : ℝ} (g₀ : a < b) (g₁ : b < c)
    (h : ContinuousAt f b) (hd₀ : DifferentiableOn ℝ f (Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Ioo b c)) (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0)
    (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) : IsLocalMin f b :=
  (isMinOn_Ioo_of_deriv h hd₀ hd₁ h₀ h₁).isLocalMin (Ioo_mem_nhds g₀ g₁)

/-- The First-Derivative Test from calculus, maxima version,
expressed in terms of left and right filters.
@isnad1 id=islocalm.5h2v.s8.13a29092bee2 from=seed src=0 shape=5ce81e67 vocab=389a0191
-/
lemma isLocalMax_of_deriv' {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd₀ : ∀ᶠ x in 𝓝[<] b, DifferentiableAt ℝ f x) (hd₁ : ∀ᶠ x in 𝓝[>] b, DifferentiableAt ℝ f x)
    (h₀ : ∀ᶠ x in 𝓝[<] b, 0 ≤ deriv f x) (h₁ : ∀ᶠ x in 𝓝[>] b, deriv f x ≤ 0) :
    IsLocalMax f b := by
  obtain ⟨a, ha⟩ := (nhdsLT_basis b).eventually_iff.mp <| hd₀.and h₀
  obtain ⟨c, hc⟩ := (nhdsGT_basis b).eventually_iff.mp <| hd₁.and h₁
  exact isLocalMax_of_deriv_Ioo ha.1 hc.1 h
    (fun _ hx => (ha.2 hx).1.differentiableWithinAt)
    (fun _ hx => (hc.2 hx).1.differentiableWithinAt)
    (fun _ hx => (ha.2 hx).2) (fun x hx => (hc.2 hx).2)

/-- The First-Derivative Test from calculus, minima version,
expressed in terms of left and right filters.
@isnad1 id=islocalm.5h2v.s8.1f006a000571 from=seed src=0 shape=8cac8b38 vocab=74188e16
-/
lemma isLocalMin_of_deriv' {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd₀ : ∀ᶠ x in 𝓝[<] b, DifferentiableAt ℝ f x) (hd₁ : ∀ᶠ x in 𝓝[>] b, DifferentiableAt ℝ f x)
    (h₀ : ∀ᶠ x in 𝓝[<] b, deriv f x ≤ 0) (h₁ : ∀ᶠ x in 𝓝[>] b, deriv f x ≥ 0) :
    IsLocalMin f b := by
  obtain ⟨a, ha⟩ := (nhdsLT_basis b).eventually_iff.mp <| hd₀.and h₀
  obtain ⟨c, hc⟩ := (nhdsGT_basis b).eventually_iff.mp <| hd₁.and h₁
  exact isLocalMin_of_deriv_Ioo ha.1 hc.1 h
    (fun _ hx => (ha.2 hx).1.differentiableWithinAt)
    (fun _ hx => (hc.2 hx).1.differentiableWithinAt)
    (fun _ hx => (ha.2 hx).2) (fun x hx => (hc.2 hx).2)

/-- The First Derivative test, maximum version.
@isnad1 id=islocalm.4h2v.s7.dd0b875581d8 from=seed src=0 shape=5f9e0852 vocab=220009cc
-/
theorem isLocalMax_of_deriv {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℝ f x)
    (h₀ : ∀ᶠ x in 𝓝[<] b, 0 ≤ deriv f x) (h₁ : ∀ᶠ x in 𝓝[>] b, deriv f x ≤ 0) :
    IsLocalMax f b :=
  isLocalMax_of_deriv' h (nhdsLT_le_nhdsNE _ (by tauto)) (nhdsGT_le_nhdsNE _ (by tauto)) h₀ h₁

/-- The First Derivative test, minimum version.
@isnad1 id=islocalm.4h2v.s7.dc27c8b2173c from=seed src=0 shape=7daec9e6 vocab=2d873231
-/
theorem isLocalMin_of_deriv {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℝ f x)
    (h₀ : ∀ᶠ x in 𝓝[<] b, deriv f x ≤ 0) (h₁ : ∀ᶠ x in 𝓝[>] b, 0 ≤ deriv f x) :
    IsLocalMin f b :=
  isLocalMin_of_deriv' h (nhdsLT_le_nhdsNE _ (by tauto)) (nhdsGT_le_nhdsNE _ (by tauto)) h₀ h₁

open Filter SignType

section SecondDeriv

variable {f : ℝ → ℝ} {x₀ : ℝ}

/-- If the derivative of `f` is positive at a root `x₀` of `f`, then locally the sign of `f x`
matches `x - x₀`.
@isnad1 id=eventual.2h2v.s7.47b49a0e4688 from=seed src=0 shape=10cbfc8b vocab=eed85e4b
-/
lemma eventually_nhdsWithin_sign_eq_of_deriv_pos (hf : deriv f x₀ > 0) (hx : f x₀ = 0) :
    ∀ᶠ x in 𝓝 x₀, sign (f x) = sign (x - x₀) := by
  rw [← nhdsNE_sup_pure x₀, eventually_sup]
  refine ⟨?_, by simpa⟩
  have h_tendsto := hasDerivAt_iff_tendsto_slope.mp
    (differentiableAt_of_deriv_ne_zero <| ne_of_gt hf).hasDerivAt
  filter_upwards [(h_tendsto.eventually <| eventually_gt_nhds hf),
    self_mem_nhdsWithin] with x hx₀ hx₁
  rw [mem_compl_iff, mem_singleton_iff, ← Ne.eq_def] at hx₁
  obtain (hx' | hx') := hx₁.lt_or_gt
  · rw [sign_neg (neg_of_slope_pos hx' hx₀ hx), sign_neg (sub_neg.mpr hx')]
  · rw [sign_pos (pos_of_slope_pos hx' hx₀ hx), sign_pos (sub_pos.mpr hx')]

/-- If the derivative of `f` is negative at a root `x₀` of `f`, then locally the sign of `f x`
matches `x₀ - x`.
@isnad1 id=eventual.2h2v.s7.a31cf47c26d3 from=seed src=0 shape=622ee8f0 vocab=c4e7e9f1
-/
lemma eventually_nhdsWithin_sign_eq_of_deriv_neg (hf : deriv f x₀ < 0) (hx : f x₀ = 0) :
    ∀ᶠ x in 𝓝 x₀, sign (f x) = sign (x₀ - x) := by
  simpa [Left.sign_neg, -neg_sub, ← neg_sub x₀] using
    eventually_nhdsWithin_sign_eq_of_deriv_pos
      (f := (-f ·)) (x₀ := x₀) (by simpa [deriv.neg]) (by simpa)

/--
@isnad1 id=eventual.1h2v.s7.7c385cf6f66a from=seed src=0 shape=e69a4e3b vocab=57852596
-/
lemma deriv_neg_left_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, sign (deriv f x) = sign (x - x₀)) :
    ∀ᶠ (b : ℝ) in 𝓝[<] x₀, deriv f b < 0 := by
  filter_upwards [nhdsLT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x < x₀)
  rwa [← sub_neg, ← sign_eq_neg_one_iff, ← hx', sign_eq_neg_one_iff] at hx

/--
@isnad1 id=eventual.1h2v.s7.ec2fb15f14c4 from=seed src=0 shape=dad03a56 vocab=47e0bb99
-/
lemma deriv_neg_right_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, sign (deriv f x) = sign (x₀ - x)) :
     ∀ᶠ (b : ℝ) in 𝓝[>] x₀, deriv f b < 0 := by
  filter_upwards [nhdsGT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x₀ < x)
  rwa [← sub_neg, ← sign_eq_neg_one_iff, ← hx', sign_eq_neg_one_iff] at hx

/--
@isnad1 id=eventual.1h2v.s7.46907195fa5f from=seed src=0 shape=e69a4e3b vocab=fbbccde3
-/
lemma deriv_pos_right_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, sign (deriv f x) = sign (x - x₀)) :
     ∀ᶠ (b : ℝ) in 𝓝[>] x₀, deriv f b > 0 := by
  filter_upwards [nhdsGT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x₀ < x)
  rwa [← sub_pos, ← sign_eq_one_iff, ← hx', sign_eq_one_iff] at hx

/--
@isnad1 id=eventual.1h2v.s7.8a58afda02db from=seed src=0 shape=dad03a56 vocab=1edc15c6
-/
lemma deriv_pos_left_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, sign (deriv f x) = sign (x₀ - x)) :
    ∀ᶠ (b : ℝ) in 𝓝[<] x₀, deriv f b > 0 := by
  filter_upwards [nhdsLT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x < x₀)
  rwa [← sub_pos, ← sign_eq_one_iff, ← hx', sign_eq_one_iff] at hx

/-- The First Derivative test with a hypothesis on the sign of the derivative, maximum version.
@isnad1 id=islocalm.2h2v.s7.b86e445144d1 from=seed src=0 shape=b0636026 vocab=19238c84
-/
theorem isLocalMax_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ} (h : ContinuousAt f x₀)
    (hf : ∀ᶠ x in 𝓝[≠] x₀, sign (deriv f x) = sign (x₀ - x)) :
    IsLocalMax f x₀ := by
  have hl := deriv_pos_left_of_sign_deriv hf
  have hg := deriv_neg_right_of_sign_deriv hf
  replace hf := (nhdsLT_sup_nhdsGT x₀) ▸
    eventually_sup.mpr ⟨hl.mono fun x hx => hx.ne', hg.mono fun x hx => hx.ne⟩
  exact isLocalMax_of_deriv h (hf.mono fun x hx ↦ differentiableAt_of_deriv_ne_zero hx)
    (hl.mono fun _ => le_of_lt) (hg.mono fun _ => le_of_lt)

/-- The First Derivative test with a hypothesis on the sign of the derivative, minimum version.
@isnad1 id=islocalm.2h2v.s7.c0c10b4bd80e from=seed src=0 shape=7babbedc vocab=5eb969fa
-/
theorem isLocalMin_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ} (h : ContinuousAt f x₀)
    (hf : ∀ᶠ x in 𝓝[≠] x₀, sign (deriv f x) = sign (x - x₀)) :
    IsLocalMin f x₀ := by
  refine neg_neg f ▸ (isLocalMax_of_sign_deriv (f := (-f ·)) h.neg ?foo |>.neg)
  simpa [Left.sign_neg, -neg_sub, ← neg_sub _ x₀, deriv.neg]

/-- The Second-Derivative Test from calculus, minimum version.
Applies to functions like `x^2 + 1[x ≥ 0]` as well as twice differentiable
functions.
@isnad1 id=islocalm.3h2v.s7.6b2189a70973 from=seed src=0 shape=5cd808d8 vocab=e0019fb5
-/
theorem isLocalMin_of_deriv_deriv_pos (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMin f x₀ :=
  isLocalMin_of_sign_deriv hc <| nhdsWithin_le_nhds <|
    eventually_nhdsWithin_sign_eq_of_deriv_pos hf hd

/-- The Second-Derivative Test from calculus, maximum version.
@isnad1 id=islocalm.3h2v.s7.f9397b0452f0 from=seed src=0 shape=5cd808d8 vocab=38da5446
-/
theorem isLocalMax_of_deriv_deriv_neg (hf : deriv (deriv f) x₀ < 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMax f x₀ := by
  simpa using isLocalMin_of_deriv_deriv_pos (by simpa) (by simpa) hc.neg |>.neg

end SecondDeriv
