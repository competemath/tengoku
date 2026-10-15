/-
Copyright (c) 2026 James Huang, Samuël Borza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Huang, Samuël Borza
-/
module

public import Tengoku

/-!
# Incremental derivatives

Differentiability and derivative formulas for the maps `t ↦ f⁽ᵏ⁾(t · x)` and their
finite sums, used to differentiate the exponential factors in Niven's argument.
-/

@[expose] public section

open Polynomial
open Complex

open scoped Polynomial
open scoped BigOperators

noncomputable section

/-- Given `x ∈ ℂ`, the map `t ↦ t * x` is differentiable at `t`.
@isnad1 id=differen.0h2v.s6.c44682a14686 from=translated src=- shape=3ad920cf vocab=66054778
-/
lemma differentiableAt_mul_const_ofReal (x : ℂ) (t : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => t * x) t :=
  (Complex.ofRealCLM.differentiableAt (x := t)).mul_const x

/-- `d/dt (t * x) = x`.
@isnad1 id=eq.0h2v.s6.5f1620316d11 from=translated src=- shape=de6aedf4 vocab=3d4bc586
-/
lemma deriv_mul_const_ofReal (x : ℂ) (t : ℝ) :
  deriv (fun t : ℝ => t * x) t = x := by
  simpa using deriv_smul_const (hc := differentiableAt_id (x := t)) (f := x)

/-- If `f` is differentiable at `t * x`, then `u ↦ f(u * x)` is differentiable at `t`.
@isnad1 id=differen.1h3v.s7.a08f23d6c17b from=translated src=- shape=fd38e630 vocab=66054778
-/
lemma differentiableAt_comp_mul_real
  (f : ℂ → ℂ) (x : ℂ) (t : ℝ)
  (hf : DifferentiableAt ℂ f (t * x)) :
    DifferentiableAt ℝ (fun t : ℝ => f (t * x)) t :=
  ((hf.hasDerivAt.comp (t : ℂ) (hasDerivAt_mul_const x)).comp_ofReal).differentiableAt

/-- For `x ∈ ℂ`, the map `t ↦ e^(-(t * x))` is differentiable at `t`.
@isnad1 id=differen.0h2v.s6.e5f9b479e57b from=translated src=- shape=e6f92d1a vocab=27ca4239
-/
lemma differentiableAt_exp_neg_mul (x : ℂ) (t : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => cexp (-(t * x))) t :=
  (differentiableAt_mul_const_ofReal x t).neg.cexp

/-- If `f^(n)` is differentiable at `t * x`, then `t ↦ f^(n)(t * x)` is continuous on
`[0, 1]` at `t`.
@isnad1 id=continuo.1h4v.s7.213f8e3a73a0 from=translated src=- shape=18451666 vocab=558e72db
-/
lemma continuousWithinAt_iteratedDeriv_comp_mul
  (f : ℂ → ℂ) (x : ℂ) (n : ℕ) (t : ℝ)
  (hderiv : DifferentiableAt ℂ (iteratedDeriv n f) (t * x)) :
    ContinuousWithinAt (fun t : ℝ => iteratedDeriv n f (t * x))
      (Set.uIcc (0 : ℝ) 1) t :=
  ContinuousAt.continuousWithinAt
    ((differentiableAt_comp_mul_real (f := iteratedDeriv n f) x t hderiv).continuousAt)

/-- If `f⁽ᵏ⁾` is differentiable at `t * x`, then `t ↦ f⁽ᵏ⁾(t * x)` is differentiable at `t`.
@isnad1 id=differen.1h4v.s7.e9d0ce500040 from=translated src=- shape=a03458b3 vocab=fa5cf28a
-/
lemma differentiableAt_iteratedDeriv_comp_mul
  (f : ℂ → ℂ) (x : ℂ) (k : ℕ) (t : ℝ)
  (hderiv : DifferentiableAt ℂ (iteratedDeriv k f) (t * x)) :
    DifferentiableAt ℝ (fun t : ℝ => iteratedDeriv k f (t * x)) t :=
  differentiableAt_comp_mul_real (f := iteratedDeriv k f) x t hderiv

/-- If `f⁽ⁱ⁾` is differentiable at `t * x`, then `d/dt f⁽ᵏ⁾(t * x)) = x * f⁽ᵏ⁺¹⁾(t * x)`.
@isnad1 id=eq.1h4v.s7.53861c384680 from=translated src=- shape=320c9c40 vocab=6a3b39af
-/
lemma deriv_iteratedDeriv_comp_mul
  (f : ℂ → ℂ) (x : ℂ) (k : ℕ) (t : ℝ)
  (hderiv : DifferentiableAt ℂ (iteratedDeriv k f) (t * x)) :
    deriv (fun t : ℝ => iteratedDeriv k f (t * x)) t
      = x * iteratedDeriv (k + 1) f (t * x) := by
  have hcomp :
      deriv (fun t : ℝ => iteratedDeriv k f (t * x)) t =
        deriv (iteratedDeriv k f) (t * x) *
          deriv (fun t : ℝ => (t : ℂ) * x) t := by
    exact (deriv_comp (𝕜 := ℝ) (𝕜' := ℂ) (x := t) (hh₂ := hderiv)
          (hh := differentiableAt_mul_const_ofReal x t))
  rw [hcomp, deriv_mul_const_ofReal x t, ← iteratedDeriv_succ]
  simp [mul_comm]

/-- If `f⁽ᵏ⁾` is differentiable at `t * x` for every `k ≤ n`, then
`t ↦ ∑ₖ₌₀ⁿ f⁽ᵏ⁾(t * x)` is differentiable at `t`.
@isnad1 id=differen.1h4v.s7.fbdf22dc516d from=translated src=- shape=b8298b24 vocab=40f2f3ed
-/
lemma differentiableAt_sum_iteratedDeriv
  (f : ℂ → ℂ) (x : ℂ) (n : ℕ) (t : ℝ)
  (hderiv : ∀ k ≤ n, DifferentiableAt ℂ (iteratedDeriv k f) (t * x)) :
    DifferentiableAt ℝ
      (fun t : ℝ =>
        ∑ k ∈ Finset.range (n + 1),
          iteratedDeriv k f (t * x)) t := by
  refine DifferentiableAt.fun_sum (𝕜 := ℝ) (E := ℝ) (F := ℂ)
    (u := Finset.range (n + 1))
    (A := fun k t => iteratedDeriv k f (t * x)) ?_
  intro k hk
  exact differentiableAt_iteratedDeriv_comp_mul f x k t
    (hderiv k (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk))

/-- If `f⁽ᵏ⁾` is differentiable at `t * x` for every `k ≤ n`, then
`d/dt ∑ᵢ₌₀ⁿ f⁽ⁱ⁾(t * x)) = ∑ᵢ₌₀ⁿ x * f⁽ⁱ⁺¹⁾(t * x)`.
@isnad1 id=eq.1h4v.s8.d394898dcc46 from=translated src=- shape=084a261a vocab=bcf551b6
-/
lemma sum_deriv_iteratedDeriv_comp_mul
  (f : ℂ → ℂ) (x : ℂ) (n : ℕ) (t : ℝ)
  (hderiv : ∀ k ≤ n, DifferentiableAt ℂ (iteratedDeriv k f) (t * x)) :
    deriv
      (fun t : ℝ => ∑ i ∈ Finset.range (n + 1), iteratedDeriv i f (t * x)) t =
      ∑ i ∈ Finset.range (n + 1), x * iteratedDeriv (i + 1) f (t * x) := by
  rw [deriv_fun_sum]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    simpa using deriv_iteratedDeriv_comp_mul f x i t
      (hderiv i (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hi))
  · intro k hk
    simpa using differentiableAt_iteratedDeriv_comp_mul f x k t
      (hderiv k (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk))
