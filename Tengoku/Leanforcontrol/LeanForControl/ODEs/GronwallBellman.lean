import Tengoku
import Tengoku.Leanforcontrol.LeanForControl.Analysis.Integrals

open MeasureTheory intervalIntegral Real Set Filter

/-!
# Gronwall's Inequality (Lemma A.1)

## Proof strategy (integrating-factor / variation of parameters)

Define:
  z(t) = ∫_a^t μ(s) y(s) ds
  v(t) = z(t) + Λ(t) − y(t) ≥ 0   (non-negative by hypothesis)
  M(t) = ∫_a^t μ(τ) dτ
  w(t) = exp(−M(t)) · z(t)         (integrating-factor transform)

By FTC + product rule:
  ẇ(t) = exp(−M(t)) · (μ(t)·y(t) − μ(t)·z(t))
        = exp(−M(t)) · μ(t) · (Λ(t) − v(t))
        ≤ exp(−M(t)) · μ(t) · Λ(t)   -- since exp, μ, v ≥ 0

Integrating from a (where w(a) = 0):
  w(t) ≤ ∫_a^t exp(−M(s)) μ(s) Λ(s) ds

Multiplying by exp(M(t)) and using exp(M(t))·exp(−M(s)) = exp(∫_s^t μ):
  z(t) ≤ ∫_a^t Λ(s) μ(s) exp(∫_s^t μ) ds
-/

/-
A wrapper for the Fundamental Theorem of Calculus.
Given a continuous function `μ` on `[a, b]`, this lemma proves that the
integral `x ↦ ∫ τ in a..x, μ τ` is differentiable at any interior point `t ∈ (a, b)`,
and its derivative is `μ t`.
-/

lemma hasDerivAt_integral {a b : ℝ} {μ : ℝ → ℝ}
    (hμ : ContinuousOn μ (Icc a b)) (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun x ↦ ∫ τ in a..x, μ τ) (μ t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((hμ.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
    ((hμ.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
    (hμ.continuousAt (Icc_mem_nhds ht.1 ht.2))

/-
Continuity of the integral function on a closed, ordered interval.
If a function `f` is integrable on `[a, t]`, the function defined by integrating `f`
from `a` to `s` is continuous for all `s ∈ [a, t]`.
This is a wrapper of `intervalIntegral.continuousOn_primitive_interval`
that avoids unordered interval (`uIcc`) issues by explicitly requiring `a ≤ t`.
-/

lemma continuousOn_integral_Icc {a t : ℝ} {f : ℝ → ℝ} (h : a ≤ t)
    (hf_int : IntegrableOn f (Icc a t) volume) :
    ContinuousOn (fun s ↦ ∫ τ in a..s, f τ) (Icc a t) := by
  have hu : Set.uIcc a t = Set.Icc a t := Set.uIcc_of_le h
  rw [← hu] at hf_int ⊢
  exact intervalIntegral.continuousOn_primitive_interval hf_int

/-! ## General form -/

/-
Gronwall-Bellman Inequality (Integral form with time-dependent coefficients).

This theorem provides an explicit upper bound for a function `y` that satisfies
a specific integral inequality. It is a fundamental tool in the analysis of
ordinary differential equations, often used to bound the growth of solutions or
prove uniqueness.

Let `Λ` and `μ` be continuous functions on `[a, b]`, with `μ` strictly non-negative.
If a continuous function `y` satisfies the integral inequality:
  `y t ≤ Λ t + ∫ s in a..t, μ s * y s`  for all `t ∈ [a, b]`
then `y` is bounded by:
  `y t ≤ Λ t + ∫ s in a..t, Λ s * μ s * exp (∫ τ in s..t, μ τ)`

-/

/-! ## Special case 1: constant Λ -/

/-! ## Special case 1: constant Λ, μ -/
