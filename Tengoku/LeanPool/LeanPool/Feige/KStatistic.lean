/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku

/-!
# An exponential representation of the Dirichlet statistic

Equation (2.1) defines `Kₙ` using a uniform point of the standard simplex.
For the formal proof of Theorem 2.1, this file uses the equivalent
independent-rate-one-exponential representation.  Its identification with
the simplex statistic in (2.1) is isolated in a later geometry module.

The coordinate indexed by `none` is `E₀`; `some i` is `Eᵢ`.  We put the
exponentials on `ℝ≥0`, so their nonnegativity is encoded by the type and the
coordinatewise antitonicity of `K` is a pointwise set inclusion.
-/

@[expose] public section

open scoped BigOperators ENNReal

open MeasureTheory ProbabilityTheory Set

namespace Feige

section ExponentialMeasure

/-- The rate-one exponential law, pushed to `ℝ≥0`.

The source exponential law is already supported on the nonnegative reals.
Using the push-forward makes nonnegativity definitional in all later finite
sum arguments.
-/
noncomputable def nnexpMeasure : Measure NNReal :=
  (expMeasure 1).map Real.toNNReal

/-- The joint law of `E₀` and an `ι`-indexed family of independent
rate-one exponentials. -/
noncomputable def expProductMeasure (ι : Type*) [Fintype ι] :
    Measure (Option ι → NNReal) :=
  Measure.pi fun _ ↦ nnexpMeasure

end ExponentialMeasure

section Statistic

variable {ι : Type*} [Fintype ι]

/-- The exponential event corresponding to the simplex event in (2.1). -/
def kEvent (y : ι → ℝ) : Set (Option ι → NNReal) :=
  {e | ∑ i, (y i - 1) * (e (some i) : ℝ) ≤ (e none : ℝ)}

theorem measurableSet_kEvent (y : ι → ℝ) : MeasurableSet (kEvent y) := by
  unfold kEvent
  apply measurableSet_le
  · exact Finset.measurable_fun_sum Finset.univ fun i _ ↦
      measurable_const.mul ((measurable_pi_apply (some i)).coe_nnreal_real)
  · exact (measurable_pi_apply none).coe_nnreal_real

/-- The Dirichlet statistic from (2.1), represented internally by
independent rate-one exponentials. -/
noncomputable def dirichletK (y : ι → ℝ) : ℝ :=
  (expProductMeasure ι).real (kEvent y)

theorem dirichletK_nonneg (y : ι → ℝ) : 0 ≤ dirichletK y :=
  measureReal_nonneg

theorem kEvent_antitone {y z : ι → ℝ} (hyz : y ≤ z) :
    kEvent z ⊆ kEvent y := by
  intro e he
  change (∑ i, (z i - 1) * (e (some i) : ℝ)) ≤ (e none : ℝ) at he
  change (∑ i, (y i - 1) * (e (some i) : ℝ)) ≤ (e none : ℝ)
  apply le_trans _ he
  exact Finset.sum_le_sum fun i _ ↦
    mul_le_mul_of_nonneg_right (sub_le_sub_right (hyz i) 1) (e (some i)).coe_nonneg

end Statistic

end Feige
