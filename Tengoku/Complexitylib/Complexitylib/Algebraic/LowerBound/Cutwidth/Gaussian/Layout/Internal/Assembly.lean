/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Expectation
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Grid

/-!
# A good Gaussian sample

Fix thresholds `-T + i δ` with `δ = 2T / M`. For each threshold count the separated
edges and the scores in the following window, and count both tails. Each count deviates
from its mean by at least `ε h` with probability `O(1 / h)` by the second-moment bound,
so for large cubic graphs some sample keeps all `2M + 2` counts within `ε h` of their
means. The grid bound then controls every prefix of that sample's score order.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory

/-- The per-vertex prefix-cut bound of the layout with the given parameters. -/
noncomputable def layoutBound (ρ₀ T ε : ℝ) (M : ℕ) : ℝ :=
  max (3 / T ^ 2 + 3 * ε)
    (3 / 2 * crossBound ρ₀ + 4 * ε + 3 * (2 * T / M) / Real.sqrt (2 * Real.pi))

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem measurableSet_scoreEvent (q : ℝ) (R : ℕ) {p : ℝ → Prop}
    (hp : MeasurableSet {x | p x}) (v : W) : MeasurableSet (scoreEvent H q R p v) :=
  Gaussian.measurable_form (unitKernel H q R v) hp

omit [DecidableEq W] in
theorem card_edgeFinset_of_regular (regular : H.IsRegularOfDegree 3) :
    (H.edgeFinset.card : ℝ) = 3 / 2 * Fintype.card W := by
  have hsum := H.sum_degrees_eq_twice_card_edges
  simp only [regular.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have : ((Fintype.card W * 3 : ℕ) : ℝ) = ((2 * H.edgeFinset.card : ℕ) : ℝ) := by
    exact_mod_cast hsum
  push_cast at this
  linarith

/-- The deviation event of a count of local events. -/
def deviation {κ : Type} (F : Finset κ) (A : κ → Set (W → ℝ)) (c : ℝ) : Set (W → ℝ) :=
  {ω | c ≤ |∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω -
    ∑ k ∈ F, (gaussPi W).real (A k)|}

omit [DecidableEq W] in
theorem lt_of_notMem_deviation {κ : Type} {F : Finset κ} {A : κ → Set (W → ℝ)} {c : ℝ}
    {ω : W → ℝ} (h : ω ∉ deviation F A c) :
    ∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω < ∑ k ∈ F, (gaussPi W).real (A k) + c := by
  simp only [deviation, Set.mem_ofPred_eq, not_le] at h
  linarith [le_abs_self (∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω -
    ∑ k ∈ F, (gaussPi W).real (A k))]

end Algebraic.Cutwidth.Gaussian.Internal
