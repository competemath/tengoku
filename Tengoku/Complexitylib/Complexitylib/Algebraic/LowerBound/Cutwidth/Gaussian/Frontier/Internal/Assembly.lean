/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Internal.Expectation
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Assembly

/-!
# A good sample for the edge-score decomposition

Fix thresholds `-T + i δ` with `δ = 2T / M`. For each threshold count the vertices whose edge
scores straddle it and the edges scoring in the following window, and count the edges in both
tails. Each count is a sum of local events, so it deviates from its mean by `ε h` with
probability `O(1 / h)`. For large cubic graphs some sample keeps all counts near their means,
and the edge-score decomposition of that sample has bags of at most
`h · frontierLayoutBound ρ₀ T ε M` vertices.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- The bag bound of the edge-score decomposition with the given parameters, per vertex. -/
noncomputable def frontierLayoutBound (ρ₀ T ε : ℝ) (M : ℕ) : ℝ :=
  max (3 / T ^ 2 + 2 * ε)
    (frontierBound ρ₀ + 3 * (2 * T / M) / Real.sqrt (2 * Real.pi) + 3 * ε)

theorem card_filter_eq_sum_indicator' {Ω κ : Type} (F : Finset κ) (A : κ → Set Ω) (ω : Ω) :
    ((F.filter fun k => ω ∈ A k).card : ℝ) = ∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : ω ∈ A k <;> simp [h]

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- An event about one edge score. -/
def edgeScoreEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (e : Sym2 W) : Set (W → ℝ) :=
  {ω | p (edgeScore H q R ω e)}

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem measurableSet_edgeScoreEvent (q : ℝ) (R : ℕ) {p : ℝ → Prop}
    (hp : MeasurableSet {x | p x}) (e : Sym2 W) : MeasurableSet (edgeScoreEvent H q R p e) :=
  measurable_edgeScore H q R e hp

omit [DecidableRel H.Adj] in
theorem dependsOn_edgeScoreEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (e : Sym2 W) :
    DependsOn (· ∈ edgeScoreEvent H q R p e) (edgeSupport H R e : Set W) := by
  intro ω ω' h
  simp only [edgeScoreEvent, Set.mem_ofPred_eq]
  rw [edgeScore_congr H le_rfl fun i hi => h i hi]

omit [DecidableEq W] in
/-- Edge vectors of a graph with large kernel correlations are unit vectors. -/
theorem sum_edgeVector_sq_of_mem (degree : ∀ v, H.degree v ≤ 3) {q : ℝ} (hq0 : 0 ≤ q)
    {R : ℕ} {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀) (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    {e : Sym2 W} (he : e ∈ H.edgeFinset) : ∑ z, edgeVector H q R e z ^ 2 = 1 := by
  induction e using Sym2.ind with
  | _ u v =>
  have hadj : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
  have hcorr := hρ.trans (sum_unitKernel_mul_ge H degree hq0 R hadj)
  exact sum_edgeVector_sq H (by rw [pairNormSq_eq]; linarith)

end Algebraic.Cutwidth.Gaussian.Internal
