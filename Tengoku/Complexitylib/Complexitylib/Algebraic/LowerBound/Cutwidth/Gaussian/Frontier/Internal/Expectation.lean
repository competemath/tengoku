/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Internal.Vector
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Order
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Star
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Arccos
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Decay
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Exact
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Expectation

/-!
# Expected straddling vertices of the edge-score order

A threshold separates two Gaussian edge scores with probability at most `arccos ρ' / π`
(Sheppard's bound), where `ρ'` is the correlation of the edge vectors. The three edge vectors
at a vertex are within correlation `√((1 + ρ₀)/2)` of the vertex row, so the star inequality
bounds their summed angles. A straddling vertex has at least four separated ordered pairs,
so it straddles a threshold with probability at most `(3/(2π)) arccos ((1 + 3ρ₀)/4)`.
The threshold-decay crossing bound multiplies this by `exp (-t²/2)` at the threshold `t`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- The per-vertex straddling bound for edge correlations at least `ρ₀`. -/
noncomputable def frontierBound (ρ₀ : ℝ) : ℝ :=
  3 / (2 * Real.pi) * Real.arccos ((1 + 3 * ρ₀) / 4)

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The event that the edge scores at `v` straddle `t`. -/
def straddleEvent (q : ℝ) (R : ℕ) (t : ℝ) (v : W) : Set (W → ℝ) :=
  {ω | EdgeStraddles H (edgeScore H q R ω) t v}

omit [DecidableEq W] in

end Algebraic.Cutwidth.Gaussian.Internal
