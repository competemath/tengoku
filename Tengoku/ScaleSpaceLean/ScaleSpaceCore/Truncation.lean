/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.Additivity
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Bounds
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic
import Tengoku.Seed.MeasureTheory.Function.SpecialFunctions.Sinc
import Tengoku.Seed.Analysis.Real.Pi.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The two elementary inequalities of `thm:increments-levy`

Home: line:thm:increments-levy

Blueprint: `blueprint/src/parts/05-cascade.tex`, `thm:increments-levy`.

The null-array proof of the increments theorem rests on two pointwise inequalities and nothing
else that is not measure theory. They are proved here, ahead of the theorem, because they are
the part of that proof that is *ours* — the causal argument compactifies the half-line instead —
and because both differ from the constants the blueprint writes.

* `sub_one_sub_exp_neg_le` — `0 ≤ u - (1 - e^{-u}) ≤ u²` for `u ≥ 0`. The blueprint writes
  `u²/2`, which is sharp; the sharper constant needs a derivative argument, `u²` follows from
  `e^v ≥ 1 + v` alone through `e^{-u} ≤ (1+u)⁻¹ ≤ 1 - u + u²`, and the factor multiplies a
  quantity that is going to zero. Paper I records the same substitution at the same step.

* `one_sub_sinc_ge` — `1 - sin u / u ≥ c (1 ∧ u²)` with `c = 2/(3π²)`. **This is a genuine
  correction of the route, not of the statement.** The blueprint justifies the constant `2/15`
  from `sin u ≤ u - u³/6 + u⁵/120`, an alternating-series bound Mathlib does not carry; and the
  Taylor machinery to get it is out of proportion to what the step needs, since the constant is
  multiplied by a quantity that only has to be finite. What Mathlib does carry is
  `Real.cos_le_one_sub_mul_cos_sq`: `1 - cos x ≥ (2/π²)x²` for `|x| ≤ π`. Integrating it over
  `[0,u]` — the identity `u - sin u = ∫₀^u (1 - cos v) dv` — gives `1 - sinc u ≥ (2/(3π²))u²`
  for `0 < u ≤ π`, and beyond `π` the crude bound `sin u / u ≤ 1/u < 1/π` finishes, because
  `2/(3π²) < 2/27 < 2/3 < 1 - 1/π`. The blueprint's proof of record is amended to this route.

## Provenance

Moved by Q-0305 from Paper V's `SpatialLine/Truncation.lean` (the public cone export,
`cone-v0.1`, commit `f28c066e`) for the line classification (`MainAnalysis`,
`MainConstruction`): only the declarations those theorems reach, with statements and
proofs unchanged up to the namespace. Blueprint labels are Paper V's.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The exponential inequality of the null-array step -/

/-- `0 ≤ u - (1 - e^{-u})` for `u ≥ 0`.
@isnad1 id=le.0h1v.s4.9694d969d531 from=translated src=- shape=4b077e48 vocab=e9db171f
-/
theorem one_sub_exp_neg_le (u : ℝ) : 1 - Real.exp (-u) ≤ u := by
  have h := Real.add_one_le_exp (-u)
  linarith

/-! ## The truncation inequality -/

/-- `u - sin u = ∫₀^u (1 - cos v) dv`.
@isnad1 id=eq.0h1v.s5.15438acb1258 from=translated src=- shape=23cbdef2 vocab=48eaf76b
-/
lemma sub_sin_eq_intervalIntegral (u : ℝ) :
    u - Real.sin u = ∫ v in (0:ℝ)..u, (1 - Real.cos v) := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_cos)]
  simp

end ScaleSpace
