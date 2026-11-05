/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Resolution.Algebraic.Monomial.State
import Tengoku.Hironaka.HironakaExamples.Monomial.Examples
import Tengoku.Hironaka.Hironaka.Resolution.Algebraic.Monomial.Step3Phases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The monomial order-reduction run on the combinatorial state: worked examples

Examples of the run `step3` of [Kol07, Theorem 107, Step 3 of the proof] (order reduction for a
monomial ideal supported on a simple normal crossing divisor with ordered components) on the
combinatorial state `MonomialState`, decided by `decide` (never `native_decide`) through the
fuelled copies `step3Fuel`/`maxMultRun` and the agreement theorem `step3_map_eq_of_step3Fuel`.

* [Kol07, Example 112]: two curves meeting at a point, `a₁ = a₂ = m + 1`. The
  maximal-multiplicity procedure ("look for the highest multiplicity locus and blow it up … does
  not work, not even for surfaces", [Kol07, Theorem 107, Step 3 of the proof]) blows up the point,
  then `E² ∩ E³`, `E³ ∩ E⁴`, …, and the exceptional exponents are `m + p_i` with `p_i` the
  Fibonacci numbers (`3, 4, 6, 9` for `m = 1`): unbounded. Kollár's Step 3 blows up `E¹`, then
  `E²` (trivial blow-ups: the components die and the exceptional components carry `1`), and is
  done with `max-ord = 2` for `m ≥ 3`; for `m = 2` phase 2 blows up the remaining double point
  once; for `m = 1` phase 1 takes two steps per curve: `4, 3, 2, 2, 2` blow-ups for
  `m = 1, 2, 3, 5, 10`.
* A three-phase instance: `n = 3`, `m = 8`, `a = (4, 9, 3, 6)`, maximal faces `{0}` and
  `{1, 2, 3}`; phase 1 blows up `{1}`, phase 2 `{2, 3}`, phase 3 `{3, 4, 5}`, final
  `max-ord = 7 < 8`; the measure vectors `((m_s, n_s))_{s = 1, 2, 3}` are
  `((9,1), (15,1), (18,1))`, `((6,1), (9,1), (10,1))`, `((6,1), (7,2), (8,1))`,
  `((6,1), (7,2), (7,2))`: no pair ever increases.
* The split example: `E¹ = V(x(x-1))`, `E² = V(y(y-1))`, `I = (xy)`, `m = 1`, exponents
  `1, 0, 1, 0` on the four lines; Step 3 blows up `V(x)` then `V(y)` on `X` and on
  `U = D((x-1)(y-1))` alike.
* The nerve rule: three lines in `𝔸²` blown up at a double point; the coordinate planes of `𝔸³`
  blown up at the origin and then along the transform of a line.
-/

@[expose] public section

namespace Hironaka.Monomial.Examples

open Hironaka.Monomial MonomialState Hironaka.Monomial.Examples

/-! ### Example 112 -/

/-! ### A three-phase instance -/

/-! ### The split example -/

/-! ### The nerve rule -/

/-- Three lines `E⁰ = V(x)`, `E¹ = V(y)`, `E² = V(x + y - 1)` in `𝔸²`.-/
def threeLines : MonomialState :=
  ofValid 2 1 3 3 (fun c => c) (fun _ => 0) {{0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}} (by decide)

/-- The coordinate planes of `𝔸³`: the nerve is the full simplex on `{0, 1, 2}`.-/
def planes : MonomialState :=
  ofValid 3 1 3 3 (fun c => c) (fun _ => 0)
    {{0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} (by decide)

end Hironaka.Monomial.Examples
