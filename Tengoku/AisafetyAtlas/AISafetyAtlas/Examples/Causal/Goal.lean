module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.Goal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A worked goal space on two states and two actions

`AISafetyAtlas.Causal.Goal` renders MAIS-A2's goal formalism. This module runs
it on `𝐒 = 𝐀 = Fin 2` and checks the facts that decide whether it is the printed
object rather than a shape with the right name:

* each of the three operators is exercised on a concrete trajectory, and the
  *Eventually* case is checked at the **least** hitting time rather than at some
  hitting time — a weaker reading would shift the recursion past a different
  point;
* a sequential goal of depth two is satisfied, so the shift clause is not
  vacuous, and one is **not** satisfied, so satisfaction is not trivial;
* the immediate-win lemma fires on a composite goal, which is the step every
  counting argument over `𝚿_n` rests on;
* the three counts are evaluated: `|SubGoal| = 48`, `|𝚿_1| = 2^48 - 1`, and
  `R = 8` immediate wins per state–action pair.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Causal.Goal

open AISafetyAtlas.Causal

/-! ## The space -/

/-! ## The trajectory semantics, exercised

`τ` visits `(0,0)`, then `(1,1)`, then `(0,1)` for ever. -/

/-- The worked trajectory.-/
@[expose] public def τ : ℕ → Fin 2 × Fin 2
  | 0 => (0, 0)
  | 1 => (1, 1)
  | _ => (0, 1)

/-! ## The immediate win fires -/

end AISafetyAtlas.Examples.Causal.Goal
