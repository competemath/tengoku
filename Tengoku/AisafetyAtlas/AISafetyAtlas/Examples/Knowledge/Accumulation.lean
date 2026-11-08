module

import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge.Accumulation
import Tengoku.Seed.Data.Fintype.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Accumulation is possible, bounded, and not automatic

`Knowledge.Accumulation` brackets window ambiguity between "never decreases" and
"at most the product". Neither bound says growth *happens* — that depends on
whether each step adds a distinction the observation cannot see, which is a
statement about dynamics this layer does not have.

Both extremes are exhibited here:

* a blind observer, where ambiguity **doubles per step** and hits the product
  ceiling exactly — `2 ^ k` over a `k`-step window;
* a fully informed observer, where ambiguity stays `1` no matter how wide the
  window gets, so the left bound holds with equality and nothing accumulates.

The second is the one that keeps the first honest. "Ambiguity accumulates" is a
property of a *situation*, not a theorem about windows.
-/

namespace AISafetyAtlas.Examples.Knowledge.Accumulation

open AISafetyAtlas.Knowledge

/-! ## A blind observer: doubling per step

Three independent bits; the observation reveals nothing. Each step of the window
adds a factor of two, and the product ceiling is met exactly. -/

private abbrev Hist3 := Bool × Bool × Bool

private def blind : Hist3 → Unit := fun _ => ()

private def bit0 : Hist3 → Bool := fun ω => ω.1
private def bit1 : Hist3 → Bool := fun ω => ω.2.1
private def bit2 : Hist3 → Bool := fun ω => ω.2.2

/-! ## An informed observer: no accumulation at all

The same three bits, but the observation is the whole history. Ambiguity is `1`
at every window width, so the left bound holds with equality and widening costs
nothing. -/

private def seeAll : Hist3 → Hist3 := id

/-! ## The other axis: waiting pays

Widening a window costs ambiguity. Reading later recovers it, and the two bounds
compose. Here evidence is blind at time `0` and complete from time `1`, so the
same target goes from ambiguity `2` to ambiguity `1` purely by waiting. -/

private def evidence : ℕ → Hist3 → Hist3 :=
  fun t ω => if t = 0 then (false, false, false) else ω

private theorem evidence_monotone : Temporal.EvidenceMonotone evidence := by
  intro t t' hle
  by_cases ht : t = 0
  · -- Blind at `t`, so a constant decoder works whatever the later reading is.
    exact ⟨fun _ => (false, false, false), by intro ω; simp [evidence, ht]⟩
  · -- Otherwise the later time is nonzero too, and both readings are the identity.
    have ht' : t' ≠ 0 := fun h => ht (Nat.le_zero.mp (h ▸ hle))
    exact ⟨id, by intro ω; simp [evidence, ht, ht']⟩

/-! ## What this does not show

Neither model has dynamics. The bits do not evolve; they are components of a
history fixed in advance. So "doubling per step" here is a property of how the
observation relates to the components, not a rate at which a running system
generates unobserved distinctions. Stating the latter needs a transition system,
and would be the first genuine use of `Knowledge.Temporal` beyond indexing. -/

end AISafetyAtlas.Examples.Knowledge.Accumulation
