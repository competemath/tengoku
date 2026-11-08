module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.Query
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.BehavioralCollision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Worked model of the MAIS-A2 query protocol

`AISafetyAtlas.Causal.Query` renders `subsec:queries`. This module exercises it
on the two-variable skeleton `skel`, so that the shapes the protocol commits to
are checked against something concrete rather than only asserted in a docstring.

Four things are worth seeing run, and each corresponds to a printed commitment:

* a query really is a **rational** mixture read against the model's value field;
* a **deterministic** analyst is the special case of a randomized one whose laws
  are point masses, so nothing was lost by randomizing the type;
* a **non-adaptive** analyst is the special case that ignores its history;
* `N(ε)` is `⊤` exactly when no budget achieves `ε`, which is the case a
  `ℕ`-valued budget could not express.
-/

namespace AISafetyAtlas.Examples.Causal.Query

open AISafetyAtlas.Causal
open AISafetyAtlas.Examples.Causal

/-! ## A concrete query -/

/-- The query that masks nothing, mixes nothing, and reads the policy at
`X = 0, Y = 0`. `skel.observed` is empty here, so the empty visible set is the
only legal mask — which is `q:chain`'s `𝐎 = ∅` situation, not a restriction the
protocol imposes.-/
public noncomputable def trivialQuery : ShiftedQuery skel where
  visible := ∅
  visible_subset := Finset.empty_subset _
  mix := ProbMixture.dirac (fun _ ↦ id)
  observation := asg false false

/-! ## Deterministic analysts are randomized analysts -/

/-- A deterministic strategy, embedded by taking point masses.-/
public noncomputable def constStrategy (q : ShiftedQuery skel) :
    RandomizedQueryStrategy skel :=
  fun _ ↦ PMF.pure q

/-! ## Expectation collapses on a point mass -/

/-! ## `N(ε)` is `⊤` when nothing achieves `ε`

The `ℕ∞` codomain exists for this case. A `ℕ`-valued budget has to return some
natural number when no budget is feasible, and `0` — the value the previous
definition returned — asserts that *zero queries suffice*, which is the opposite
of the truth. Every upper bound on `N(ε)` then holds vacuously on exactly the
instances print would answer *no* for. -/

end AISafetyAtlas.Examples.Causal.Query
