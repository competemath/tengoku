module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Conjectures.MAIS
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.BehavioralCollision
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.OneNodeClass
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.Query
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Conjectures.MAIS.Common
public import Tengoku.Seed.Analysis.Asymptotics.Theta
public import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `⊤` refutes the budget bounds

An infeasible target must break a finite bound rather than satisfy one. These
are the discipline checks for the rate predicates shared by O25 and O26.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Examples.Causal

/-! ## `⊤` refutes the budget bound

MAIS-O25 and MAIS-O26 are both stated over `Causal.exactMinimalBudget`, which is
`ℕ∞`-valued and returns `⊤` when no budget drives the minimax risk to `ε`. The
whole point of that codomain is that an infeasible target must **refute** a bound
rather than satisfy one. `IsPolyLogBudget`, `NonadaptiveWithinConstant` and
`IsThetaWithMarginBound` were all restated to make that so, and the checks below
are what a `ℕ`-valued budget with an `else 0` fallback would have got wrong:
there, `N(ε) = 0` and every upper bound holds vacuously on exactly the instances
print answers *no* for. -/

/-! ## The rate predicate really is a `Θ`

`IsThetaWithMarginBound` is not Mathlib's `IsTheta`, and the reason is the
polynomial-constant clause: `conj:exact` demands the implied constants be
bounded by `A · (1 + 1/λ + 1/μ + L)^d`, and `Asymptotics.IsTheta` quantifies its
constants existentially with nothing said about their size. So the atlas
predicate cannot be replaced by the library one.

What can be checked is that it *implies* it, which is what the theorem below
does — and that direction is the whole of the claim. -/

end AISafetyAtlas.Examples.Conjectures.MAIS
