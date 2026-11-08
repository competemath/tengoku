module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Conjectures.MAIS
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.BehavioralCollision
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.OneNodeClass
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.Query

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Shared checks behind more than one MAIS proof

`def:margin`'s chart dimension on the collision skeleton, and the equality of
the budget under `PMF`-valued and measure-valued analyst outputs, which both
query-complexity problems read.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Examples.Causal

/-! ## `def:margin`'s `K` on this skeleton

`O26ClassAssumptions` carries `IsClassChartDim`, which pins `K` to the
maximum of `K(G) = Σᵢ 2^{|Pa_G(Cᵢ)|}` over the margin class. That is a real
obligation and not a formality: it is what stops `K` from being a free number
that reaches MAIS-O26 only through the rate `K log(1/ε)`, where `K = 0` and
`K = 1` refute the conjecture against each other on one and the same class.

On two chance variables the maximum is `3`, and the upper half of the argument
needs nothing from the margin conditions — acyclicity alone caps it. -/

/-! ## The output-law equality reaches MAIS-O26's own quantifier

`Causal.measureMinimalBudget_eq_exactMinimalBudget_binary` is stated for a
skeleton over any finite binary chance-variable set. MAIS-O26 is stated over
`Fin (m + 1)`, which is an instance of that — but "is an instance of" is a claim
about typeclass resolution, not a proof, and the closure of CONJ-003's scope axis
rests on it. So it is instantiated here rather than asserted. -/

/-- `N(ε)` computed over `PMF`-valued analysts is `N(ε)` computed over arbitrary
output measures, at exactly the skeleton MAIS-O26 quantifies over.-/
public theorem o26_minimalBudget_eq_measure {m : ℕ}
    (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ)
    (modelClass : Set (Model (Fin (m + 1)) (binaryDim (Fin (m + 1))) ℝ)) (ε : ℝ) :
    measureMinimalBudget sk modelClass ε = exactMinimalBudget sk modelClass ε :=
  measureMinimalBudget_eq_exactMinimalBudget_binary sk modelClass ε

/-- The same at MAIS-O25's quantifier, which is the general finite binary one.-/
public theorem o25_minimalBudget_eq_measure {C : Type} [Fintype C] [DecidableEq C]
    [Nonempty C] (sk : Skeleton C (binaryDim C) Bool ℝ)
    (modelClass : Set (Model C (binaryDim C) ℝ)) (ε : ℝ) :
    measureMinimalBudget sk modelClass ε = exactMinimalBudget sk modelClass ε :=
  measureMinimalBudget_eq_exactMinimalBudget_binary sk modelClass ε

end AISafetyAtlas.Examples.Conjectures.MAIS
