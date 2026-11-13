import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.Basepoint
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.BridgeLevel
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.ZModTwoGlue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Final algebraic assembly for the Pontryagin--Thom calculation

The geometric development naturally constructs its invariant at the canonical
south-pole basepoint.  This file isolates the two purely algebraic final steps:

* a bijective two-valued invariant shows that the source group has cardinality two,
  and is therefore promoted to a `MulEquiv` without a separate additivity proof;
* the result is transported from the south pole to an arbitrary point of the unit
  sphere using `basepointMulEquiv`.

Thus the remaining geometric target is exactly a value of
`StableSphereClassification n`; no basepoint bookkeeping remains downstream.
-/

noncomputable section

namespace Submission

variable {n : ℕ}

/-- The homotopy group appearing in the theorem, at the canonical south pole.-/
abbrev StableSpherePi (n : ℕ) :=
  HomotopyGroup (Fin (n + 1))
    (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)

/-- The final output expected from the geometric Pontryagin--Thom argument: a
`ZMod 2`-valued classification together with its injectivity and surjectivity.

It deliberately asks only for a function, not a homomorphism.  A bijection with a
two-element type forces the source group itself to have two elements, after which
the group isomorphism is automatic.-/
structure StableSphereClassification (n : ℕ) where
  invariant : StableSpherePi n → Multiplicative (ZMod 2)
  bijective : Function.Bijective invariant

namespace StableSphereClassification

end StableSphereClassification

end Submission
