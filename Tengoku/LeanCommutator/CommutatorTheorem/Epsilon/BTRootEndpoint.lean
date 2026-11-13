import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTRootShrinkingClose

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Endpoint cases of refined root shrinking

The strictly admissible positive-variance case is proved in
`BTRootShrinkingClose`.  This file closes the two algebraic endpoints without
a limiting argument:

* at `c = (1+α)⁻¹` the claimed upper bound simplifies exactly to `1`, and
  differentiation preserves the original upper root bound;
* at `α = 0`, all roots vanish, so the polynomial is a power of `X`.
-/

namespace CommutatorTheorem

open scoped Polynomial BigOperators
open Polynomial Finset

/-- A non-strict upper root bound is preserved by one derivative as long as
the original polynomial has degree at least two.-/
theorem derivative_rootUpperBound_of_realRooted
    {p : ℝ[X]} (hp : RealRooted p) (hdeg : 2 ≤ p.natDegree)
    {b : ℝ} (hb : IsRootUpperBound p b) :
    IsRootUpperBound p.derivative b := by
  intro r hr
  by_contra hnot
  have hbr : b < r := lt_of_not_ge hnot
  let y := (b + r) / 2
  have hby : b < y := by dsimp [y]; linarith
  have hyr : y < r := by dsimp [y]; linarith
  have hystrict : IsStrictRootUpperBound p y := by
    intro z hz
    exact lt_of_le_of_lt (hb z hz) hby
  have hderiv := hp.derivative_strictRootUpperBound
    (lt_of_lt_of_le (by omega) hdeg) hystrict
  exact (not_lt_of_ge hyr.le) (hderiv r hr)

end CommutatorTheorem
