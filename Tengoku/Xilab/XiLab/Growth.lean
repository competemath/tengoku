import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# XiLab.Growth — the shared growth predicate

`OrderOne.lean` proves its factorization theorems under
`‖f z‖ ≤ A * exp (B * ‖z‖)`, which is order ≤ 1 **of finite exponential type**.

The Riemann kernel's odd channel `F` is NOT of finite type. Its bound is
`log max_{‖w‖ = r} ‖F‖ ≤ (r / 2) * log r + O(r)`, which outgrows every `B * r`;
`F` is order 1 of *maximal* type, exactly like `ξ` itself. So the finite-type
hypothesis is too strong for the intended application and the two halves of
XiLab do not compose without this weaker predicate.

This file fixes the predicate that the growth producer (`FGrowth.lean`) and the
growth consumer (`OrderOneGen.lean`) must both use, so they cannot drift apart.

This definition is shared by `FGrowth.lean` (its producer) and
`OrderOneGen.lean` (its consumer); do not edit it without updating both.
-/

namespace XiLab

/-- `f` has **order at most one**: for every `ε > 0` there is `C > 0` with
`‖f z‖ ≤ C * exp (C * ‖z‖ ^ (1 + ε))` for all `z`.

This is the classical order-≤-1 condition. It is strictly weaker than finite
exponential type: it admits `log M(r) ~ r log r`, which is the actual growth of
`F`.-/
def HasOrderLeOne (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ ^ (1 + ε))

end XiLab
