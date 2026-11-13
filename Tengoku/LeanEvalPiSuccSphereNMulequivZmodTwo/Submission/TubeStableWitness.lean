import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.TubeCollapse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dimension-uniform tube witnesses

`TubeCollapse` constructs the twist-`k` Thom class with dimension written as
`m + 2`.  The final theorem is indexed by an arbitrary `n ≥ 3`; this file performs
that dependent dimension transport once and records the correct delta convention.

For a single framed circle, `delta = frameClass + 1`.  The explicit derivative
frame contains the unavoidable tangent turn as well as the prescribed normal
twist, so its class is `k + 1` and its delta is `k`.  Hence the untwisted tube
has delta `0`, while the once-twisted tube has delta `1`.
-/

noncomputable section

namespace Submission

/-- Transport a stable sphere class across an equality of dimensions.-/
def stableSpherePiCast {n n' : ℕ} (h : n = n') :
    StableSpherePi n → StableSpherePi n' := by
  subst n'
  exact id

/-- The explicit twist-`k` Thom class in every dimension at least two.

This is an abbreviation so that bridge data indexed by the transported class
remains definitionally visible to dependent projections.-/
abbrev tubeTwistStableClass (n : ℕ) (hn : 2 ≤ n) (k : ℕ) : StableSpherePi n :=
  stableSpherePiCast (Nat.sub_add_cancel hn)
    (tubeThomStableClass (m := n - 2) k)

/-- The class intended to realize delta zero: the untwisted tube.-/
def tubeDeltaZeroClass (n : ℕ) (hn : 2 ≤ n) : StableSpherePi n :=
  tubeTwistStableClass n hn 0

/-- The class intended to realize delta one: the once-twisted tube.-/
def tubeDeltaOneClass (n : ℕ) (hn : 2 ≤ n) : StableSpherePi n :=
  tubeTwistStableClass n hn 1

/-- Expected delta of the standard twist-`k` northern fiber.-/
def tubeExpectedDelta (k : ℕ) : ZMod 2 := tubeTwistParity k

/--
@isnad1 id=eq.0h0v.s6.1eebfa051d14 from=translated src=- shape=3a1213c4 vocab=95388396
-/
@[simp] theorem tubeExpectedDelta_zero : tubeExpectedDelta 0 = 0 := by
  rfl

/--
@isnad1 id=eq.0h0v.s6.8d4bc089734e from=translated src=- shape=3a1213c4 vocab=95388396
-/
@[simp] theorem tubeExpectedDelta_one : tubeExpectedDelta 1 = 1 := by
  rfl

/-- The local tube framing contract computes the expected one-component delta.
@isnad1 id=eq.0h2v.s4.e6aa0c451ea4 from=translated src=- shape=a9dbed4d vocab=a9960861
-/
theorem tubeNorthFiberContract_expectedDelta (m k : ℕ) :
    (tubeNorthFiberContract (m := m) k).parity = tubeExpectedDelta k := by
  rw [tubeNorthFiberContract_parity]
  rfl

/-- The two standard tubes have different expected delta values.
@isnad1 id=ne.0h0v.s4.3f994b7cc1b3 from=translated src=- shape=2560e880 vocab=95388396
-/
theorem tubeExpectedDelta_zero_ne_one :
    tubeExpectedDelta 0 ≠ tubeExpectedDelta 1 := by
  decide

end Submission
