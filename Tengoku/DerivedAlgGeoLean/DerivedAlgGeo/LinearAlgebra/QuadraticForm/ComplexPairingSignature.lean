/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.LinearAlgebra.QuadraticForm.ComplexPairing
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.LinearAlgebra.QuadraticForm.PositiveFrame
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Signature consequences for a paired complex functional

This downstream module combines the wall-independent functional/kernel algebra
with positive-plane and signature theory. Kernel negativity is one half of a
quadratic support criterion; it is not by itself the full support property.
-/

open QuadraticMap Complex

namespace PeriodDomain

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}
variable [FiniteDimensional ℝ M]

/-- On the kernel of the paired complex functional the form is negative
definite. A full support claim additionally requires nonnegativity on the
relevant semistable classes.
@isnad1 id=lt.4h5v.s7.a6c9e52f0d4b from=translated src=- shape=a4be77e9 vocab=5ff58570
-/
theorem neg_of_centralCharge_eq_zero (hsig : HasSignatureTwo Q) {x y : M}
    (hxy : IsPositiveFrame Q x y) {v : M} (hv : centralCharge Q x y v = 0) (hv0 : v ≠ 0) :
    Q v < 0 :=
  neg_of_mem_orthogonal hsig hxy (centralCharge_eq_zero_iff.mp hv) hv0

/-- No nonzero class of nonnegative square lies in the kernel.
@isnad1 id=ne.4h5v.s7.5664c10c171e from=translated src=- shape=0b008251 vocab=8d900a8a
-/
theorem centralCharge_ne_zero_of_nonneg (hsig : HasSignatureTwo Q) {x y : M}
    (hxy : IsPositiveFrame Q x y) {v : M} (hv : 0 ≤ Q v) (hv0 : v ≠ 0) :
    centralCharge Q x y v ≠ 0 := by
  intro hzero
  have := neg_of_centralCharge_eq_zero hsig hxy hzero hv0
  linarith

/-- The positive-frame span and the functional kernel split the space.
@isnad1 id=iscompl.1h4v.s6.0f931a04690b from=translated src=- shape=89b88b74 vocab=bf94af84
-/
theorem isCompl_ker_centralCharge {x y : M} (hxy : IsPositiveFrame Q x y) :
    IsCompl (pairSpan x y) (orthogonal Q (pairSpan x y)) :=
  isCompl_orthogonal hxy

end PeriodDomain
