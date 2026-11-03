/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.RealForm
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.LinearAlgebra.QuadraticForm.ComplexPairingSignature
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Mukai.Chart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `Z(β,ω)` on the Mukai extension

The central charge of the exponential pair, written out. For `v = (r, c, s)`:

```
Z (r, c, s) = (b β c - s - r * (b β β - b ω ω) / 2) + i * (b ω c - r * b β ω)
```

which is Bridgeland's `Z(β,ω)` — his `⟪exp(β + iω), v⟫`, with the pairing read
on the real and imaginary parts rather than on a complexified space.

The classes of vanishing charge are exactly the orthogonal complement of the
exponential plane, where the form is negative definite under the signature
hypothesis.  Interpreting that fact as one half of a support condition, or as a
wall statement, belongs to downstream stability modules.

`V` is an arbitrary real bilinear space; no geometry is asserted, and `v(E)` for
an object `E` is not defined here.

## Why this path

This file used to sit in `LinearAlgebra/Lattice/Mukai/`, which put a central
charge inside the quadratic extension it is computed on and let geometry consume
a stability construction without declaring the edge. `expCharge` is
`PeriodDomain.centralCharge` -- the neutral paired functional of
`QuadraticForm/ComplexPairing.lean`, unchanged -- specialised at `realForm` and
at the exponential frame, so it is an application adapter and belongs with the
numerical central-charge construction. `neg_of_expCharge_eq_zero` and
`expCharge_ne_zero_of_nonneg` are the comparison half: the charge kernel against
the sign of `realForm`. They remain the kernel statement only;
`Weak/Support/Predicate/Quadratic.lean` still owns the full support criterion.
-/

open QuadraticMap

namespace Mukai

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V)

/-- **`Z(β,ω)`**: the central charge of the exponential pair.-/
noncomputable def expCharge (v : RealExtension V) : ℂ :=
  PeriodDomain.centralCharge (realForm b) (expRe b β ω) (expIm b β ω) v

/-- **`Z(β,ω)` as an additive homomorphism.**

The exponential charge is linear in the Mukai class.  Exposing that structure
at the numerical layer lets categorical consumers compose class maps with the
charge instead of rebuilding its additivity object by object.-/
noncomputable def expChargeHom : RealExtension V →+ ℂ where
  toFun := expCharge b β ω
  map_zero' := by
    simp [expCharge, PeriodDomain.centralCharge]
  map_add' v w := by
    simp only [expCharge, PeriodDomain.centralCharge, polar_add_right]
    push_cast
    ring

/--
@isnad1 id=eq.0h5v.s7.6be0cf18f8e2 from=translated src=- shape=853344b2 vocab=6517dcb5
-/
@[simp]
theorem expChargeHom_apply (v : RealExtension V) :
    expChargeHom b β ω v = expCharge b β ω v := rfl

/-- **`Z(β,ω)` as an `ℝ`-linear map.**

The additive homomorphism above is enough for the wall arithmetic, but the
    quadratic compatibility predicates downstream are
    stated for an `ℝ`-linear charge.  Real
homogeneity comes from `PeriodDomain.centralCharge_smul`; nothing new is
computed.-/
noncomputable def expChargeLinearMap : RealExtension V →ₗ[ℝ] ℂ where
  toFun := expCharge b β ω
  map_add' := (expChargeHom b β ω).map_add
  map_smul' a v := by
    show expCharge b β ω (a • v) = (a : ℝ) • expCharge b β ω v
    rw [expCharge, expCharge, PeriodDomain.centralCharge_smul, Complex.real_smul]

/--
@isnad1 id=eq.0h5v.s8.e8aa39017b04 from=translated src=- shape=5752a110 vocab=d1110c44
-/
@[simp]
theorem expChargeLinearMap_apply (v : RealExtension V) :
    expChargeLinearMap b β ω v = expCharge b β ω v := rfl

/-- The charge written out on a triple. This is Bridgeland's formula.
@isnad1 id=eq.1h7v.s10.f0fcd5dfb894 from=translated src=- shape=f27a104c vocab=3767ce15
-/
theorem expCharge_apply (hb : ∀ x y : V, b x y = b y x) (r : ℝ) (c : V) (s : ℝ) :
    expCharge b β ω (r, c, s)
      = Complex.ofReal (b β c - s - r * (b β β - b ω ω) / 2)
        + Complex.ofReal (b ω c - r * b β ω) * Complex.I := by
  refine Complex.ext ?_ ?_
  · simp [expCharge, PeriodDomain.centralCharge, polar_realForm b hb, realPairing, expRe, expIm]
    ring
  · simp [expCharge, PeriodDomain.centralCharge, polar_realForm b hb, realPairing, expRe, expIm]

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- A nonzero class of vanishing charge has negative square. This is the kernel
half of a quadratic support criterion, not the full support property.
@isnad1 id=lt.5h5v.s10.9cf4256c0000 from=translated src=- shape=6c74b7a2 vocab=d289f37a
-/
theorem neg_of_expCharge_eq_zero
    (hsig : PeriodDomain.HasSignatureTwo (realForm b)) (hb : ∀ x y : V, b x y = b y x)
    (hω : 0 < b ω ω) {v : RealExtension V} (hv : expCharge b β ω v = 0) (hv0 : v ≠ 0) :
    realForm b v < 0 :=
  PeriodDomain.neg_of_centralCharge_eq_zero hsig (isPositiveFrame_exp b β ω hb hω) hv hv0

/-- No nonzero class of nonnegative square is killed by `Z(β,ω)`.
@isnad1 id=ne.5h5v.s10.e93e6d7024f8 from=translated src=- shape=049ecd26 vocab=32191eef
-/
theorem expCharge_ne_zero_of_nonneg
    (hsig : PeriodDomain.HasSignatureTwo (realForm b)) (hb : ∀ x y : V, b x y = b y x)
    (hω : 0 < b ω ω) {v : RealExtension V} (hv : 0 ≤ realForm b v) (hv0 : v ≠ 0) :
    expCharge b β ω v ≠ 0 :=
  PeriodDomain.centralCharge_ne_zero_of_nonneg hsig (isPositiveFrame_exp b β ω hb hω) hv hv0

end FiniteDimensional

end Mukai

namespace Mukai

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V)

/-! The elementary charge identities are projections of `expChargeHom`. -/

/-- The exponential charge kills the zero class.
@isnad1 id=eq.0h4v.s7.cc4a1370552d from=translated src=- shape=2b4f49d1 vocab=4df2f539
-/
@[simp]
theorem expCharge_zero : Mukai.expCharge b β ω 0 = 0 :=
  (expChargeHom b β ω).map_zero

/-- The exponential charge is additive in the Mukai class.
@isnad1 id=eq.0h6v.s7.e0efa1c421a3 from=translated src=- shape=f8ae9242 vocab=f695b7af
-/
theorem expCharge_add (v w : Mukai.RealExtension V) :
    Mukai.expCharge b β ω (v + w) =
      Mukai.expCharge b β ω v + Mukai.expCharge b β ω w :=
  (expChargeHom b β ω).map_add v w

/-- The exponential charge negates on negated classes.
@isnad1 id=eq.0h5v.s7.2da50f10a130 from=translated src=- shape=1d4b4505 vocab=737c1761
-/
theorem expCharge_neg (v : Mukai.RealExtension V) :
    Mukai.expCharge b β ω (-v) = -Mukai.expCharge b β ω v :=
  (expChargeHom b β ω).map_neg v

end Mukai
