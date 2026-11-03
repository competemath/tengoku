/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.Surface.K3
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.MukaiVector

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Mukai data of the rank-one K3 model

`GrothendieckGroup/MukaiVector.lean` says in its own "What this file does not
assert" section that nothing constructs an `IntegralMukaiData` and nothing
constructs an `AdditiveMukaiData`. This file meets that hypothesis, on the
degree-`2d` rank-one model `k3NumericalVariety d`, with

```
Λ = ℤ        c₁(E) = E 1        b x y = 2d·x·y
```

## What an inhabitant buys, without a line changing anywhere else

Every consumer of `IntegralMukaiData` on `main` takes one as a hypothesis, so
each is a statement about a structure nothing was known to satisfy. Supplying
one de-vacuates all of them at once: `GrothendieckGroup/CentralChargeK3.lean`,
`CategoricalCharge.lean`, `RadicalKernel.lean`, `Realization.lean` (the
`preservesEuler` family and the two isometry constructions), `EulerTransfer.lean`
and `Walls/Spherical/Basic.lean`.

## The three coordinates

`mukaiVector` is `(rank, c₁, mukaiSInt)` and `mukaiSInt = χ − rank`. On this
model `χ(E) = 2·E 0 + 2d·E 2` and `rank E = E 0`, so

```
v(E) = (E 0, E 1, E 0 + 2d·E 2)
```

which `mukaiVector_k3` records. Two classes are worth naming: the structure
sheaf `![1,0,0]` has `v = (1,0,1)` and is **spherical**, and the point class
`![0,0,1]` has `v = (0,0,2d)` and is **isotropic**. Those are the two
distinguished classes of `Mukai/Basic.lean`, inhabited here for the first time.

## `d ≠ 0` is needed less often than expected

The Mukai-vector computations below are evaluations on the model, not
consequences of Riemann–Roch, so they hold for every `d` — including `d = 0`,
where the "K3" is degenerate. Only `mukaiPairing_k3`, which crosses to
`mukaiPairing` through `pairing_mukaiVector`, needs `SatisfiesHRR` and `IsK3`
and hence `d ≠ 0`. Carrying `hd` on the others would be a hypothesis nothing
uses.

## Main results

* `k3MukaiForm`, `k3IntegralMukaiData`, `k3AdditiveMukaiData` — the witnesses.
* `mukaiVector_k3` and `pairing_mukaiVector_k3` — the coordinates and the
  pairing, evaluated.
* `mukaiPairing_k3` — the bridge to `mukaiPairing`, where `d ≠ 0` is spent.
* `isSpherical_structureSheaf_k3`, `isIsotropic_point_k3`.
-/

namespace AlgebraicGeometry.Numerical.Examples

open AlgebraicGeometry.Numerical

/-! ### The form and the data -/

/-- The Mukai form of the degree-`2d` model on `Λ = ℤ`: `⟪x, y⟫ = 2d·x·y`.

This is the intersection form of the rank-one Néron–Severi lattice `ℤ·H` with
`∫H² = 2d`, which is what `b_spec` has to reproduce.-/
def k3MukaiForm (d : ℕ) : ℤ →ₗ[ℤ] ℤ →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun x y => 2 * (d : ℤ) * x * y)
    (fun _ _ _ => by ring) (fun _ _ _ => by ring)
    (fun _ _ _ => by ring) (fun _ _ _ => by ring)

/--
@isnad1 id=eq.0h3v.s8.5bbd070096e3 from=translated src=- shape=f2ae786d vocab=9a464acc
-/
@[simp]
theorem k3MukaiForm_apply (d : ℕ) (x y : ℤ) :
    k3MukaiForm d x y = 2 * (d : ℤ) * x * y := rfl

/-! ### The coordinates, evaluated -/

/-! ### The two distinguished classes -/

end AlgebraicGeometry.Numerical.Examples
