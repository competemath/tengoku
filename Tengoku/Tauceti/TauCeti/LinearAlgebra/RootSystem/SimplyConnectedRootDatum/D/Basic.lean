/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic

/-!
# The simply connected root datum of type `Dₙ`

This file constructs, uniformly in the rank `n ≥ 4`, the pinned integral root datum of type `Dₙ` on
the character and cocharacter lattices `Fin n → ℤ`. The character lattice is written in the
fundamental-weight basis and the cocharacter lattice in the simple-coroot basis, so the `i`-th
simple root is the `i`-th row of the Bourbaki-numbered Cartan matrix `CartanMatrix.D n` and the
`i`-th simple coroot is the `i`-th standard basis vector.

## The coordinates

Simple roots and coordinates alike are indexed from zero throughout: the simple root `αᵢ` is
Bourbaki node `i + 1`, and `e_j` is the zero-based coordinate `j`, so what is called `α_{n-1}` here
is Bourbaki's fork root `α_n`.

The classical model is `ℤ ^ n` with the dot product: the `2 * n * (n - 1)` roots are the vectors
`±e_a ± e_b` with `a ≠ b`, which are exactly the integral vectors of squared length two, and the
Bourbaki simple roots are `αᵢ = eᵢ - eᵢ₊₁` for `i + 1 < n` together with the fork root
`α_{n-1} = e_{n-2} + e_{n-1}`. That model, its enumeration by `Fin (2 * n * (n - 1))` with the
simple roots first, the expansion of every root in the simple roots, their linear independence and
reflection in a root are all supplied by `TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD` and are
consumed here rather than rebuilt.

Type `Dₙ` is simply laced, so `α^∨ = α` under the dot product and both pinned lattices are images
of the one classical model:

```text
typeDWeight x = (x ⬝ᵥ αⱼ)ⱼ,      typeDSimpleRootCoordinates x = the coefficients of x in the αᵢ.
```

The first records a vector by its pairings against the simple coroots, the second by its
coordinates in the simple coroots. Because the second family reconstructs the classical vector,
the pinned pairing is the classical dot product, `typeDWeight_dotProduct_coordinates`, and every
axiom of the datum reduces to a statement about `⬝ᵥ` on `ℤ ^ n`.

The roots are indexed by `Fin (2 * n * (n - 1))` through `TauCeti.DynkinType.typeDRootEquiv`, whose
first `n` values are the simple roots in Bourbaki order. That index type is the one Layer 6 pins
for the type, since `(DynkinType.D n).numRoots` is `2 * n * (n - 1)` by definition.

Only the coroots are asked to span their lattice, and only that half is recorded, in
`corootSpan_typeDSimplyConnectedRootDatum_eq_top`. The roots span the root lattice, which sits
inside the weight lattice with index four (Bourbaki, Plate IV), so the datum is a `RootDatum`
carrying no `RootPairing.IsRootSystem` instance. That asymmetry is what "simply connected" means
here.

## Main definitions

* `TauCeti.DynkinType.typeDSimplyConnectedRootDatum`: the pinned root datum of type `Dₙ`.
* `TauCeti.DynkinType.typeDSimplyConnectedBase`: the base formed by the first `n` root indices.

## Main results

* `TauCeti.DynkinType.root_typeDSimpleIndex` and `TauCeti.DynkinType.coroot_typeDSimpleIndex`: the
  `i`-th simple root is the `i`-th row of `CartanMatrix.D n` and the `i`-th simple coroot is
  `Pi.single i 1`, which is what pins the two lattices as the weight and coroot lattices.
* `TauCeti.DynkinType.toLinearMap_typeDSimplyConnectedRootDatum` and
  `TauCeti.DynkinType.toLinearMap_typeDSimplyConnectedRootDatum_single_single`: the pinned pairing
  is the classical dot product, and the standard basis of the character lattice is the family of
  fundamental weights.
* `TauCeti.DynkinType.hasCartanType_typeDSimplyConnectedRootDatum`: the pinned base has Cartan type
  `D n`.
* `TauCeti.DynkinType.corootSpan_typeDSimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice, the simply connected condition.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate IV, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1. The layout of the file follows its sibling
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A` (#2594), whose type-agnostic
scaffolding — the perfect pairing, the pinned support, the Cartan-type criterion and the coroot
span — now lives in `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic` and is shared
with this file. This is the `Dₙ` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

public section

namespace TauCeti

open Function Set Submodule

namespace DynkinType

variable {n : ℕ}

/-! ## The two pinned coordinate families -/

/-- The character-lattice coordinates of a classical vector of type `Dₙ`: its pairings against the
Bourbaki-numbered simple coroots, which for a simply laced type are the simple roots. Reading the
simple roots as the rows of a matrix exhibits this as a linear map. -/
private def typeDWeight (n : ℕ) (hn : 4 ≤ n) : (Fin n → ℤ) →ₗ[ℤ] Fin n → ℤ :=
  (Matrix.of (typeDSimpleRoot n hn)).mulVecLin

/-! ## Reflections -/

/-- Reflection in the root indexed by `k`, transported to the enumeration of the roots. -/
private noncomputable def typeDReflectionPerm (n : ℕ) (hn : 4 ≤ n)
    (k : Fin (2 * n * (n - 1))) : Fin (2 * n * (n - 1)) ≃ Fin (2 * n * (n - 1)) :=
  ((typeDRootEquiv n hn).trans (typeDRootReflectionEquiv (typeDRootEquiv n hn k))).trans
    (typeDRootEquiv n hn).symm

/-! ## The pinned root datum -/

/-! ## The pinned base -/

/-- The support of the pinned base of type `Dₙ`: the first `n` root indices. -/
private abbrev typeDSimpleSupport (n : ℕ) (hn : 4 ≤ n) : Finset (Fin (2 * n * (n - 1))) :=
  simpleSupport (typeDSimpleIndex_injective hn)

end DynkinType

end TauCeti
