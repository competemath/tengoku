/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.NumberOfRoots
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.Datum
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.C.Datum
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.Basic
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.Basic
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.Datum
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Datum
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.Basic
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Basic

/-!
# The pinned simply connected root datum of a Dynkin type

This file assembles the explicit simply connected root data for the nine irreducible
crystallographic Dynkin families into one construction indexed by a valid
`TauCeti.DynkinType`. Both lattices are `Fin t.rank → ℤ`: the character lattice uses the
fundamental-weight basis and the cocharacter lattice uses the simple-coroot basis. Roots are
indexed by `Fin t.numRoots`, with the first `t.rank` indices the Bourbaki-numbered simple roots.

The construction dispatches directly to the coordinate data in the family modules imported
above. It does not choose a root datum from a realization theorem. The branch equations below
make this explicit data available without requiring downstream users to unfold the dispatcher.

## Main definitions

* `TauCeti.DynkinType.simplyConnectedRootDatum`: the pinned datum of a valid Dynkin type.
* `TauCeti.DynkinType.simplyConnectedBase`: its Bourbaki-numbered base.
* `TauCeti.DynkinType.simpleIndex`: the first `t.rank` root indices in Bourbaki order.

## Main results

* `TauCeti.DynkinType.hasCartanType_simplyConnectedRootDatum`: the pinned datum realizes its
  indexing Dynkin type.
* `TauCeti.DynkinType.span_coroot_simplyConnectedRootDatum`: its coroots span the cocharacter
  lattice.
* `TauCeti.DynkinType.root_simpleIndex`, `coroot_simpleIndex`, and
  `mem_support_simplyConnectedBase`: the entrywise pinning of the simple roots and base.
* `TauCeti.DynkinType.pairing_simpleIndex` and `TauCeti.DynkinType.pairingIn_simpleIndex`: the
  Cartan integers at the simple indices are the entries of the Bourbaki-numbered Cartan matrix.
* `TauCeti.DynkinType.card_support_simplyConnectedBase`: the pinned base has `t.rank` elements.
* `TauCeti.DynkinType.toLinearMap_simplyConnectedRootDatum`: the pinned pairing is the dot
  product, uniformly in the type.
* `TauCeti.DynkinType.coroot'_simpleIndex_apply`: evaluation at a simple coroot extracts the
  corresponding fundamental-weight coordinate.
* `TauCeti.DynkinType.simpleIndex_B`, `simpleIndex_F4` and `simpleIndex_G2`: the simple-root
  index of the dispatcher is the family module's own simple-root index, for the three families
  carrying a special isogeny.

## References

The family data and numbering follow N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plates I--IX, and J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*,
Chapter 11. This assembles the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md` for its consumer,
`CFSGStatement` milestone L0.
-/

public section

namespace TauCeti.DynkinType

noncomputable section

/-! ## The uniform pinned datum -/

/-! ## Branch equations -/

/-! ## The uniform Bourbaki pinning -/

/-- The index of the `i`-th Bourbaki simple root in the pinned root enumeration. -/
def simpleIndex (t : DynkinType) (ht : t.Valid) (i : Fin t.rank) : Fin t.numRoots :=
  Fin.castLE (rank_le_numRoots ht) i

/-- The root enumeration index of a simple root has the same zero-based value as its node. -/
@[simp] theorem simpleIndex_val (t : DynkinType) (ht : t.Valid) (i : Fin t.rank) :
    (t.simpleIndex ht i : ℕ) = i := (rfl)

/-! Each family module enumerates its own roots and names its own simple-root index. The
equations below identify the dispatcher with those names, so a statement proved for one family
about its own index transfers to the uniform one. They are stated by `Fin.ext` against
`simpleIndex_val` rather than by unfolding either side. -/

/-- The simple-root index of the dispatcher at type `B n` is type `B`'s own simple-root index. -/
@[simp] theorem simpleIndex_B (n : ℕ) (ht : (B n).Valid) (i : Fin n) :
    (B n).simpleIndex ht i = typeBSimpleIndex n i := by
  apply Fin.ext
  rw [typeBSimpleIndex_val]
  exact simpleIndex_val (B n) ht i

/-- The simple-root index of the dispatcher at type `F₄` is type `F₄`'s own simple-root index. -/
@[simp] theorem simpleIndex_F4 (ht : F4.Valid) (i : Fin 4) :
    F4.simpleIndex ht i = Fin.castAdd 44 i := Fin.ext rfl

/-- The simple-root index of the dispatcher at type `G₂` is type `G₂`'s own simple-root index. -/
@[simp] theorem simpleIndex_G2 (ht : G2.Valid) (i : Fin 2) :
    G2.simpleIndex ht i = Fin.castAdd 10 i := Fin.ext rfl

/-! ## Uniform acceptance theorems -/

end

end TauCeti.DynkinType
