/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.Reduced
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NonSimplyLaced

/-!
# Reducedness of the pinned root data

The pinned simply connected root data of types `A`, `D`, `E₆`, `E₇`, and `E₈` are reduced. Their
character and cocharacter lattices use different preferred bases, so reducedness is not obtained
by identifying each root with its coroot. Instead, their coordinate constructions all exhibit a
symmetric root--coroot pairing. `RootPairing.isReduced_of_pairing_comm` then rules out nontrivial
multiples among their roots.

These instances supply the reducedness hypothesis needed to apply Mathlib's Geck construction to
the rational scalar extensions of the pinned data. The non-simply-laced cases are supplied by
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NonSimplyLaced`; the final theorem here
joins the two cases uniformly.

## Main results

* Reducedness results for `DynkinType.typeASimplyConnectedRootDatum`,
  `typeDSimplyConnectedRootDatum`, `e6SimplyConnectedRootDatum`,
  `e7SimplyConnectedRootDatum`, and `e8SimplyConnectedRootDatum`.
* `DynkinType.isReduced_simplyConnectedRootDatum_of_isSimplyLaced`: the uniform reducedness
  theorem for every valid simply-laced Dynkin type.
* `DynkinType.isReduced_simplyConnectedRootDatum`: the uniform reducedness theorem for every
  valid Dynkin type.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I, IV--VII.
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*.
-/

public section

namespace TauCeti.DynkinType

/-- The pinned simply connected root datum of type `E₆` is reduced. -/
instance instIsReducedE6SimplyConnectedRootDatum : e6SimplyConnectedRootDatum.IsReduced :=
  RootPairing.isReduced_of_pairing_comm _ fun i j => by
    simpa only [e6SimplyConnectedRootDatum_pairing] using e6Root_dotProduct_e6Coroot_comm i j

/-- The pinned simply connected root datum of type `E₇` is reduced. -/
instance instIsReducedE7SimplyConnectedRootDatum : e7SimplyConnectedRootDatum.IsReduced :=
  RootPairing.isReduced_of_pairing_comm _ fun i j => by
    simpa only [e7SimplyConnectedRootDatum_pairing] using e7Root_dotProduct_e7Coroot_comm i j

end TauCeti.DynkinType
