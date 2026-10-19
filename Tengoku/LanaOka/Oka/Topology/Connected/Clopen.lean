/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Topology.Connected.Clopen
import Tengoku.Seed.Topology.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The connected component of a point of a disjoint union of connected spaces

`Sigma.mk i` embeds the `i`-th member of a disjoint union as a clopen subset, and a clopen
connected subset containing a point **is** that point's connected component. So if every member is
connected the components of `Σ i, β i` are exactly the members, and
`connectedComponent_sigmaMk` is that statement.

**Mathlib gets as far as the members and stops one step short of the components.**
`Mathlib/Topology/Connected/Clopen.lean` — the file this one is staged for — has
`Sigma.isConnected_iff`, *a subset of a disjoint union is connected exactly when it is the image
of a connected subset of one member*, and `Mathlib/Topology/Constructions.lean` has
`isOpen_range_sigmaMk` and `isClosed_range_sigmaMk`. **What neither says is what the connected
component of a point is**, and at `v4.32.0` no statement in Mathlib mentions `connectedComponent`
together with a disjoint union at all:
`grep -rn 'connectedComponent' Mathlib/ | grep -iE 'sigma|Sum\.|coprod'` returns **nothing**,
against **56** occurrences of `connectedComponent` in the destination file itself.

**There is no complex-analytic content here**, so this file is in the `Oka/Topology/` mirror of the
Mathlib directory tree; `README.md`'s mirror-tree section is what asks for that.
**Upstreaming to `Mathlib/Topology/Connected/Clopen.lean` costs that file nothing**:
its only import beyond the target is `Mathlib.Topology.Constructions`, which is already in that
target's closure of **614** Mathlib modules, measured with `python3 scripts/import_cost.py
--target Mathlib.Topology.Connected.Clopen Mathlib.Topology.Constructions`.
That is not an accident of this proof — the destination file already consumes `isOpenMap_sigmaMk`
and `sigma_mk_injective` from that module, in `Sigma.isConnected_iff`'s own proof.

## Main results

- `connectedComponent_sigmaMk`: **the connected component of a point of a disjoint union of
  connected spaces is the member it lies in**, as the range of `Sigma.mk` at that point's index.

## What is not here

* **No converse and no hypothesis-free version.** `[∀ i, ConnectedSpace (β i)]` is what makes the
  member equal to the component rather than merely contain it; without it the component of
  `⟨i, y⟩` is the image of the component of `y`, which is a different statement and is not
  needed by the consumer this was written for.
* **Nothing about `ConnectedComponents`**, the quotient type. The statement below is about the
  set, and a reader who wants the quotient identified with the index type would have to say what
  happens over an empty member — a member with empty carrier is excluded here by
  `ConnectedSpace`, which is why the set-level statement needs no such case.
  **This bullet is about this file and was never a claim about the tree**, and since 2026-09-20 it
  would be false as one: `Oka/Topology/Homeomorph/Lemmas.lean`, which reads the statement below,
  concludes `Finite (ConnectedComponents X)` for a space homeomorphic to a disjoint union of
  finitely many connected spaces. **It is still not an identification of the quotient with the
  index type**, for the reason this bullet gives, and that file's own `## What is not here` says
  so. The split is by destination: nothing there goes to
  `Mathlib/Topology/Connected/Clopen.lean`, because every statement in it names a homeomorphism.
-/

open Set

/-- **The connected component of a point of a disjoint union of connected spaces is the member it
lies in.**

The two inclusions are the two things a clopen connected set is good for. `Set.range (Sigma.mk i)`
is clopen — `isClosed_range_sigmaMk` and `isOpen_range_sigmaMk` — and contains the point, so it
contains no more than the component by `IsClopen.connectedComponent_subset`; and it is
preconnected, being the image of the connected `β i` under `Sigma.mk i`, so it is contained in the
component by `IsPreconnected.subset_connectedComponent`.

**`[∀ i, ConnectedSpace (β i)]` is used in the second inclusion only**, and only through
`isPreconnected_univ`: the first holds for any family whatever. -/
theorem connectedComponent_sigmaMk {ι : Type*} {β : ι → Type*} [∀ i, TopologicalSpace (β i)]
    [∀ i, ConnectedSpace (β i)] (i : ι) (y : β i) :
    connectedComponent (⟨i, y⟩ : Σ i, β i) = Set.range (Sigma.mk i) := by
  refine subset_antisymm
    (IsClopen.connectedComponent_subset ⟨isClosed_range_sigmaMk, isOpen_range_sigmaMk⟩ ⟨y, rfl⟩)
    (IsPreconnected.subset_connectedComponent ?_ ⟨y, rfl⟩)
  simpa [Set.image_univ] using
    (isPreconnected_univ (α := β i)).image _ continuous_sigmaMk.continuousOn
