/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Tengoku.Seed.Algebra.Group.Defs
import Tengoku.Seed.Data.Set.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Subgroups of a Semigroup: Definitions

This file defines what it means for a subset of a semigroup to be a subgroup
with a given identity. Since a semigroup has no distinguished identity, the
identity is part of the data of the predicate. The theory — the group
structure on such a subset and Green's theorem, that the H-class of an
idempotent is the greatest subgroup at that idempotent — is developed in
`Semigroup.GreensTheorem.Subgroups.Basic`.

## Main definitions

* `IsSubgroupWith`: `IsSubgroupWith e G` means the set `G` is a subgroup of the ambient
  semigroup with identity `e`.

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995]

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/
namespace Tengoku.Semigroup end Tengoku.Semigroup open Tengoku.Semigroup
variable {S : Type*} [Semigroup S]

/-- `IsSubgroupWith e G` means that the set `G` is a subgroup of the semigroup `S`
with identity `e`: `G` contains `e`, is closed under multiplication, `e` is a
two-sided identity on `G`, and every element of `G` has a two-sided inverse in `G`
relative to `e`.

The primed fields carry the raw bounded-quantifier clauses; use the unprimed
accessors in `Semigroup.GreensTheorem.Subgroups.Basic` (`IsSubgroupWith.mul_mem`,
`IsSubgroupWith.identity_mul`, `IsSubgroupWith.mul_identity`,
`IsSubgroupWith.exists_inv`) in proofs.-/
structure _root_.Tengoku.Semigroup.IsSubgroupWith (e : S) (G : Set S) : Prop where
  /-- The identity belongs to the subgroup.-/
  identity_mem : e ∈ G
  /-- The subgroup is closed under multiplication.-/
  mul_mem' : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G
  /-- The identity is a two-sided identity on the subgroup.-/
  identity_laws : ∀ x ∈ G, e * x = x ∧ x * e = x
  /-- Every element has a two-sided inverse in the subgroup relative to `e`.-/
  exists_inv' : ∀ x ∈ G, ∃ y ∈ G, x * y = e ∧ y * x = e
-- Tengoku: root names of this library moved to Tengoku.Semigroup so they do not collide with other libraries (generated)
