/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Transfer.FiniteUnion
import Tengoku.AclGeom.AclGeom.Transfer.Intersections
import Tengoku.AclGeom.AclGeom.Transfer.Transcendence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The specialized one-quantifier transfer

Gismatullin's transfer (blueprint Thm one-quantifier-transfer, main case):
a Boolean combination of closure-membership conditions with finite
parameters from `K₁` — in disjunctive normal form, a conjunction of
memberships `z ∈ racl k (Aᵢ)` and non-memberships `z ∉ racl k (Bⱼ)` —
has a witness in `K₁` iff it has one in `K₂ ≥ K₁`.

The proof is Boolean assembly of the three transfer bricks: the
intersection of the `racl k (Aᵢ)` is a single finitely generated closure
`racl k C` (iterating `exists_finite_inter_generator`), each excluded
closure traces on it as `racl k (Cⱼ)`, a witness exists in `K` exactly
when the subfield `racl k C ⊓ K` is not covered by the finitely many
subfields `racl k (Cⱼ) ⊓ K` (relative no-field-cover), and each
covering equality transfers between `K₁` and `K₂` by the
strict-inclusion transfer.

As long as at least one membership conjunct is present, *no
transcendence-degree hypothesis is needed* — blueprint hypothesis (9.4)
enters only the case with no `Aᵢ`. `one_quantifier_transfer_full` covers both its
equal-finite-degree and both-infinite-degree branches.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (M5, checklist T3): both the main case and the two
branches of the no-membership case in blueprint hypothesis (9.4) are proved.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

end

end AclGeom
