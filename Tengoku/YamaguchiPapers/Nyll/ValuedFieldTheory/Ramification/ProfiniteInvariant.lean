/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.FieldTheory.Galois.Profinite
import Tengoku.Seed.RingTheory.Invariant.Profinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Profinite invariant rings: normality on prime residue fields

The finite invariant-ring API proves that a prime residue extension is
normal. The residue-action exact sequence also needs the corresponding profinite
statement.  The proof is the same finite-orbit argument as in this construction: an
element of the discrete ring is fixed by an open normal subgroup, so its
orbit polynomial is computed in a finite quotient.
-/

namespace RamificationTheory

noncomputable section

open scoped Pointwise

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B]
variable [ContinuousSMul G B] [Algebra.IsInvariant A B G]

namespace Ideal.Quotient

attribute [local instance] Ideal.Quotient.field

include G

end Ideal.Quotient

end

end RamificationTheory
