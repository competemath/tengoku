/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Forcing.Forcing.Model.GenericOver
import Tengoku.Forcing.Forcing.Order.Requirement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The requirement–visibility bridge

The passage from visibility to meeting is generic, not Cohen-specific: a requirement whose
support is visible is a visible dense-open test (`Requirement.mem_visibleDenseOpen`), so a
filter generic over the context meets it (`GenericOver.meets_requirement`). Every forcing
notion reuses this bridge; carrier-specific files keep only thin named specializations (see
`Forcing/Cohen/Visibility.lean`).

The layer boundary is deliberate: the `Requirement` supplies dense-openness, the context
supplies visibility, and `GenericOver` supplies meeting. No layer duplicates another's job.

## Main results

* `Forcing.Requirement.mem_visibleDenseOpen`: a visible requirement is a visible dense-open
  test.
* `Forcing.GenericOver.meets_requirement`: a generic filter meets every visible requirement.
-/

namespace Forcing

open Order

variable {P : Type*} [Preorder P] {M : VisibilityContext P} {G : PFilter P}

/-- A requirement whose support is visible is a visible dense-open test: visibility is the
hypothesis, dense-openness comes with being a requirement.
@isnad1 id=mem.1h3v.s5.68bb7fecc332 from=translated src=- shape=d8489a68 vocab=f932638f
-/
theorem Requirement.mem_visibleDenseOpen (R : Requirement P) (hR : M.Visible R.support) :
    R.support ∈ M.visibleDenseOpen :=
  ⟨hR, R.isDenseOpen_support⟩

/-- **A generic filter meets every visible requirement** — the generic form of the
visibility-to-meeting passage.
@isnad1 id=meets.2h4v.s5.359fc50ea217 from=translated src=- shape=0e8f10f5 vocab=94dbcf24
-/
theorem GenericOver.meets_requirement {R : Requirement P} (hG : GenericOver M G)
    (hR : M.Visible R.support) :
    Meets G R.support :=
  hG _ (R.mem_visibleDenseOpen hR)

end Forcing
