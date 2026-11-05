/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import Tengoku.AclGeom.AclGeom.Transfer.Transcendence
import Tengoku.Seed.Data.Set.Finite.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fresh sequences over infinite transcendence degree

* `exists_fresh_sequence_of_aleph0_le_trdeg`: if `ℵ₀ ≤ trdeg_k K` and `S` is finite, there is a
  sequence `t` such that each `t n` lies outside `acl(S ∪ {t m | m < n})`.  No algebraic
  closedness is needed.

The sequences supply the families of fresh inputs of the affine-grid producers: in `K` itself in
`AclGeom.Config.AffineGridInfinite`, and in an algebraically closed extension with at least
countable transcendence degree over `k` in `AclGeom.Config.AffineGridNormalization`.

**Status:** proved (#27, P5); moved here unchanged in P6.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

end AclGeom
