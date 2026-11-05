/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Curves.Differentials

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The duality theorem and the canonical class

For a nonzero Weil differential with maximal level `W`, the
multiplication pairing `L(W − D) → Ω(D)` is bijective: injectivity is
the cancellation of multiplication, surjectivity combines the
proportionality theorem with the shift of the maximal level. Hence
`i(D) = ℓ(W − D)` — the duality theorem (Stichtenoth 1.5.15) — and
evaluating at `D = 0` and `D = W` pins the canonical class:
`ℓ(W) = g` and `deg W = 2g − 2`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P5).
-/

namespace AclGeom

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

end

end AclGeom
