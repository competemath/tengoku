/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku
import Tengoku.Tnlean.TNLean.PEPS.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Edge gauge extraction from insertion algebra isomorphisms

This file records the finite-dimensional algebra step in the injective PEPS
Fundamental Theorem. Once the edge-blocked three-site argument gives an algebra
isomorphism between the full matrix algebras of insertions on a chosen edge,
Skolem--Noether turns that isomorphism into conjugation by an invertible edge
matrix.
-/

open scoped Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

end PEPS
end TNLean
