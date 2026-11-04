/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.FiniteIntersection
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Degrees of finite scheme-theoretic intersections

Over a field, the residue-degree-weighted degree of a finite intersection cycle is its
intersection number.  On a compact ambient scheme this number is the finite sum of the local
intersection lengths multiplied by the degrees of the residue fields.  It is nonnegative and is
unchanged when the two closed subschemes are exchanged.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Chow.FiniteClosedIntersectionData

variable {X : Scheme.{u}} {p : ℕ} (d : FiniteClosedIntersectionData X p)
  (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]

noncomputable local instance : Fintype d.intersection := Fintype.ofFinite d.intersection

end AlgebraicGeometry.Chow.FiniteClosedIntersectionData
