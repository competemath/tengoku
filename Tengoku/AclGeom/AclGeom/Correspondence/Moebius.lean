/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Closure.Basic
import Tengoku.AclGeom.AclGeom.Correspondence.BaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bidegree-(1,1) correspondences are Möbius graphs

The elementary classification at the heart of the rational-curve route to
the affine-action lemma (design issue on the project tracker): a bivariate
relation of degree at most one in each variable, vanishing at a pair with
transcendental first coordinate, expresses the second coordinate as a
Möbius function of the first. This replaces the `PGL₂`-analysis of
blueprint Lemma 8.4 at the level of correspondences on a rational curve —
no projective models or genus theory are involved.

* `eq_bilinear_of_degreeOf_le_one`: the four-coefficient normal form;
* `exists_moebius_of_bidegree_le_one`: the Möbius formula, with a nonzero
  denominator.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4a, issue #12 pipeline step 2 groundwork).
-/

namespace AclGeom

open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]

section Bilinear

/-- Reconstruction of a `Fin 2`-finsupp from its two values.-/
theorem finsupp_fin_two_eq (m : Fin 2 →₀ ℕ) :
    m = Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) := by
  ext i
  fin_cases i <;> simp

end Bilinear

section Moebius

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

end Moebius

section DegreeOne

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

end DegreeOne

end

end AclGeom
