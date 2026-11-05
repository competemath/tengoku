/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Config.Psi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The multiplication diagram and the geometric Q′

The projective multiplication diagram, stated without a picture
(blueprint §multiplication diagram):

* `MulDiagram X Y V E A₀ B₀ C₀ D₀`: eight pairwise distinct points, the
  seven rank-two lines
  `{X, A₀, B₀}`, `{A₀, Y, C₀}`, `{A₀, E, D₀}`, `{B₀, Y, D₀}`,
  `{X, C₀, D₀}`, `{B₀, C₀, V}`, `{X, Y, E, V}` (the last a common
  rank-two line through four points), and the nondegeneracy clause
  `rk(X ∨ Y ∨ A₀) = 3`;
* `Q'Geom X Y S E`: the geometric relation `Q′` — a `Q`-witness on
  `(X, Y, S, V)` together with a multiplication diagram converting the
  ratio point `V` into the product point `E`.

The coordinate check is proved in `Config.MulDiagramCheck`, and the full coordinate
converse over ACF base and ambient fields is proved in `Config.MultiplicationConverse`,
without a rank bound. `Transfer.MulDiagramProduct` strengthens its product clause to
arbitrary fields for actual bottom representatives, without descending the auxiliary table.
`Config.Completeness` supplies rank-five ACF `Q′` completeness, and
`Transfer.ProjectedConfigurations` gives its corrected projected form over perfect ambient
fields at rank five. The original raw arbitrary-field consequence remains refuted.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the definitions and guard lemmas in this module are complete (M4, G4).
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- The projective multiplication diagram on eight points (blueprint
§multiplication diagram): seven rank-two lines and the nondegeneracy
clauses. Semantically, with `x, y, a` independent, the points are
`x, y, x/y, xy, a, ax, ay, axy`.-/
structure MulDiagram (X Y V E A₀ B₀ C₀ D₀ : Point k K) : Prop where
  /-- The eight points are pairwise distinct; in particular any two named
  points on a displayed line are distinct, so every line is genuine.-/
  distinct : Function.Injective ![X, Y, V, E, A₀, B₀, C₀, D₀]
  /-- The line `{X, A₀, B₀}` (semantically `ax = a · x`).-/
  line_XAB : RankEq 2 (X.1 ⊔ (A₀.1 ⊔ B₀.1))
  /-- The line `{A₀, Y, C₀}` (semantically `ay = a · y`).-/
  line_AYC : RankEq 2 (A₀.1 ⊔ (Y.1 ⊔ C₀.1))
  /-- The line `{A₀, E, D₀}` (semantically `axy = a · xy`).-/
  line_AED : RankEq 2 (A₀.1 ⊔ (E.1 ⊔ D₀.1))
  /-- The line `{B₀, Y, D₀}` (semantically `axy = (ax) · y`).-/
  line_BYD : RankEq 2 (B₀.1 ⊔ (Y.1 ⊔ D₀.1))
  /-- The line `{X, C₀, D₀}` (semantically `axy = x · (ay)`).-/
  line_XCD : RankEq 2 (X.1 ⊔ (C₀.1 ⊔ D₀.1))
  /-- The line `{B₀, C₀, V}` (semantically `x/y = (ax)/(ay)`).-/
  line_BCV : RankEq 2 (B₀.1 ⊔ (C₀.1 ⊔ V.1))
  /-- The common line through `X, Y, E, V` (semantically the
  multiplicative relations among `x, y, xy, x/y`).-/
  line_XYEV : RankEq 2 (X.1 ⊔ (Y.1 ⊔ (E.1 ⊔ V.1)))
  /-- Nondegeneracy: `X, Y, A₀` are in general position.-/
  rank_XYA : RankEq 3 (X.1 ⊔ (Y.1 ⊔ A₀.1))

/-- The geometric relation `Q′` (blueprint §multiplication diagram):
a `Q`-witness produces the ratio point `V` from `(X, Y, S)`, and a
multiplication diagram converts it into the product point `E`.-/
def Q'Geom (X Y S E : Point k K) : Prop :=
  ∃ V A₀ B₀ C₀ D₀ : Point k K,
    QGeom X Y S V ∧ MulDiagram X Y V E A₀ B₀ C₀ D₀

/-- The geometric relation `J` — the Evans–Hrushovski identity reproduced
by Gismatullin (blueprint §geometric definition of J):
`J(X, P, Q, R, A)` is one `Q`-instance and two `Q′`-instances. The third
conjunct exploits `[a+1] = [a]` and `x(a+1) = x + xa`, so the same pair
`(P, R)` of sum points appears against both product coordinates.-/
def JGeom (X P Q R A : Point k K) : Prop :=
  QGeom X Q R A ∧ Q'Geom X A P Q ∧ Q'Geom X A P R

end

end AclGeom
