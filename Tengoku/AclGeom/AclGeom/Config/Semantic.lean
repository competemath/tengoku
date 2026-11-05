/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Geometry.Equivalence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The semantic relations Q, Q′, and J

The semantic configurations of blueprint Def semantic-configs: for points of
the geometry `𝒢(K/k)`, writing `[x]` for the principal closure
`ClosedIF.point k x`,

* `QSem X Y Z W`: some independent pair `x, y` has
  `(X, Y, Z, W) = ([x], [y], [x+y], [x/y])`;
* `Q'Sem X Y Z W`: likewise with `[xy]` in place of `[x/y]`;
* `JSem X`: the five-tuple `X` is `([x], [x+a], [xa], [x+xa], [a])` for some
  independent `x, a` (the image of the `j`-map).

The normalization identities (`[cx] = [x]`, `[x+c] = [x]`, invariance under
nonzero powers, inverses, and negation) are recorded at the level of
principal closures; the blueprint notes they need no extra theory beyond
the singleton-closure calculus of `AclGeom.Closure.Basic`.

By the blueprint's architecture rule, this file imports only closure/point
foundations — no geometric predicates.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4).
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

namespace ClosedIF

/-- Normalization: translating by a constant of the base field does not
move a principal closure (blueprint §semantic relations).
@isnad1 id=eq.0h4v.s7.34cbd2fffc76 from=translated src=- shape=3a6fc349 vocab=8fc70fcf
-/
theorem point_add_algebraMap (x : K) (c : k) :
    point k (x + algebraMap k K c) = point k x :=
  Subtype.ext (racl_add_algebraMap x c)

/-- Normalization: inversion does not move a principal closure.
@isnad1 id=eq.0h3v.s6.5f4e637de6ba from=translated src=- shape=179a48ee vocab=8b3ba376
-/
theorem point_inv (x : K) : point k x⁻¹ = point k x :=
  Subtype.ext (racl_inv x)

/-- A ratio and its reciprocal generate the same principal closure.
@isnad1 id=eq.0h4v.s6.e2e5c12d225c from=translated src=- shape=cbff7a1a vocab=daa87c40
-/
theorem point_div_symm (x y : K) : point k (x / y) = point k (y / x) := by
  rw [← point_inv (x / y), inv_div]

end ClosedIF

open ClosedIF

/-- The semantic relation `Q` (blueprint Def semantic-configs): the four
points are `([x], [y], [x+y], [x/y])` for some pair `x, y` algebraically
independent over `k`.-/
def QSem (X Y Z W : Point k K) : Prop :=
  ∃ x y : K, AlgebraicIndependent k ![x, y] ∧
    X.1 = point k x ∧ Y.1 = point k y ∧
    Z.1 = point k (x + y) ∧ W.1 = point k (x / y)

/-- **The ratio point of a semantic `Q`-quadruple differs from its second point**: in
`([x], [y], [x+y], [x/y])` with `x, y` independent, `[x/y] = [y]` would put `x = (x/y) y` in
the closure of `y`.
@isnad1 id=ne.1h6v.s6.bb2390f4f218 from=translated src=- shape=26bb322d vocab=f8e8e75b
-/
theorem QSem.ratio_ne {X Y Z W : Point k K} (h : QSem X Y Z W) : W ≠ Y := by
  obtain ⟨x, y, hind, -, hY, -, hW⟩ := h
  intro hWY
  have hpt : ClosedIF.point k (x / y) = ClosedIF.point k y :=
    hW.symm.trans ((congrArg Subtype.val hWY).trans hY)
  have hxy : x / y ∈ racl k ({y} : Set K) :=
    ClosedIF.mem_point.1 (ClosedIF.point_eq_point_iff.1 hpt).1
  have hy : y ∈ racl k ({y} : Set K) := subset_racl k _ rfl
  have hy0 : y ≠ 0 := hind.ne_zero 1
  have hx := MulMemClass.mul_mem hxy hy
  rw [div_mul_cancel₀ x hy0] at hx
  exact AlgebraicIndependent.notMem_racl_pair' hind hx

/-- The semantic relation `Q′` (blueprint Def semantic-configs): the four
points are `([x], [y], [x+y], [xy])` for some pair `x, y` algebraically
independent over `k`.-/
def Q'Sem (X Y Z W : Point k K) : Prop :=
  ∃ x y : K, AlgebraicIndependent k ![x, y] ∧
    X.1 = point k x ∧ Y.1 = point k y ∧
    Z.1 = point k (x + y) ∧ W.1 = point k (x * y)

/-- The semantic relation `J` (blueprint Def semantic-configs): the
five-tuple is the value `j(x, a) = ([x], [x+a], [xa], [x+xa], [a])` of the
`j`-map at some pair `x, a` algebraically independent over `k`.-/
def JSem (X : Fin 5 → Point k K) : Prop :=
  ∃ x a : K, AlgebraicIndependent k ![x, a] ∧
    (X 0).1 = point k x ∧ (X 1).1 = point k (x + a) ∧
    (X 2).1 = point k (x * a) ∧ (X 3).1 = point k (x + x * a) ∧
    (X 4).1 = point k a

end

end AclGeom
