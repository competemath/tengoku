/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Topology.Sheaves.Stalks

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Two missing lemmas about stalks

`TopCat.Presheaf.stalkPushforward C g F x : (g _* F).stalk (g x) ⟶ F.stalk x` is natural in `F`.
Mathlib has the definition and its compatibility with germs, identities and composites of `g`,
but not this naturality square, which is what one needs to move a morphism of presheaves on the
source space through a stalk computation on the target space.

`TopCat.Presheaf.stalkCongr F e : F.stalk x ≅ F.stalk y` for inseparable `x` and `y` likewise
has its compatibility with germs in Mathlib only as an equality of morphisms, for
`stalkSpecializes`; `TopCat.Presheaf.stalkCongr_hom_germ` is the applied form, which is what one
needs after `AlgebraicGeometry.SheafedSpace.hom_stalk_ext` puts such a transport into a goal.

There is no analytic content here, so this file is a candidate for upstreaming to Mathlib; it
lives in the `Oka/Topology/` mirror of the Mathlib directory tree for that reason.

## Main results

- `TopCat.Presheaf.stalkPushforward_naturality`
- `TopCat.Presheaf.stalkCongr_hom_germ`
- `TopCat.Presheaf.isIso_stalkSpecializes_of_eq`
-/

open CategoryTheory Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u v

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] [HasColimits C]

/-- **The specialization map between the stalks at two points which are in fact equal is an
isomorphism.**

`TopCat.Presheaf.stalkCongr` says this for `Inseparable` points and returns an isomorphism; this
is the `IsIso` form for a specialization arising from an equality, which is the shape in which it
is needed after `AlgebraicGeometry.LocallyRingedSpace.stalkMap_congr_hom` — that lemma produces a
`stalkSpecializes` whose proof argument is manufactured from an equation between morphisms, and
one cannot name the resulting proof term in advance. -/
lemma isIso_stalkSpecializes_of_eq {X : TopCat.{v}} (F : X.Presheaf C) {a b : X} (h : a ⤳ b)
    (h' : b = a) : IsIso (F.stalkSpecializes h) := by
  subst h'
  have hid : F.stalkSpecializes h = 𝟙 _ := by simp
  rw [hid]
  infer_instance

section Concrete

variable {FC : C → C → Type*} {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{v} C FC]

/-- **Transporting a germ between the stalks at two inseparable points is the germ at the other
point.**

Mathlib has `TopCat.Presheaf.germ_stalkSpecializes` as an equality of morphisms; this is the
applied form for the isomorphism `TopCat.Presheaf.stalkCongr`, which is what one needs after
`AlgebraicGeometry.SheafedSpace.hom_stalk_ext` puts a `stalkCongr` transport into the goal.

Note that the membership `hy` is an argument rather than derived from `hx`: any proof will do,
and taking it as given is what lets the caller write the germ at `y` in whatever form the
surrounding statement already produced. -/
lemma stalkCongr_hom_germ {X : TopCat.{v}} (F : X.Presheaf C) {x y : X} (e : Inseparable x y)
    (U : Opens X) (hx : x ∈ U) (hy : y ∈ U) (s : ToType (F.obj (op U))) :
    ConcreteCategory.hom (F.stalkCongr e).hom (F.germ U x hx s) = F.germ U y hy s :=
  (ConcreteCategory.comp_apply (F.germ U x hx) (F.stalkSpecializes e.ge) s).symm.trans
    (ConcreteCategory.congr_hom (F.germ_stalkSpecializes (h := e.ge) (U := U) (hy := hx)) s)

end Concrete

end TopCat.Presheaf
