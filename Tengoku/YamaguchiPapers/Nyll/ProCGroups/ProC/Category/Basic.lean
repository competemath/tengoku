/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Topology.Algebra.Category.ProfiniteGrp.Limits
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.Subgroups.Closed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The category of pro-\(C\) groups

`ProCGrp C` is the full subcategory of Mathlib's `ProfiniteGrp` cut out by
`HasOpenNormalBasisInClass C`. Thus the ambient object supplies the group, topological-group,
compact, Hausdorff, and totally disconnected structures; the class-restricted open-normal basis is
the only additional property.
-/

open CategoryTheory Topology

universe u

/-- The canonical object property underlying the category of pro-`C` groups.-/
def ProCGroups.proCObjectProperty (C : ProCGroups.FiniteGroupClass.{u}) :
    ObjectProperty ProfiniteGrp.{u} :=
  fun G => ProCGroups.ProC.HasOpenNormalBasisInClass C G

/-- Pro-\(C\) groups: profinite groups with an open-normal quotient basis in \(C\).-/
abbrev ProCGrp (C : ProCGroups.FiniteGroupClass.{u}) :=
  (ProCGroups.proCObjectProperty C).FullSubcategory

namespace ProCGrp

variable {C : ProCGroups.FiniteGroupClass.{u}}

/-- A canonical pro-`C` object has exactly the carrier of its ambient `ProfiniteGrp` object.

This is the only carrier coercion installed here.  All algebraic and topological instances then
come definitionally from `G.obj`; redeclaring them on `ProCGrp` would create competing instance
paths with the ambient full-subcategory concrete structure.-/
instance : CoeSort (ProCGrp C) (Type u) where
  coe G := G.obj

/-- Construct a bundled pro-\(C\) group from a `ProfiniteGrp` and its open-normal basis property.-/
def of (C : ProCGroups.FiniteGroupClass.{u})
    (G : ProfiniteGrp.{u})
    (hBasis : ProCGroups.ProC.HasOpenNormalBasisInClass C G) : ProCGrp C :=
  ⟨G, hBasis⟩

/-- The continuous homomorphism carried by a full-subcategory morphism.-/
abbrev continuousHom {A B : ProCGrp C} (f : A ⟶ B) : A →ₜ* B :=
  ConcreteCategory.hom (C := ProCGrp C) f

/-- Morphisms in ProCGrp are equal when their underlying continuous homomorphisms are equal.
@isnad1 id=eq.1h5v.s7.cf74188712ea from=translated src=- shape=8dc2ed1d vocab=4d37a61e
-/
@[ext] theorem hom_ext {A B : ProCGrp C} {f g : A ⟶ B}
    (hf : continuousHom f = continuousHom g) :
    f = g :=
  ConcreteCategory.ext hf

/-- On profinite groups the all-finite object property imposes no additional condition.
@isnad1 id=procobje.0h1v.s2.d51af54dd394 from=translated src=- shape=f5394aa3 vocab=351da25c
-/
@[simp] theorem allFinite_property (G : ProfiniteGrp.{u}) :
    ProCGroups.proCObjectProperty ProCGroups.FiniteGroupClass.allFinite G := by
  intro W hW h1W
  rcases ProCGroups.ProC.exists_openNormalSubgroup_sub_open_nhds_of_one
      (G := G) hW h1W with ⟨U, hUW⟩
  exact ⟨U, hUW, ProCGroups.openNormalSubgroup_finiteQuotient (G := G) U⟩

end ProCGrp
