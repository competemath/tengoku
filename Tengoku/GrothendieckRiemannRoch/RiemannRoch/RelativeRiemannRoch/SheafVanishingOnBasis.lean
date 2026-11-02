/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.Topology.Sheaves.Stalks
import Tengoku.Seed.Topology.Sheaves.Abelian
import Tengoku.Seed.Algebra.Category.Grp.Zero
import Tengoku.Seed.Topology.Sheaves.Sheafify

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vanishing on a basis suffices

`RelativeRiemannRoch/AffineLocalHigherDirectImageSheafVanishing.lean` records why relative Serre
vanishing cannot use a naive "vanishes on every open" criterion: for `π : ℙⁿ_R ⟶ Spec R` the
absolute vanishing theorem gives `Hⁱ(π ⁻¹ᵁ V, O(d)) = 0` only when `π ⁻¹ᵁ V` is itself a projective
space over a ring, i.e. only for **basic** opens `V = D(f)`.  The general fix is to weaken the
hypothesis to a basis, which is what this file provides, for sheaves of abelian groups on any
topological space:

* `TopCat.Presheaf.subsingleton_stalk_of_isBasis`: a presheaf vanishing on a basis has zero stalks.
  Every germ is represented on *some* neighbourhood (`exists_germ_eq`); that neighbourhood may be
  shrunk to a basic one (`Opens.IsBasis.exists_subset_of_mem_open`), where the section is zero, so
  the germ is zero (`germ_res_apply`).
* `TopCat.Sheaf.isZero_of_isBasis`: consequently a *sheaf* vanishing on a basis is a zero object,
  via `TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero` and
  `AddCommGrpCat.isZero_iff_subsingleton`.
* `TopCat.Presheaf.isZero_sheafify_of_isBasis`: and a *presheaf* vanishing on a basis has zero
  sheafification.  This is the form the higher-direct-image argument needs, and it is the one that
  actually closes the gap: `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` says the unit
  induces an isomorphism on stalks, so the sheafification inherits the presheaf's vanishing stalks.

Neither statement is in Mathlib.  The first is the load-bearing one: it applies to a presheaf, so it
is exactly what a *sheafification* argument needs, the sheafification having the same stalks as the
presheaf it comes from.

Remaining link for the intended consumer: `Rⁱf_*` is
`SchemeRelativeRiemannRoch.affineLocalHigherDirectImageSheafification`, built with
`PresheafOfModules.sheafification`, and
`affineLocalHigherDirectImageSheafification_toSheaf` identifies its underlying `AddCommGrpCat`-valued
sheaf with `presheafToSheaf` of the additive presheaf **definitionally**.  So
`isZero_sheafify_of_isBasis` applies to that underlying sheaf directly; what is still needed is only
that `Scheme.Modules.toSheafAb` *reflects* `IsZero` (the preserving direction is already used, at
`AffineLocalHigherDirectImageBaseChangeVanishing.lean:85`).  The topological content is done.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TopCat.Presheaf

/-- A presheaf of abelian groups vanishing on a basis has zero stalks: every germ is represented on
some neighbourhood, which may be shrunk to a basic one, where the section is zero.-/
theorem subsingleton_stalk_of_isBasis {X : TopCat.{u}} (P : X.Presheaf AddCommGrpCat.{u})
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hzero : ∀ U ∈ B, Subsingleton (P.obj (op U))) (x : X) :
    Subsingleton (P.stalk x) := by
  have key : ∀ u : P.stalk x, u = 0 := by
    intro u
    obtain ⟨U, hxU, sU, rfl⟩ := P.exists_germ_eq u
    obtain ⟨_, ⟨W, hWB, rfl⟩, hxW, hWU⟩ := hB.exists_subset_of_mem_open hxU U.2
    have hres : P.map (homOfLE hWU).op sU = 0 := @Subsingleton.elim _ (hzero W hWB) _ 0
    rw [← P.germ_res_apply (homOfLE hWU) x hxW sU]
    have h0 := congrArg (fun z => (ConcreteCategory.hom (P.germ W x hxW)) z) hres
    simp only [map_zero] at h0
    exact h0
  exact ⟨fun a b => by rw [key a, key b]⟩

end TopCat.Presheaf

namespace TopCat.Sheaf

/-- A sheaf of abelian groups vanishing on a basis of the topology is a zero object.-/
theorem isZero_of_isBasis {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hzero : ∀ U ∈ B, Subsingleton (F.obj.obj (op U))) : IsZero F := by
  rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
  intro x
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact TopCat.Presheaf.subsingleton_stalk_of_isBasis F.obj hB hzero x

end TopCat.Sheaf

namespace TopCat.Presheaf

set_option backward.isDefEq.respectTransparency false in
/-- A presheaf of abelian groups vanishing on a basis has zero sheafification.  The unit of
sheafification induces an isomorphism on stalks
(`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`), so the vanishing stalks of the presheaf
are inherited.-/
theorem isZero_sheafify_of_isBasis {X : TopCat.{u}} (P : X.Presheaf AddCommGrpCat.{u})
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hzero : ∀ U ∈ B, Subsingleton (P.obj (op U))) :
    IsZero ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj P) := by
  rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
  intro x
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  refine IsZero.of_iso ?_ (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P))).symm
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact TopCat.Presheaf.subsingleton_stalk_of_isBasis P hB hzero x

end TopCat.Presheaf
