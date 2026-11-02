/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.AlgebraicGeometry.Modules.Tilde
import Tengoku.Seed.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Tengoku.Seed.Topology.Sheaves.Sheafify

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Comparing a module-presheaf sheafification on a basis

A morphism from a presheaf of modules to a sheaf of modules induces a canonical morphism from
the associated sheaf.  If the original morphism is bijective on a topological basis, then the
induced morphism is an isomorphism.  In particular, comparison with a quasicoherent target
proves that the associated sheaf is quasicoherent.

This isolates the sheaf-theoretic last step in affine-local base-change arguments: all geometric
work may be carried out on an affine or principal-open basis.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace SchemeRelativeRiemannRoch

variable {Y : Scheme.{u}}

/-- The comparison from the associated module sheaf induced by a module-presheaf morphism.-/
noncomputable def modulePresheafSheafificationComparison
    (P : Y.PresheafOfModules) (N : Y.Modules)
    (g : P ⟶ (SheafOfModules.forget Y.ringCatSheaf).obj N) :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P ⟶ N :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 Y.ringCatSheaf.obj)).symm g

lemma modulePresheafSheafificationComparison_toSheafify_comp
    (P : Y.PresheafOfModules) (N : Y.Modules)
    (g : P ⟶ (SheafOfModules.forget Y.ringCatSheaf).obj N) :
    CategoryTheory.toSheafify
        (Opens.grothendieckTopology Y) P.presheaf ≫
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map
        (modulePresheafSheafificationComparison P N g)).1 =
      (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map g := by
  let L := modulePresheafSheafificationComparison P N g
  change
    CategoryTheory.toSheafify
        (Opens.grothendieckTopology Y) P.presheaf ≫
      (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map L.val =
      (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map g
  rw [← PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (𝟙 Y.ringCatSheaf.obj) L]
  have hL :
      PresheafOfModules.sheafificationHomEquiv
          (𝟙 Y.ringCatSheaf.obj) L = g := by
    dsimp only [L, modulePresheafSheafificationComparison]
    exact Equiv.apply_symm_apply _ g
  rw [hL]
  rfl

lemma modulePresheafComparison_stalk_isIso_of_basis_bijective
    (P : Y.PresheafOfModules) (N : Y.Modules)
    (g : P ⟶ (SheafOfModules.forget Y.ringCatSheaf).obj N)
    (B : Set Y.Opens) (hB : Opens.IsBasis B)
    (hbij : ∀ U ∈ B, Function.Bijective
      (((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map g).app (op U)))
    (x : Y) :
    IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map g)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  let FP := (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj P
  let FN := (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj
    ((SheafOfModules.forget Y.ringCatSheaf).obj N)
  let α : FP ⟶ FN :=
    (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map g
  constructor
  · apply TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB
    intro U hU
    exact (hbij U hU).1
  · intro t
    obtain ⟨U, hxU, hU, s, hs⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB FN x t
    obtain ⟨q, hq⟩ := (hbij U hU).2 s
    refine ⟨TopCat.Presheaf.germ FP U x hxU q, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hq, hs]

set_option backward.isDefEq.respectTransparency false in
theorem modulePresheafSheafificationComparison_isIso_of_basis_bijective
    (P : Y.PresheafOfModules) (N : Y.Modules)
    (g : P ⟶ (SheafOfModules.forget Y.ringCatSheaf).obj N)
    (B : Set Y.Opens) (hB : Opens.IsBasis B)
    (hbij : ∀ U ∈ B, Function.Bijective
      (((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map g).app (op U))) :
    IsIso (modulePresheafSheafificationComparison P N g) := by
  let L := modulePresheafSheafificationComparison P N g
  let T := SheafOfModules.toSheaf.{u} Y.ringCatSheaf
  let ℓ := T.map L
  letI (x : Y) :
      IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ℓ.hom) := by
    let S := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    let η :=
      CategoryTheory.toSheafify
        (Opens.grothendieckTopology Y) P.presheaf
    let α := (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map g
    letI : IsIso (S.map α) :=
      modulePresheafComparison_stalk_isIso_of_basis_bijective
        P N g B hB hbij x
    letI : IsIso (S.map η) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        x AddCommGrpCat.{u} P.presheaf
    have hcomp :
        S.map η ≫ S.map ℓ.hom = S.map α := by
      rw [← S.map_comp]
      exact congrArg S.map
        (modulePresheafSheafificationComparison_toSheafify_comp P N g)
    letI : IsIso (S.map η ≫ S.map ℓ.hom) := by
      rw [hcomp]
      infer_instance
    exact IsIso.of_isIso_comp_left (S.map η) (S.map ℓ.hom)
  haveI : IsIso ℓ :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso ℓ
  haveI : IsIso ℓ.hom := by
    exact Functor.map_isIso
      (TopCat.Sheaf.forget AddCommGrpCat.{u} Y) ℓ
  have hToPresheaf :
      (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map L.val =
        ℓ.hom := rfl
  letI : IsIso
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map L.val) := by
    rw [hToPresheaf]
    infer_instance
  haveI : IsIso L.val := by
    exact isIso_of_reflects_iso L.val
      (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj)
  have hForget :
      (SheafOfModules.forget.{u} Y.ringCatSheaf).map L =
        L.val := rfl
  letI : IsIso ((SheafOfModules.forget.{u} Y.ringCatSheaf).map L) := by
    rw [hForget]
    infer_instance
  exact isIso_of_fully_faithful
    (SheafOfModules.forget.{u} Y.ringCatSheaf) L

/-- Extend an additive comparison on a basis to all opens, using that the target is a sheaf.-/
noncomputable def modulePresheafBasisPresheafComparison
    {ι : Type u} (b : ι → Y.Opens) (hB : Opens.IsBasis (Set.range b))
    (P : Y.PresheafOfModules) (N : Y.Modules)
    (αB :
      (inducedFunctor b).op ⋙ P.presheaf ⟶
        (inducedFunctor b).op ⋙ N.presheaf) :
    P.presheaf ⟶ N.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom P.presheaf
    ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N) hB αB

lemma modulePresheafBasisPresheafComparison_app
    {ι : Type u} (b : ι → Y.Opens) (hB : Opens.IsBasis (Set.range b))
    (P : Y.PresheafOfModules) (N : Y.Modules)
    (αB :
      (inducedFunctor b).op ⋙ P.presheaf ⟶
        (inducedFunctor b).op ⋙ N.presheaf)
    (j : ι) :
    (modulePresheafBasisPresheafComparison b hB P N αB).app (op (b j)) =
      αB.app (op j) := by
  exact TopCat.Sheaf.extend_hom_app P.presheaf
    ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N) hB αB j

set_option backward.isDefEq.respectTransparency false in
lemma modulePresheafBasisPresheafComparison_map_smul
    {ι : Type u} (b : ι → Y.Opens) (hB : Opens.IsBasis (Set.range b))
    (P : Y.PresheafOfModules) (N : Y.Modules)
    (αB :
      (inducedFunctor b).op ⋙ P.presheaf ⟶
        (inducedFunctor b).op ⋙ N.presheaf)
    (hlinear : ∀ (j : ι) (s : Γ(Y, b j))
      (m : P.obj (op (b j))),
      αB.app (op j) (((P.obj (op (b j))).smul s).hom m) =
        ((N.val.obj (op (b j))).smul s).hom (αB.app (op j) m))
    (U : Y.Opens) (r : Γ(Y, U)) (m : P.obj (op U)) :
    (modulePresheafBasisPresheafComparison b hB P N αB).app
        (op U) (((P.obj (op U)).smul r).hom m) =
      ((N.val.obj (op U)).smul r).hom
        ((modulePresheafBasisPresheafComparison b hB P N αB).app
          (op U) m) := by
  let α := modulePresheafBasisPresheafComparison b hB P N αB
  let F := (SheafOfModules.toSheaf Y.ringCatSheaf).obj N
  apply TopCat.Presheaf.section_ext F U
  intro x hx
  obtain ⟨_, ⟨D, hDB, rfl⟩, hxD, hDU⟩ :=
    hB.exists_subset_of_mem_open hx U.2
  obtain ⟨j, rfl⟩ := hDB
  have hres :
      N.presheaf.map (homOfLE hDU).op
          (α.app (op U) (((P.obj (op U)).smul r).hom m)) =
        N.presheaf.map (homOfLE hDU).op
          (((N.val.obj (op U)).smul r).hom (α.app (op U) m)) := by
    calc
      N.presheaf.map (homOfLE hDU).op
          (α.app (op U) (((P.obj (op U)).smul r).hom m)) =
          α.app (op (b j))
            (P.presheaf.map (homOfLE hDU).op
              (((P.obj (op U)).smul r).hom m)) := by
        exact (α.naturality_apply (homOfLE hDU).op
          (((P.obj (op U)).smul r).hom m)).symm
      _ = α.app (op (b j))
            (((P.obj (op (b j))).smul
              ((Y.presheaf.map (homOfLE hDU).op).hom r)).hom
                (P.presheaf.map (homOfLE hDU).op m)) := by
        exact congrArg (fun z => α.app (op (b j)) z)
          (P.map_smul (homOfLE hDU).op r m)
      _ = ((N.val.obj (op (b j))).smul
              ((Y.presheaf.map (homOfLE hDU).op).hom r)).hom
            (α.app (op (b j))
              (P.presheaf.map (homOfLE hDU).op m)) := by
        rw [modulePresheafBasisPresheafComparison_app]
        exact hlinear j
          ((Y.presheaf.map (homOfLE hDU).op).hom r)
          (P.presheaf.map (homOfLE hDU).op m)
      _ = ((N.val.obj (op (b j))).smul
              ((Y.presheaf.map (homOfLE hDU).op).hom r)).hom
            (N.presheaf.map (homOfLE hDU).op (α.app (op U) m)) := by
        exact congrArg
          (fun z : Γ(N, b j) =>
            ((N.val.obj (op (b j))).smul
              ((Y.presheaf.map (homOfLE hDU).op).hom r)).hom z)
          (α.naturality_apply (homOfLE hDU).op m)
      _ = N.presheaf.map (homOfLE hDU).op
            (((N.val.obj (op U)).smul r).hom (α.app (op U) m)) := by
        exact (N.map_smul (homOfLE hDU) r (α.app (op U) m)).symm
  calc
    N.presheaf.germ U x hx
        (α.app (op U) (((P.obj (op U)).smul r).hom m)) =
        N.presheaf.germ (b j) x hxD
          (N.presheaf.map (homOfLE hDU).op
            (α.app (op U) (((P.obj (op U)).smul r).hom m))) :=
      (N.presheaf.germ_res_apply (homOfLE hDU) x hxD _).symm
    _ = N.presheaf.germ (b j) x hxD
          (N.presheaf.map (homOfLE hDU).op
            (((N.val.obj (op U)).smul r).hom (α.app (op U) m))) := by
      rw [hres]
    _ = N.presheaf.germ U x hx
          (((N.val.obj (op U)).smul r).hom (α.app (op U) m)) :=
      N.presheaf.germ_res_apply (homOfLE hDU) x hxD _

/-- A basiswise linear additive comparison extends to a morphism of module presheaves.-/
noncomputable def modulePresheafBasisComparison
    {ι : Type u} (b : ι → Y.Opens) (hB : Opens.IsBasis (Set.range b))
    (P : Y.PresheafOfModules) (N : Y.Modules)
    (αB :
      (inducedFunctor b).op ⋙ P.presheaf ⟶
        (inducedFunctor b).op ⋙ N.presheaf)
    (hlinear : ∀ (j : ι) (s : Γ(Y, b j))
      (m : P.obj (op (b j))),
      αB.app (op j) (((P.obj (op (b j))).smul s).hom m) =
        ((N.val.obj (op (b j))).smul s).hom (αB.app (op j) m)) :
    P ⟶ (SheafOfModules.forget Y.ringCatSheaf).obj N :=
  PresheafOfModules.homMk
    (modulePresheafBasisPresheafComparison b hB P N αB)
    (fun U r m =>
      modulePresheafBasisPresheafComparison_map_smul
        b hB P N αB hlinear U.unop r m)

/-- A basiswise linear, componentwise bijective comparison identifies the associated module
sheaf with the target.-/
theorem modulePresheafBasisSheafificationComparison_isIso
    {ι : Type u} (b : ι → Y.Opens) (hB : Opens.IsBasis (Set.range b))
    (P : Y.PresheafOfModules) (N : Y.Modules)
    (αB :
      (inducedFunctor b).op ⋙ P.presheaf ⟶
        (inducedFunctor b).op ⋙ N.presheaf)
    (hlinear : ∀ (j : ι) (s : Γ(Y, b j))
      (m : P.obj (op (b j))),
      αB.app (op j) (((P.obj (op (b j))).smul s).hom m) =
        ((N.val.obj (op (b j))).smul s).hom (αB.app (op j) m))
    (hbij : ∀ j, Function.Bijective (αB.app (op j))) :
    IsIso (modulePresheafSheafificationComparison P N
      (modulePresheafBasisComparison b hB P N αB hlinear)) := by
  apply modulePresheafSheafificationComparison_isIso_of_basis_bijective
    P N (modulePresheafBasisComparison b hB P N αB hlinear)
    (Set.range b) hB
  intro U hU
  obtain ⟨j, rfl⟩ := hU
  change Function.Bijective
    ((modulePresheafBasisPresheafComparison b hB P N αB).app (op (b j)))
  rw [modulePresheafBasisPresheafComparison_app]
  exact hbij j

/-- A basiswise linear, componentwise bijective comparison with a quasicoherent target proves
quasicoherence of the associated module sheaf.-/
theorem modulePresheafBasisSheafification_isQuasicoherent
    {ι : Type u} (b : ι → Y.Opens) (hB : Opens.IsBasis (Set.range b))
    (P : Y.PresheafOfModules) (N : Y.Modules) [N.IsQuasicoherent]
    (αB :
      (inducedFunctor b).op ⋙ P.presheaf ⟶
        (inducedFunctor b).op ⋙ N.presheaf)
    (hlinear : ∀ (j : ι) (s : Γ(Y, b j))
      (m : P.obj (op (b j))),
      αB.app (op j) (((P.obj (op (b j))).smul s).hom m) =
        ((N.val.obj (op (b j))).smul s).hom (αB.app (op j) m))
    (hbij : ∀ j, Function.Bijective (αB.app (op j))) :
    ((PresheafOfModules.sheafification
      (𝟙 Y.ringCatSheaf.obj)).obj P).IsQuasicoherent := by
  let g := modulePresheafBasisComparison b hB P N αB hlinear
  letI : IsIso (modulePresheafSheafificationComparison P N g) :=
    modulePresheafBasisSheafificationComparison_isIso
      b hB P N αB hlinear hbij
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (asIso (modulePresheafSheafificationComparison P N g)).symm
    inferInstance

/-- A basiswise isomorphism to a quasicoherent target makes the associated module sheaf
quasicoherent.-/
theorem modulePresheafSheafification_isQuasicoherent_of_basis_bijective
    (P : Y.PresheafOfModules) (N : Y.Modules) [N.IsQuasicoherent]
    (g : P ⟶ (SheafOfModules.forget Y.ringCatSheaf).obj N)
    (B : Set Y.Opens) (hB : Opens.IsBasis B)
    (hbij : ∀ U ∈ B, Function.Bijective
      (((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map g).app (op U))) :
    ((PresheafOfModules.sheafification
      (𝟙 Y.ringCatSheaf.obj)).obj P).IsQuasicoherent := by
  letI : IsIso (modulePresheafSheafificationComparison P N g) :=
    modulePresheafSheafificationComparison_isIso_of_basis_bijective
      P N g B hB hbij
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (asIso (modulePresheafSheafificationComparison P N g)).symm
    inferInstance

end SchemeRelativeRiemannRoch
