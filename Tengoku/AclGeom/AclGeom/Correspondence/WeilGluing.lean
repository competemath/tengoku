/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.Seed.AlgebraicGeometry.Gluing
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FiniteType
import Tengoku.Seed.AlgebraicGeometry.Morphisms.QuasiCompact
import Tengoku.Seed.AlgebraicGeometry.Properties

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scheme-theoretic consequences of Weil chart gluing

This module supplies the gluing layer used in blueprint Theorem 8.2.  It
starts with Mathlib's explicit `Scheme.GlueData`, so the output is an
actual scheme obtained from open charts and transition isomorphisms.

Compatible chart morphisms descend to the glued scheme.  In particular,
compatible structure morphisms to a base scheme make the gluing relative
over that base.  Local finite type then descends from the charts, while a
finite atlas of quasi-compact chart morphisms is quasi-compact.  Finally,
integral charts with nonempty pairwise overlaps glue to an integral
scheme.  A family of charts containing one fixed open subscheme is also
packaged as gluing data whose transition and triple-cocycle maps are strict
identities on that common overlap.  These are precisely the local finite-type and irreducibility
arguments in Weil's construction; separatedness and the finite atlas for
the eventual group are established only after multiplication and inverse
have been glued.

This module is part of the formalization of the
Evans--Hrushovski--Gismatullin reconstruction theorem; the source of truth
is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open CategoryTheory CategoryTheory.Limits Function
open AlgebraicGeometry

universe u

namespace WeilGluing

variable {J : Type u} (U : J → Scheme.{u}) (W : Scheme.{u})
  (f : ∀ i, W ⟶ U i) [hopen : ∀ i, IsOpenImmersion (f i)]

/-- Categorical gluing data for a family of charts that all contain the same
open subscheme.  Every off-diagonal overlap is `W` and every transition on
`W` is the identity, so the triple-overlap cocycle is literal.-/
def commonOverlapGlueData' : CategoryTheory.GlueData'.{u, u + 1} Scheme.{u} where
  J := J
  U := U
  V i j h := W
  f i j h := f i
  t i j h := 𝟙 W
  t' i j k hij hik hjk :=
    pullback.lift (pullback.fst _ _) (pullback.fst _ _) rfl
  t_fac i j k hij hik hjk := by
    rw [pullback.lift_snd, Category.comp_id]
  t_inv i j hij := by simp
  cocycle i j k hij hik hjk := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        Category.id_comp]
      exact fst_eq_snd_of_mono_eq (f i)

/-- A family of open immersions from one fixed scheme into a family of
charts determines actual scheme gluing data with a strict identity cocycle
on the common overlap.-/
def commonOverlapGlueData : Scheme.GlueData where
  toGlueData := CategoryTheory.GlueData.ofGlueData'
    (commonOverlapGlueData' U W f)
  f_open i j := by
    classical
    change IsOpenImmersion ((commonOverlapGlueData' U W f).f' i j)
    delta CategoryTheory.GlueData'.f'
    split
    · infer_instance
    · delta commonOverlapGlueData'
      letI := hopen i
      exact IsOpenImmersion.comp _ _

variable (D : Scheme.GlueData.{u})

/-- A family of morphisms on the charts is compatible when the two maps
from every transition overlap agree.-/
def CompatibleMaps {X : Scheme.{u}} (g : ∀ i, D.U i ⟶ X) : Prop :=
  ∀ i j, D.f i j ≫ g i = D.t i j ≫ D.f j i ≫ g j

/-- Compatible morphisms from the charts descend to the glued scheme.-/
def desc {X : Scheme.{u}} (g : ∀ i, D.U i ⟶ X)
    (hg : CompatibleMaps D g) : D.glued ⟶ X := by
  fapply Multicoequalizer.desc
  · exact g
  · rintro ⟨i, j⟩
    change D.f i j ≫ g i = (D.t i j ≫ D.f j i) ≫ g j
    simpa only [Category.assoc] using hg i j

/-- The descended morphism restricts to the prescribed map on every
chart.-/
@[simp, reassoc]
theorem ι_desc {X : Scheme.{u}} (g : ∀ i, D.U i ⟶ X)
    (hg : CompatibleMaps D g) (i : D.J) :
    D.ι i ≫ desc D g hg = g i :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- Morphisms out of a glued scheme are determined on its charts.-/
theorem hom_ext {X : Scheme.{u}} (f g : D.glued ⟶ X)
    (h : ∀ i, D.ι i ≫ f = D.ι i ≫ g) : f = g := by
  apply Multicoequalizer.hom_ext
  exact h

/-- The structure morphism obtained by gluing compatible chart morphisms
to a fixed base scheme.-/
abbrev toBase {S : Scheme.{u}} (s : ∀ i, D.U i ⟶ S)
    (hs : CompatibleMaps D s) : D.glued ⟶ S :=
  desc D s hs

-- Unfold the scheme-morphism property to synthesize its source-locality instance.
set_option backward.isDefEq.respectTransparency.types false in
/-- Local finite type over the base descends from every chart of a
scheme gluing.-/
instance toBase_locallyOfFiniteType {S : Scheme.{u}}
    (s : ∀ i, D.U i ⟶ S) (hs : CompatibleMaps D s)
    [hlt : ∀ i, LocallyOfFiniteType (s i)] :
    LocallyOfFiniteType (toBase D s hs) := by
  apply IsZariskiLocalAtSource.of_openCover D.openCover
  intro i
  change LocallyOfFiniteType (D.ι i ≫ toBase D s hs)
  rw [ι_desc D s hs i]
  exact hlt i

/-- A finite gluing of charts quasi-compact over the base is
quasi-compact over the base.-/
instance toBase_quasiCompact {S : Scheme.{u}}
    (s : ∀ i, D.U i ⟶ S) (hs : CompatibleMaps D s)
    [Finite D.J] [∀ i, QuasiCompact (s i)] :
    QuasiCompact (toBase D s hs) := by
  constructor
  intro U hU hUc
  have hpreimage :
      toBase D s hs ⁻¹' U =
        ⋃ i, D.ι i '' ((s i) ⁻¹' U) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
      refine Set.mem_iUnion.2 ⟨i, ⟨y, ?_, rfl⟩⟩
      have heq : toBase D s hs (D.ι i y) = s i y := by
        rw [← Scheme.Hom.comp_apply, ι_desc D s hs i]
      change toBase D s hs (D.ι i y) ∈ U at hx
      change s i y ∈ U
      rwa [heq] at hx
    · intro hx
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
      have heq : toBase D s hs (D.ι i y) = s i y := by
        rw [← Scheme.Hom.comp_apply, ι_desc D s hs i]
      change s i y ∈ U at hy
      change toBase D s hs (D.ι i y) ∈ U
      rwa [heq]
  rw [hpreimage]
  apply isCompact_iUnion
  intro i
  have hi : IsCompact ((s i) ⁻¹' U) :=
    QuasiCompact.isCompact_preimage U hU hUc
  exact hi.image (D.ι i).continuous

/-- Chart maps to a fixed target are compatible on a common-overlap atlas
when all of their restrictions to the common overlap agree.-/
theorem commonOverlap_compatible {S : Scheme.{u}}
    (s : ∀ i, U i ⟶ S) (w : W ⟶ S)
    (h : ∀ i, f i ≫ s i = w) :
    CompatibleMaps (commonOverlapGlueData U W f) s := by
  unfold CompatibleMaps
  change ∀ i j : J,
    (commonOverlapGlueData U W f).f i j ≫ s i =
      (commonOverlapGlueData U W f).t i j ≫
        (commonOverlapGlueData U W f).f j i ≫ s j
  intro i j
  classical
  by_cases hij : i = j
  · subst j
    simp [commonOverlapGlueData, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', commonOverlapGlueData']
  · simp [commonOverlapGlueData, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', hij, Ne.symm hij, commonOverlapGlueData', h]

/-- The morphism from a common-overlap gluing obtained by descending a
compatible family of chart morphisms.-/
def commonOverlapToBase {S : Scheme.{u}}
    (s : ∀ i, U i ⟶ S) (w : W ⟶ S)
    (h : ∀ i, f i ≫ s i = w) :
    (commonOverlapGlueData U W f).glued ⟶ S :=
  toBase (commonOverlapGlueData U W f) s
    (commonOverlap_compatible U W f s w h)

/-- The descended common-overlap morphism restricts to its prescribed map
on each chart.-/
@[simp, reassoc]
theorem commonOverlap_ι_toBase {S : Scheme.{u}}
    (s : ∀ i, U i ⟶ S) (w : W ⟶ S)
    (h : ∀ i, f i ≫ s i = w) (i : J) :
    (commonOverlapGlueData U W f).ι i ≫
      commonOverlapToBase U W f s w h = s i := by
  unfold commonOverlapToBase
  apply ι_desc

instance commonOverlapToBase_locallyOfFiniteType {S : Scheme.{u}}
    (s : ∀ i, U i ⟶ S) (w : W ⟶ S)
    (h : ∀ i, f i ≫ s i = w)
    [hft : ∀ i, LocallyOfFiniteType (s i)] :
    LocallyOfFiniteType (commonOverlapToBase U W f s w h) := by
  unfold commonOverlapToBase
  exact @toBase_locallyOfFiniteType (commonOverlapGlueData U W f) S s
    (commonOverlap_compatible U W f s w h) (fun i ↦ hft i)

instance commonOverlapToBase_quasiCompact {S : Scheme.{u}} [hJ : Finite J]
    (s : ∀ i, U i ⟶ S) (w : W ⟶ S)
    (h : ∀ i, f i ≫ s i = w)
    [hqc : ∀ i, QuasiCompact (s i)] :
    QuasiCompact (commonOverlapToBase U W f s w h) := by
  unfold commonOverlapToBase
  exact @toBase_quasiCompact (commonOverlapGlueData U W f) S s
    (commonOverlap_compatible U W f s w h) hJ (fun i ↦ hqc i)

/-- The glued scheme is reduced when every chart is reduced.-/
instance isReduced [hred : ∀ i, IsReduced (D.U i)] : IsReduced D.glued := by
  letI (i : D.openCover.I₀) : IsReduced (D.openCover.X i) :=
    hred i
  exact IsReduced.of_openCover D.glued D.openCover

/-- If every chart is irreducible and every pairwise overlap is nonempty,
then the glued topological space is preirreducible.-/
instance preirreducibleSpace
    [∀ i, IrreducibleSpace (D.U i)]
    [∀ i j, Nonempty (D.V (i, j)).carrier] :
    PreirreducibleSpace D.glued := by
  let U : D.J → TopologicalSpace.Opens D.glued :=
    fun i ↦ (D.ι i).opensRange
  have hU (i : D.J) : IsPreirreducible (U i : Set D.glued) := by
    change IsPreirreducible (Set.range (D.ι i))
    rw [← Set.image_univ]
    exact PreirreducibleSpace.isPreirreducible_univ.image
      (D.ι i) (D.ι i).continuous.continuousOn
  have hpair : Pairwise ((¬ Disjoint · ·) on U) := by
    intro i j hij
    change ¬ Disjoint (U i) (U j)
    rw [disjoint_iff]
    intro hdisj
    let x : (D.V (i, j)).carrier := Classical.choice inferInstance
    have hx : D.ι i (D.f i j x) ∈ U i ∧
        D.ι i (D.f i j x) ∈ U j := by
      constructor
      · exact ⟨D.f i j x, rfl⟩
      · refine ⟨D.f j i (D.t i j x), ?_⟩
        change (D.t i j ≫ D.f j i ≫ D.ι j) x =
          (D.f i j ≫ D.ι i) x
        rw [D.glue_condition]
    have : D.ι i (D.f i j x) ∈ U i ⊓ U j := hx
    rw [hdisj] at this
    exact this
  exact PreirreducibleSpace.of_isOpenCover hpair
    D.openCover.isOpenCover_opensRange (fun i ↦
      (isPreirreducible_iff_preirreducibleSpace.mp (hU i)))

/-- A nonempty gluing has a nonempty underlying topological space when
its charts are nonempty.-/
instance nonemptyGlued [Nonempty D.J] [∀ i, Nonempty (D.U i).carrier] :
    Nonempty D.glued.carrier := by
  let i : D.J := Classical.choice inferInstance
  let x : (D.U i).carrier := Classical.choice inferInstance
  exact ⟨D.ι i x⟩

/-- A nonempty gluing of irreducible charts with nonempty pairwise
overlaps is irreducible.-/
instance irreducibleSpace [Nonempty D.J]
    [∀ i, IrreducibleSpace (D.U i)]
    [∀ i j, Nonempty (D.V (i, j)).carrier] :
    IrreducibleSpace D.glued where
  toPreirreducibleSpace := inferInstance
  toNonempty := inferInstance

/-- Integral charts with nonempty pairwise overlaps glue to an integral
scheme.-/
instance isIntegral [Nonempty D.J] [∀ i, IsIntegral (D.U i)]
    [∀ i j, Nonempty (D.V (i, j)).carrier] : IsIntegral D.glued := by
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨inferInstance, inferInstance⟩

end WeilGluing

end

end AclGeom
