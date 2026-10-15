/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import Tengoku

/-!
# LeanPool.WhiteheadTheorem.HomotopyGroup.InducedMaps

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.HomotopyGroup.InducedMaps`.
-/

@[expose] public section

open CategoryTheory
open scoped Topology Topology.Homotopy

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- `PointedTopCat` -/
abbrev PointedTopCat := Under (TopCat.of PUnit)

namespace PointedTopCat

universe u

/-- Make a pointed topological space from `X` and a piont in `X`. -/
abbrev of (point : X) : PointedTopCat.{u} :=
  Under.mk <| TopCat.ofHom <| ContinuousMap.const _ point

/-- Typecheck a `ContinuousMap` as a morphism in `PointedTopCat`, by choosing a point in `X`. -/
abbrev ofHom (f : C(X, Y)) (point : X) :
    PointedTopCat.of point ⟶ PointedTopCat.of (f point) :=
  Under.homMk (TopCat.ofHom f)

namespace Hom

/-- Change the target point of a morphism of `PointedTopCat`
from `g point` to `f point`, given `g = f`.  Useful to fix definitional equality. -/
abbrev rwTargetPt {f g : C(X, Y)} (point : X) (gf : g = f) :
    PointedTopCat.of point ⟶ PointedTopCat.of (f point) :=
  Under.homMk (TopCat.ofHom g)

/--
@isnad1 id=eq.1h5v.s7.72ceb0526fce from=translated src=- shape=9e16377e vocab=640084dd
-/
lemma toFun_rwTargetPt {f g : C(X, Y)} (point : X) (gf : g = f) :
    (rwTargetPt point gf).right.hom.toFun = g :=
  rfl

/--
@isnad1 id=eq.1h5v.s6.bf24ff58b4b0 from=translated src=- shape=84a36913 vocab=766054cc
-/
lemma rwTargetPt_eq {f g : C(X, Y)} (point : X) (gf : g = f) :
    rwTargetPt point gf = ofHom f point := by
  simp_all

end Hom

/-- Typecheck a morphism in `TopCat` as a morphism in `PointedTopCat`,
by choosing a point in `X`. -/
abbrev ofHom' {X Y : TopCat.{u}} (f : X ⟶ Y) (point : X) :
    PointedTopCat.of point ⟶ PointedTopCat.of (f point) :=
  Under.homMk f

namespace Hom'

/-- Change the target point of a morphism of `PointedTopCat`
from `g point` to `f point`, given `g = f`.  Useful to fix definitional equality. -/
abbrev rwTargetPt {X Y : TopCat.{u}} {f g : X ⟶ Y} (point : X) (gf : g = f) :
    PointedTopCat.of point ⟶ PointedTopCat.of (f point) :=
  Under.homMk g

/--
@isnad1 id=eq.1h5v.s9.b6bea995a809 from=translated src=- shape=0386c33a vocab=dcbe7482
-/
lemma toFun_rwTargetPt {X Y : TopCat.{u}} {f g : X ⟶ Y} (point : X) (gf : g = f) :
    (rwTargetPt point gf).right.hom.toFun = g :=
  rfl

/--
@isnad1 id=eq.1h5v.s7.f5adba218d19 from=translated src=- shape=bf71fc8e vocab=5bc8a693
-/
lemma rwTargetPt_eq {X Y : TopCat.{u}} {f g : X ⟶ Y} (point : X) (gf : g = f) :
    rwTargetPt point gf = ofHom' f point := by
  simp_all

end Hom'

/-- Regard a pointed topological space as simply a topological space. -/
abbrev as (X : PointedTopCat.{u}) : TopCat.{u} := X.right

/-- The distinguished piont of a pointed topological space -/
abbrev point (X : PointedTopCat.{u}) : X.as := (TopCat.Hom.hom X.hom) PUnit.unit

/-- A morphism between pointed topological spaces maps the base point to the base point.
@isnad1 id=eq.0h3v.s7.c074638ae71a from=translated src=- shape=42038cb1 vocab=a686241d
-/
lemma w {X Y : PointedTopCat.{u}} (f : X ⟶ Y) : f.right X.point = Y.point := by
  change (TopCat.Hom.hom (X.hom ≫ f.right)) _ = _
  rw [Under.w]

lemma _root_.TopCat.isIso_of_isHomeomorph
    (f : C(X, Y)) (hf : IsHomeomorph f) : IsIso (TopCat.ofHom f) :=
  let e : TopCat.of X ≅ TopCat.of Y := TopCat.isoOfHomeo (IsHomeomorph.homeomorph f hf)
  ⟨e.inv, ⟨e.hom_inv_id, e.inv_hom_id⟩⟩

/--
@isnad1 id=isiso.1h4v.s6.ca9b004ee255 from=translated src=- shape=83ea3ac6 vocab=0f2da093
-/
lemma isIso_of_isHomeomorph
    (f : C(X, Y)) (point : X) (hf : IsHomeomorph f) : IsIso (PointedTopCat.ofHom f point) :=
  let e : TopCat.of X ≅ TopCat.of Y := TopCat.isoOfHomeo (IsHomeomorph.homeomorph f hf)
  let E : PointedTopCat.of point ≅ PointedTopCat.of (f point) := Under.isoMk e
  ⟨E.inv, ⟨E.hom_inv_id, E.inv_hom_id⟩⟩

/--
@isnad1 id=eq.0h6v.s7.02ba71eafc3b from=translated src=- shape=c128de2c vocab=f588bcb0
-/
lemma ofHom_comp (f : C(X, Y)) (g : C(Y, Z)) (point : X) :
    ofHom (g.comp f) point = (ofHom f point) ≫ (ofHom g (f point)) := by
  unfold ofHom
  simp only [ContinuousMap.comp_apply, TopCat.ofHom_comp]
  rfl

/--
@isnad1 id=eq.0h6v.s8.36be6529d191 from=translated src=- shape=9c7d1872 vocab=89855608
-/
lemma ofHom'_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (point : X) :
    ofHom' (f ≫ g) point = (ofHom' f point) ≫ (ofHom' g (f point)) := by
  unfold ofHom'
  simp only []
  rfl

end PointedTopCat

namespace Pointed

/--
@isnad1 id=iff.0h5v.s7.10e4f4072ada from=translated src=- shape=961834aa vocab=f3677f5a
-/
lemma isIso_iff_bijective {A B : Type u} {a₀ : A} {b₀ : B}
    (f : Pointed.of a₀ ⟶ Pointed.of b₀) : IsIso f ↔ Function.Bijective f := by
  constructor
  · intro isof
    refine ⟨?_, ?_⟩
    · intro a₁ a₂ ha
      have h1 : (f ≫ inv f) a₁ = (f ≫ inv f) a₂ := by
        change (inv f) (f a₁) = (inv f) (f a₂)
        rw [ha]
      simp_all
    · intro b
      refine ⟨(inv f) b, ?_⟩
      simp_all
  · intro bf
    constructor
    obtain ⟨g, ⟨gl, gr⟩⟩ := Function.bijective_iff_has_inverse.mp bf
    use { toFun := g,
          map_point := by
            dsimp only
            have : f a₀ = b₀ := f.map_point
            rw [← this, gl a₀] }
    constructor
    · ext a; exact gl a
    · ext b; exact gr b

namespace Hom

/-- Change the target point of a `Pointed.Hom` from `g point` to `f point`, given `g = f`.
Useful to fix definitional equality. -/
abbrev rwTargetPt {X Y : Type u} (point : X) {f g : X → Y} (gf : g = f) :
    of point ⟶ of (f point) :=
  ⟨g, by rw [gf]⟩

/--
@isnad1 id=eq.1h5v.s5.b22014c4fb7c from=translated src=- shape=42e1b19d vocab=61ba3b90
-/
lemma toFun_rwTargetPt {X Y : Type u} (point : X) {f g : X → Y} (gf : g = f) :
    (rwTargetPt point gf).toFun = g :=
  rfl

/--
@isnad1 id=eq.1h5v.s5.be4efd7b17ce from=translated src=- shape=e64bd361 vocab=62e570d3
-/
lemma rwTargetPt_eq {X Y : Type u} (point : X) {f g : X → Y} (gf : g = f) :
    rwTargetPt point gf = ⟨f, rfl⟩ := by
  simp_all

end Hom

end Pointed

namespace GenLoop

/-- The map of `GenLoop`s induced by a morphism `f : X ⟶ Y` of pointed topological spaces -/
def inducedMap' (n : ℕ) {X Y : PointedTopCat} (f : X ⟶ Y) :
    Ω^ (Fin n) X.as X.point → Ω^ (Fin n) Y.as Y.point :=
  fun α ↦ ⟨f.right.hom.comp α.val, fun i hi ↦ by
    rw [ContinuousMap.comp_apply, ← PointedTopCat.w f]
    congr 1
    exact α.property i hi ⟩

/-- The map of `GenLoop`s induced by a continuous map `f : C(X, Y)` -/
abbrev inducedMap (n : ℕ) (x : X) (f : C(X, Y)) :
    Ω^ (Fin n) X x → Ω^ (Fin n) Y (f x) :=
  inducedMap' n (PointedTopCat.ofHom f x)

end GenLoop

namespace HomotopyGroup

private theorem inducedMap'_respects (n : ℕ) {X Y : PointedTopCat} (f : X ⟶ Y)
    {α β : Ω^ (Fin n) X.as X.point} (hαβ : α ≈ β) :
    GenLoop.inducedMap' n f α ≈ GenLoop.inducedMap' n f β := by
  let H := hαβ.some
  have := H.toHomotopy
  exact Nonempty.intro <|
    { toHomotopy := (ContinuousMap.Homotopy.refl f.right.hom).comp H.toHomotopy
      prop' t y hy := by
        simp only [GenLoop.inducedMap', ContinuousMap.toFun_eq_coe,
          ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.comp_apply,
          ContinuousMap.Homotopy.refl_apply, ContinuousMap.coe_mk, ContinuousMap.comp_apply]
        have hprop : H.toHomotopy (t, y) = α.val y := by
          have := H.prop' t y hy
          simpa using this
        rw [hprop] }

/-- The map between homotopy groups (as sets)
induced by a morphism `f : X ⟶ Y` of pointed topological spaces -/
def inducedMap' (n : ℕ) {X Y : PointedTopCat} (f : X ⟶ Y) :
    π_ n X.as X.point → π_ n Y.as Y.point :=
  Quotient.map (GenLoop.inducedMap' n f) fun {α β} hαβ ↦ by
    exact inducedMap'_respects n f (α := α) (β := β) hαβ

/--
@isnad1 id=eq.0h4v.s6.cf2aa036168a from=translated src=- shape=b298d9b6 vocab=bc6b2dc2
-/
lemma inducedMap'_default (n : ℕ) {X Y : PointedTopCat} (f : X ⟶ Y) :
    inducedMap' n f (default : π_ n X.as X.point) = (default : π_ n Y.as Y.point) := by
  change inducedMap' n f ⟦GenLoop.const⟧ = ⟦GenLoop.const⟧
  unfold inducedMap'
  dsimp only [Quotient.map_mk]
  unfold GenLoop.const
  simp only [GenLoop.inducedMap', ContinuousMap.comp_const]
  congr 2
  ext y
  rw [ContinuousMap.const_apply]
  exact PointedTopCat.w f

/-- The map between homotopy groups (as sets) induced by a continuous map `f : C(X, Y)` -/
abbrev inducedMap (n : ℕ) (x : X) (f : C(X, Y)) :
    π_ n X x → π_ n Y (f x) :=
  inducedMap' n (PointedTopCat.ofHom f x)

namespace inducedMap

/-- Change an induced map's target point from `g x` to `f x`, given `g = f`.
Useful to fix definitional equality. -/
abbrev rwTargetPt (n : ℕ) {f g : C(X, Y)} (x : X) (gf : g = f) :
    π_ n X x → π_ n Y (f x) :=
  inducedMap' n (PointedTopCat.Hom.rwTargetPt x gf)

/--
@isnad1 id=eq.1h6v.s6.4106547ceb02 from=translated src=- shape=908a82fb vocab=adc89237
-/
lemma rwTargetPt_eq (n : ℕ) {f g : C(X, Y)} (x : X) (gf : g = f) :
    rwTargetPt n x gf = inducedMap n x f := by
  rw [rwTargetPt, PointedTopCat.Hom.rwTargetPt_eq]

end inducedMap

/-- `π_n` is a functor sending a based topological space `(X, x₀)`
to its `n`-th homotopy group (as a type, ignoring its group structure) based at `x₀`. -/
noncomputable def functorToType (n : ℕ) : PointedTopCat.{u} ⥤ Type u where
  obj X := π_ n X.as X.point
  map {X Y} f := TypeCat.ofHom (inducedMap' n f)
  map_id X := by
    ext α
    change inducedMap' n (𝟙 X) α = α
    simp only [inducedMap']
    rw [← Quotient.out_eq α, Quotient.map_mk]
    congr 1
  map_comp {X Y Z} f g := by
    ext α
    change inducedMap' n (f ≫ g) α = inducedMap' n g (inducedMap' n f α)
    simp only [inducedMap']
    rw [← Quotient.out_eq α]
    iterate 3 (rw [Quotient.map_mk])
    congr 1

/-- `π_n` is a functor sending a based topological space `(X, x₀)`
to its `n`-th homotopy group
(as a pointed type whose base point is the contant map, ignoring its group structure)
based at `x₀`. -/
noncomputable def functorToPointed (n : ℕ) : PointedTopCat.{u} ⥤ Pointed.{u} where
  obj X := Pointed.of (default : π_ n X.as X.point)
  map {X Y} f :=
    { toFun := (functorToType n).map f
      map_point := inducedMap'_default n f }
  map_id X := by
    simp only [
      CategoryTheory.Functor.map_id]
    congr
  map_comp {X Y Z} f g := by
    simp only [
      Functor.map_comp]
    congr

-- TODO (phase 3): The `functorToGrp` definition was here.
-- Its `map_mul` proof relied on subtle definitional equalities between the
-- old `HomotopyGroup` multiplication and `GenLoop.transAt`, which changed
-- substantially under v4.30 (the multiplicative structure now unfolds through
-- `loopHomeo` rather than being directly `transAt`-based). Restoring this
-- functor (whose `map` field requires the `map_mul` step) needs a new proof
-- strategy via `HomotopyGroup.mul_spec` plus a fresh ⟦·⟧ congruence argument.
-- It is unused elsewhere in this project. -/

/-- The morphism $f_{*} : π_n(X, x₀) → π_n(Y, f(x₀))$ in the category `Pointed`,
induced by the continuous map `f : C(X, Y)` -/
noncomputable abbrev inducedPointedHom (n : ℕ) (x₀ : X) (f : C(X, Y)) :
    Pointed.of (default : π_ n X x₀) ⟶ Pointed.of (default : π_ n Y (f x₀)) :=
  (functorToPointed n).map (PointedTopCat.ofHom f x₀)

/-- The morphism $f_{*} : π_n(X, x₀) → π_n(Y, f(x₀))$ in the category `Pointed`,
induced by the morphism `f : X ⟶ Y` in `TopCat` -/
noncomputable abbrev inducedPointedHom' (n : ℕ) {X Y : TopCat.{u}} (x₀ : X) (f : X ⟶ Y) :
    Pointed.of (default : π_ n X x₀) ⟶ Pointed.of (default : π_ n Y (f x₀)) :=
  (functorToPointed n).map (PointedTopCat.ofHom' f x₀)

/--
@isnad1 id=eq.0h5v.s8.0a92b5232cd1 from=translated src=- shape=b5d85b57 vocab=4084e1f2
-/
lemma inducedPointedHom'_eq_inducedPointedHom
    (n : ℕ) {X Y : TopCat.{u}} (x₀ : X) (f : X ⟶ Y) :
    inducedPointedHom' n x₀ f = inducedPointedHom n x₀ f.hom :=
  rfl

namespace inducedPointedHom

/-- `isoTarget` -/
noncomputable abbrev isoTarget (n : ℕ) {f g : C(X, Y)} (x₀ : X) (gf : g = f) :
    Pointed.of (default : π_ n Y (g x₀)) ≅ Pointed.of (default : π_ n Y (f x₀)) :=
  gf ▸ Iso.refl _

/-- Change an induced pointed morphism's target point from `g x₀` to `f x₀`, given `g = f`.
Useful to fix definitional equality. -/
noncomputable abbrev rwTargetPt (n : ℕ) {f g : C(X, Y)} (x₀ : X) (gf : g = f) :
    Pointed.of (default : π_ n X x₀) ⟶ Pointed.of (default : π_ n Y (f x₀)) :=
  (functorToPointed n).map (PointedTopCat.Hom.rwTargetPt x₀ gf)

/--
@isnad1 id=eq.1h6v.s7.e852fcd98a4f from=translated src=- shape=41c9de0d vocab=82bc6cef
-/
lemma toFun_rwTargetPt
     (n : ℕ) {f g : C(X, Y)} (x₀ : X) (gf : g = f) :
    (rwTargetPt n x₀ gf).toFun =
    inducedMap.rwTargetPt n x₀ gf := by
  rfl

/--
@isnad1 id=eq.1h6v.s7.2dfedff907ff from=translated src=- shape=98c1ec0f vocab=6b78b0d1
-/
lemma rwTargetPt_eq (n : ℕ) {f g : C(X, Y)} (x₀ : X) (gf : g = f) :
    rwTargetPt n x₀ gf = inducedPointedHom n x₀ f := by
  simp_all

end inducedPointedHom

namespace inducedPointedHom'

/-- `isoTarget` -/
noncomputable abbrev isoTarget
    (n : ℕ) {X Y : TopCat.{u}} (x₀ : X) {f g : X ⟶ Y} (gf : g = f) :
    Pointed.of (default : π_ n Y (g x₀)) ≅ Pointed.of (default : π_ n Y (f x₀)) :=
  gf ▸ Iso.refl _

/-- Change an induced pointed morphism's target point from `g x₀` to `f x₀`, given `g = f`.
Useful to fix definitional equality. -/
noncomputable abbrev rwTargetPt
    (n : ℕ) {X Y : TopCat.{u}} (x₀ : X) {f g : X ⟶ Y} (gf : g = f) :
    Pointed.of (default : π_ n X x₀) ⟶ Pointed.of (default : π_ n Y (f x₀)) :=
  (functorToPointed n).map (PointedTopCat.Hom'.rwTargetPt x₀ gf)

/--
@isnad1 id=eq.1h6v.s9.fb189e9e2a27 from=translated src=- shape=7f661a8d vocab=b5b84c35
-/
lemma toFun_rwTargetPt
    (n : ℕ) {X Y : TopCat.{u}} (x₀ : X) {f g : X ⟶ Y} (gf : g = f) :
    (rwTargetPt n x₀ gf).toFun =
    inducedMap.rwTargetPt n x₀ (congr_arg TopCat.Hom.hom gf) := by
  rfl

/--
@isnad1 id=eq.1h6v.s8.59e644b74e5a from=translated src=- shape=d986b1c5 vocab=0abc2d58
-/
lemma rwTargetPt_eq
    (n : ℕ) {X Y : TopCat.{u}} (x₀ : X) {f g : X ⟶ Y} (gf : g = f) :
    rwTargetPt n x₀ gf = inducedPointedHom' n x₀ f := by
  simp_all

end inducedPointedHom'

/--
@isnad1 id=isiso.1h5v.s7.025bac11bbfa from=translated src=- shape=27018044 vocab=27799cf1
-/
lemma isIso_inducedPointedHom_of_isHomeomorph (n : ℕ) (x₀ : X) (f : C(X, Y))
    (hf : IsHomeomorph f) : IsIso (inducedPointedHom n x₀ f) := by
  unfold inducedPointedHom
  have : IsIso (PointedTopCat.ofHom f x₀) := PointedTopCat.isIso_of_isHomeomorph f _ hf
  exact Functor.map_isIso (functorToPointed n) (PointedTopCat.ofHom f x₀)

/--
@isnad1 id=eq.0h7v.s8.7d37cc62e61f from=translated src=- shape=eac62c9e vocab=479aace5
-/
lemma inducedPointedHom_comp (n : ℕ) (x₀ : X) (f : C(X, Y)) (g : C(Y, Z)) :
    inducedPointedHom n x₀ (g.comp f) =
    inducedPointedHom n x₀ f ≫ inducedPointedHom n (f x₀) g := by
  unfold inducedPointedHom
  rw [PointedTopCat.ofHom_comp]
  exact (functorToPointed n).map_comp _ _

/--
@isnad1 id=eq.1h8v.s9.eb7c404b7761 from=translated src=- shape=09ea2c91 vocab=768dce19
-/
lemma inducedPointedHom_comp_isoTarget_eq_comp (n : ℕ) (x₀ : X)
    {h : C(X, Z)} {f : C(X, Y)} {g : C(Y, Z)} (hgf : h = g.comp f) :
    inducedPointedHom n x₀ h ≫ (inducedPointedHom.isoTarget n x₀ hgf).hom =
    inducedPointedHom n x₀ f ≫ inducedPointedHom n (f x₀) g := by
  rw [← inducedPointedHom_comp]
  subst hgf
  simp only [ContinuousMap.comp_apply, Iso.refl_hom, Category.comp_id]

/--
@isnad1 id=eq.1h8v.s8.88feeba7f7d4 from=translated src=- shape=7e39e64f vocab=113b1f13
-/
lemma inducedPointedHom_eq_comp_of_eq_comp (n : ℕ) (x₀ : X)
    {h : C(X, Z)} {f : C(X, Y)} {g : C(Y, Z)} (hgf : h = g.comp f) :
    inducedPointedHom.rwTargetPt n x₀ hgf =
    inducedPointedHom n x₀ f ≫ inducedPointedHom n (f x₀) g := by
  rw [inducedPointedHom.rwTargetPt_eq, inducedPointedHom_comp]

/--
@isnad1 id=eq.0h7v.s10.a5da02cf37bc from=translated src=- shape=42ac9b5d vocab=4262a7b4
-/
lemma inducedPointedHom'_comp (n : ℕ) {X Y Z : TopCat.{u}} (x₀ : X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    inducedPointedHom' n x₀ (f ≫ g) =
    inducedPointedHom' n x₀ f ≫ inducedPointedHom' n (f x₀) g := by
  unfold inducedPointedHom'
  rw [PointedTopCat.ofHom'_comp]
  exact (functorToPointed n).map_comp _ _

/--
@isnad1 id=eq.1h8v.s11.525994983356 from=translated src=- shape=334d7338 vocab=59b0082a
-/
lemma inducedPointedHom'_comp_isoTarget_eq_comp (n : ℕ) {X Y Z : TopCat.{u}} (x₀ : X)
    {h : X ⟶ Z} {f : X ⟶ Y} {g : Y ⟶ Z} (hfg : h = f ≫ g) :
    inducedPointedHom' n x₀ h ≫ (inducedPointedHom'.isoTarget n x₀ hfg).hom =
    inducedPointedHom' n x₀ f ≫ inducedPointedHom' n (f x₀) g := by
  rw [← inducedPointedHom'_comp]
  subst hfg
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply, Iso.refl_hom, Category.comp_id]

/--
@isnad1 id=eq.1h8v.s10.2291497b1f38 from=translated src=- shape=1487ff76 vocab=85ae8826
-/
lemma inducedPointedHom'_eq_comp_of_eq_comp (n : ℕ) {X Y Z : TopCat.{u}} (x₀ : X)
    {h : X ⟶ Z} {f : X ⟶ Y} {g : Y ⟶ Z} (hfg : h = f ≫ g) :
    inducedPointedHom'.rwTargetPt n x₀ hfg =
    inducedPointedHom' n x₀ f ≫ inducedPointedHom' n (f x₀) g := by
  rw [inducedPointedHom'.rwTargetPt_eq, inducedPointedHom'_comp]

end HomotopyGroup
