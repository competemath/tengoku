/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.PrincipalKernelTransport
import Tengoku.Seed.AlgebraicGeometry.Morphisms.OpenImmersion
import Tengoku.Seed.AlgebraicGeometry.PullbackCarrier

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Principal closed immersions on open affine charts

An open base change of a scheme morphism has the same stalk map as the original morphism at a
point lying over the open set, up to the canonical stalk isomorphisms.  We use this fact twice:

* first to transport a principal kernel from an open pullback back to the original morphism;
* then to package an affine presentation of that open pullback by `Spec(R/(a)) → Spec R`.

Thus an honest affine principal chart supplies the principal-kernel hypothesis required by the
local length formula; callers no longer need to postulate that stalk kernel separately.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Chow

/-- A generator of the stalk kernel on an open pullback, transported back to the target stalk of
the original morphism.-/
noncomputable def principalOpenPullbackStalkElement
    {Z X U : Scheme.{u}} (i : Z ⟶ X) (t : U ⟶ X) [IsOpenImmersion t]
    (w : (pullback i t : Scheme.{u}))
    (a : U.presheaf.stalk (pullback.snd i t w)) :
    X.presheaf.stalk (i (pullback.fst i t w)) :=
  principalStalkElementOfIsIsoSquare i (pullback.snd i t)
    (pullback.fst i t) t pullback.condition w a

/-- A principal stalk kernel after restriction to an open subscheme gives a principal kernel for
the original morphism at the underlying point.-/
theorem ker_stalkMap_eq_span_of_openPullback
    {Z X U : Scheme.{u}} (i : Z ⟶ X) (t : U ⟶ X) [IsOpenImmersion t]
    (w : (pullback i t : Scheme.{u}))
    (a : U.presheaf.stalk (pullback.snd i t w))
    (hker : RingHom.ker ((pullback.snd i t).stalkMap w).hom = Ideal.span {a}) :
    RingHom.ker (i.stalkMap (pullback.fst i t w)).hom =
      Ideal.span {principalOpenPullbackStalkElement i t w a} := by
  exact ker_stalkMap_eq_span_of_isIso_square i (pullback.snd i t)
    (pullback.fst i t) t pullback.condition w a hker

/-- An affine principal presentation of the pullback of `i` to an open subscheme `U → X`.
The source and target isomorphisms form an isomorphism of arrows from the restricted morphism to
the standard quotient morphism `Spec(R/(a)) → Spec R`.-/
structure PrincipalOpenPullbackChart
    {Z X U : Scheme.{u}} (i : Z ⟶ X) (t : U ⟶ X) [IsOpenImmersion t] where
  /-- Coordinate ring of the affine open chart.-/
  R : Type u
  /-- The coordinate ring is commutative.-/
  [commRing_R : CommRing R]
  /-- Equation cutting out the restricted closed subscheme.-/
  equation : R
  /-- Identification of the restricted source with the principal quotient spectrum.-/
  sourceIso : pullback i t ≅ Spec (.of (R ⧸ Ideal.span {equation}))
  /-- Identification of the open target with the affine spectrum.-/
  targetIso : U ≅ Spec (.of R)
  /-- Compatibility of the two identifications with the restricted morphism.-/
  commutes : sourceIso.hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {equation}))) =
    pullback.snd i t ≫ targetIso.hom

attribute [instance] PrincipalOpenPullbackChart.commRing_R

namespace PrincipalOpenPullbackChart

variable {Z X U : Scheme.{u}} {i : Z ⟶ X} {t : U ⟶ X} [IsOpenImmersion t]

/-- Transport a principal open-pullback chart across an isomorphism of the closed source.-/
noncomputable def ofSourceIso
    {Z' : Scheme.{u}} {j : Z' ⟶ X} (e : Z ≅ Z') (h : e.hom ≫ j = i)
    (c : PrincipalOpenPullbackChart j t) : PrincipalOpenPullbackChart i t := by
  let m : pullback i t ⟶ pullback j t :=
    pullback.map i t j t e.hom (𝟙 U) (𝟙 X) (by simpa using h.symm) (by simp)
  letI : IsIso m := inferInstance
  exact
    { R := c.R
      equation := c.equation
      sourceIso := asIso m ≪≫ c.sourceIso
      targetIso := c.targetIso
      commutes := by
        change (m ≫ c.sourceIso.hom) ≫ _ = _
        rw [Category.assoc, c.commutes]
        simp only [m, pullback.map, pullback.lift_snd_assoc, Category.comp_id] }

/-- The generator in the target stalk of the restricted morphism, transported from the standard
principal quotient chart.-/
noncomputable def localStalkElement (c : PrincipalOpenPullbackChart i t)
    (w : (pullback i t : Scheme.{u})) :
    U.presheaf.stalk (pullback.snd i t w) :=
  principalStalkElementOfArrowIso (pullback.snd i t)
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {c.equation}))))
    c.sourceIso c.targetIso c.commutes w
    (principalQuotientStalkElement c.equation (c.sourceIso.hom w))

/-- The restricted morphism has the principal stalk kernel supplied by its affine quotient
presentation.-/
theorem ker_stalkMap_openPullback (c : PrincipalOpenPullbackChart i t)
    (w : (pullback i t : Scheme.{u})) :
    RingHom.ker ((pullback.snd i t).stalkMap w).hom =
      Ideal.span {c.localStalkElement w} := by
  exact ker_stalkMap_eq_span_of_arrow_iso (pullback.snd i t)
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {c.equation}))))
    c.sourceIso c.targetIso c.commutes w
    (principalQuotientStalkElement c.equation (c.sourceIso.hom w))
    (ker_stalkMap_Spec_quotient_span_singleton c.equation (c.sourceIso.hom w))

/-- The chart equation transported all the way to the target stalk of the original morphism.-/
noncomputable def stalkElement (c : PrincipalOpenPullbackChart i t)
    (w : (pullback i t : Scheme.{u})) :
    X.presheaf.stalk (i (pullback.fst i t w)) :=
  principalOpenPullbackStalkElement i t w (c.localStalkElement w)

namespace OpenIntersectionRestriction

variable {Y : Scheme.{u}} (j : Y ⟶ X)

/-- Restrict both factors of an intersection to the same open target and map the resulting
intersection back to the original fiber product.-/
noncomputable def map :
    pullback (pullback.snd i t) (pullback.snd j t) ⟶ pullback i j :=
  pullback.map (pullback.snd i t) (pullback.snd j t) i j
    (pullback.fst i t) (pullback.fst j t) t
    (pullback.condition (f := i) (g := t)).symm
    (pullback.condition (f := j) (g := t)).symm

instance : IsOpenImmersion (map (i := i) (t := t) j) := by
  dsimp only [map]
  infer_instance

/-- The restriction map commutes with the projections to the first closed factor.-/
@[reassoc (attr := simp)]
theorem map_fst :
    map (i := i) (t := t) j ≫ pullback.fst i j =
      pullback.fst (pullback.snd i t) (pullback.snd j t) ≫
        pullback.fst i t := by
  change pullback.lift _ _ _ ≫ pullback.fst i j = _
  rw [pullback.lift_fst]

/-- The restriction map commutes with the projections to the second closed factor.-/
@[reassoc (attr := simp)]
theorem map_snd :
    map (i := i) (t := t) j ≫ pullback.snd i j =
      pullback.snd (pullback.snd i t) (pullback.snd j t) ≫
        pullback.fst j t := by
  change pullback.lift _ _ _ ≫ pullback.snd i j = _
  rw [pullback.lift_snd]

/-- An original intersection point whose ambient image lies in the chosen open target has a
preimage in the intersection obtained by restricting both factors to that open.-/
theorem exists_preimage (z : (pullback i j : Scheme.{u})) (u : U)
    (h : i (pullback.fst i j z) = t u) :
    ∃ w : (pullback (pullback.snd i t) (pullback.snd j t) : Scheme.{u}),
      map (i := i) (t := t) j w = z := by
  have hij : i (pullback.fst i j z) = j (pullback.snd i j z) := by
    change (pullback.fst i j ≫ i) z = (pullback.snd i j ≫ j) z
    rw [pullback.condition]
  have hleft : pullback.fst i j z ∈ Set.range (pullback.fst i t) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨u, h.symm⟩
  have hright : pullback.snd i j z ∈ Set.range (pullback.fst j t) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨u, (hij.symm.trans h).symm⟩
  change z ∈ Set.range (pullback.map
    (pullback.snd i t) (pullback.snd j t) i j
    (pullback.fst i t) (pullback.fst j t) t
    (pullback.condition (f := i) (g := t)).symm
    (pullback.condition (f := j) (g := t)).symm)
  rw [Scheme.Pullback.range_map]
  exact ⟨hleft, hright⟩

/-- A chosen lift of an original intersection point to the intersection over an open target.-/
structure At (z : (pullback i j : Scheme.{u})) where
  /-- Point of the restricted intersection.-/
  point : (pullback (pullback.snd i t) (pullback.snd j t) : Scheme.{u})
  /-- The restricted point maps to the specified original point.-/
  map_point : map (i := i) (t := t) j point = z

namespace At

/-- Choose the lift supplied by an ambient point of the open target.-/
noncomputable def ofPoint (z : (pullback i j : Scheme.{u})) (u : U)
    (h : i (pullback.fst i j z) = t u) : At (i := i) (t := t) j z :=
  ⟨Classical.choose (exists_preimage (i := i) (t := t) j z u h),
    Classical.choose_spec (exists_preimage (i := i) (t := t) j z u h)⟩

end At

/-- A principal kernel for the second projection after restricting both factors to an open
target transports back to the original intersection stalk.-/
theorem ker_stalkMap_snd_eq_span_of_restriction
    (w : (pullback (pullback.snd i t) (pullback.snd j t) : Scheme.{u}))
    (a : (pullback j t).presheaf.stalk
      (pullback.snd (pullback.snd i t) (pullback.snd j t) w))
    (hker : RingHom.ker
      ((pullback.snd (pullback.snd i t) (pullback.snd j t)).stalkMap w).hom =
        Ideal.span {a}) :
    RingHom.ker ((pullback.snd i j).stalkMap
      (map (i := i) (t := t) j w)).hom =
      Ideal.span {
        principalStalkElementOfIsIsoSquare
          (pullback.snd i j)
          (pullback.snd (pullback.snd i t) (pullback.snd j t))
          (map (i := i) (t := t) j) (pullback.fst j t)
          (map_snd (i := i) (t := t) j) w a} := by
  exact ker_stalkMap_eq_span_of_isIso_square
    (pullback.snd i j)
    (pullback.snd (pullback.snd i t) (pullback.snd j t))
    (map (i := i) (t := t) j) (pullback.fst j t)
    (map_snd (i := i) (t := t) j) w a hker

namespace At

/-- The first closed-factor point of a restricted lift maps to the first coordinate of the
selected original intersection point.-/
theorem left_point {z : (pullback i j : Scheme.{u})}
    (d : At (i := i) (t := t) j z) :
    pullback.fst i t
        (pullback.fst (pullback.snd i t) (pullback.snd j t) d.point) =
      pullback.fst i j z := by
  calc
    pullback.fst i t
        (pullback.fst (pullback.snd i t) (pullback.snd j t) d.point) =
        pullback.fst i j (map (i := i) (t := t) j d.point) := by
      change (pullback.fst (pullback.snd i t) (pullback.snd j t) ≫
          pullback.fst i t) d.point =
        (map (i := i) (t := t) j ≫ pullback.fst i j) d.point
      rw [map_fst]
    _ = pullback.fst i j z := congrArg (pullback.fst i j) d.map_point

/-- The second closed-factor point of a restricted lift maps to the second coordinate of the
selected original intersection point.-/
theorem right_point {z : (pullback i j : Scheme.{u})}
    (d : At (i := i) (t := t) j z) :
    pullback.fst j t
        (pullback.snd (pullback.snd i t) (pullback.snd j t) d.point) =
      pullback.snd i j z := by
  calc
    pullback.fst j t
        (pullback.snd (pullback.snd i t) (pullback.snd j t) d.point) =
        pullback.snd i j (map (i := i) (t := t) j d.point) := by
      change (pullback.snd (pullback.snd i t) (pullback.snd j t) ≫
          pullback.fst j t) d.point =
        (map (i := i) (t := t) j ≫ pullback.snd i j) d.point
      rw [map_snd]
    _ = pullback.snd i j z := congrArg (pullback.snd i j) d.map_point

/-- Transport an equation on the common open target first to the original ambient stalk along
the left closed-factor square and then to the literal first coordinate of the selected global
intersection point.-/
noncomputable def ambientStalkElement {z : (pullback i j : Scheme.{u})}
    (d : At (i := i) (t := t) j z)
    (a : U.presheaf.stalk
      (pullback.snd i t
        (pullback.fst (pullback.snd i t) (pullback.snd j t) d.point))) :
    X.presheaf.stalk (i (pullback.fst i j z)) :=
  (X.presheaf.stalkCongr (.of_eq (congrArg i (left_point (i := i) (t := t) j d)))).hom
    (principalStalkElementOfIsIsoSquare i (pullback.snd i t)
      (pullback.fst i t) t pullback.condition
      (pullback.fst (pullback.snd i t) (pullback.snd j t) d.point) a)

set_option backward.isDefEq.respectTransparency false in
/-- At a point of the intersection over a common open target, pulling an open-target equation
back to the ambient stalk through the left or the right closed-factor square gives the same
element after the canonical point transport.-/
theorem principalStalkElement_commonTarget
    (w : (pullback (pullback.snd i t) (pullback.snd j t) : Scheme.{u}))
    (a : U.presheaf.stalk
      (pullback.snd i t
        (pullback.fst (pullback.snd i t) (pullback.snd j t) w))) :
    principalStalkElementOfIsIsoSquare j (pullback.snd j t)
        (pullback.fst j t) t pullback.condition
        (pullback.snd (pullback.snd i t) (pullback.snd j t) w)
        ((U.presheaf.stalkCongr (.of_eq (by
          change (pullback.fst (pullback.snd i t) (pullback.snd j t) ≫
              pullback.snd i t) w =
            (pullback.snd (pullback.snd i t) (pullback.snd j t) ≫
              pullback.snd j t) w
          rw [pullback.condition]))).hom a) =
      (X.presheaf.stalkCongr (.of_eq (by
        calc
          i (pullback.fst i t
              (pullback.fst (pullback.snd i t) (pullback.snd j t) w)) =
              t (pullback.snd i t
                (pullback.fst (pullback.snd i t) (pullback.snd j t) w)) := by
            change (pullback.fst i t ≫ i)
                (pullback.fst (pullback.snd i t) (pullback.snd j t) w) =
              (pullback.snd i t ≫ t)
                (pullback.fst (pullback.snd i t) (pullback.snd j t) w)
            rw [pullback.condition]
          _ = t (pullback.snd j t
                (pullback.snd (pullback.snd i t) (pullback.snd j t) w)) := by
            congr 1
            change (pullback.fst (pullback.snd i t) (pullback.snd j t) ≫
                pullback.snd i t) w =
              (pullback.snd (pullback.snd i t) (pullback.snd j t) ≫
                pullback.snd j t) w
            rw [pullback.condition]
          _ = j (pullback.fst j t
                (pullback.snd (pullback.snd i t) (pullback.snd j t) w)) := by
            change (pullback.snd j t ≫ t)
                (pullback.snd (pullback.snd i t) (pullback.snd j t) w) =
              (pullback.fst j t ≫ j)
                (pullback.snd (pullback.snd i t) (pullback.snd j t) w)
            rw [pullback.condition]))).hom
        (principalStalkElementOfIsIsoSquare i (pullback.snd i t)
          (pullback.fst i t) t pullback.condition
          (pullback.fst (pullback.snd i t) (pullback.snd j t) w) a) := by
  let wL := pullback.fst (pullback.snd i t) (pullback.snd j t) w
  let wR := pullback.snd (pullback.snd i t) (pullback.snd j t) w
  let uL := pullback.snd i t wL
  let uR := pullback.snd j t wR
  have hU : uL = uR := by
    change (pullback.fst (pullback.snd i t) (pullback.snd j t) ≫
        pullback.snd i t) w =
      (pullback.snd (pullback.snd i t) (pullback.snd j t) ≫
        pullback.snd j t) w
    rw [pullback.condition]
  have hI : i (pullback.fst i t wL) = t uL := by
    change (pullback.fst i t ≫ i) wL = (pullback.snd i t ≫ t) wL
    rw [pullback.condition]
  have hJ : j (pullback.fst j t wR) = t uR := by
    change (pullback.fst j t ≫ j) wR = (pullback.snd j t ≫ t) wR
    rw [pullback.condition]
  have hLocal : i (pullback.fst i t wL) = j (pullback.fst j t wR) :=
    hI.trans ((congrArg t hU).trans hJ.symm)
  let hDirect : t uL = j (pullback.fst j t wR) :=
    (congrArg t hU).trans hJ.symm
  have hnat := stalkMap_inv_naturality_of_point_eq t hU a
  simp [principalStalkElementOfIsIsoSquare, targetStalkIsoOfIsIsoSquare,
    wL, wR, uL, uR]
  change (X.presheaf.stalkCongr (.of_eq hJ.symm)).hom
      ((inv (t.stalkMap uR)).hom
        ((U.presheaf.stalkCongr (.of_eq hU)).hom a)) =
    (X.presheaf.stalkCongr (.of_eq hDirect)).hom
      ((inv (t.stalkMap uL)).hom a)
  change (inv (t.stalkMap uR)).hom
      ((U.presheaf.stalkCongr (.of_eq hU)).hom a) = _ at hnat
  rw [hnat]
  let b := (inv (t.stalkMap uL)).hom a
  simpa [b, hDirect] using stalkCongr_comp_apply_of_eq X
    (congrArg t hU) rfl hJ.symm hDirect b

/-- Transport a restricted second-projection generator to the literal target stalk at the
specified original intersection point.-/
noncomputable def stalkElement {z : (pullback i j : Scheme.{u})}
    (d : At (i := i) (t := t) j z)
    (a : (pullback j t).presheaf.stalk
      (pullback.snd (pullback.snd i t) (pullback.snd j t) d.point)) :
    Y.presheaf.stalk (pullback.snd i j z) :=
  (Y.presheaf.stalkCongr
    (.of_eq (congrArg (pullback.snd i j) d.map_point))).hom
      (principalStalkElementOfIsIsoSquare
        (pullback.snd i j)
        (pullback.snd (pullback.snd i t) (pullback.snd j t))
        (map (i := i) (t := t) j) (pullback.fst j t)
        (map_snd (i := i) (t := t) j) d.point a)

end At

end OpenIntersectionRestriction

namespace OpenRightRestriction

variable {A B S V : Scheme.{u}} (f : A ⟶ S) (g : B ⟶ S)
  (v : V ⟶ B) [IsOpenImmersion v]

/-- Restrict only the right factor of a fiber product to an open subscheme.-/
noncomputable def map : pullback f (v ≫ g) ⟶ pullback f g :=
  pullback.map f (v ≫ g) f g (𝟙 A) v (𝟙 S) (by simp) (by simp)

instance : IsOpenImmersion (map f g v) := by
  dsimp only [map]
  infer_instance

/-- The right-factor restriction map fixes the first projection.-/
@[reassoc (attr := simp)]
theorem map_fst : map f g v ≫ pullback.fst f g = pullback.fst f (v ≫ g) := by
  change pullback.lift _ _ _ ≫ pullback.fst f g = _
  rw [pullback.lift_fst, Category.comp_id]

/-- The right-factor restriction map composes the restricted second projection with the open
immersion into the original right factor.-/
@[reassoc (attr := simp)]
theorem map_snd :
    map f g v ≫ pullback.snd f g = pullback.snd f (v ≫ g) ≫ v := by
  change pullback.lift _ _ _ ≫ pullback.snd f g = _
  rw [pullback.lift_snd]

/-- If the right coordinate of a fiber-product point lies in the selected open subscheme, the
point lifts to the right-restricted fiber product.-/
theorem exists_preimage (z : (pullback f g : Scheme.{u})) (y : V)
    (h : v y = pullback.snd f g z) :
    ∃ w : (pullback f (v ≫ g) : Scheme.{u}), map f g v w = z := by
  have hleft : pullback.fst f g z ∈ Set.range (𝟙 A : A ⟶ A) :=
    ⟨pullback.fst f g z, rfl⟩
  have hright : pullback.snd f g z ∈ Set.range v := ⟨y, h⟩
  change z ∈ Set.range (pullback.map f (v ≫ g) f g
    (𝟙 A) v (𝟙 S) (by simp) (by simp))
  rw [Scheme.Pullback.range_map]
  exact ⟨hleft, hright⟩

/-- A chosen lift to a fiber product after restricting its right factor.-/
structure At (z : (pullback f g : Scheme.{u})) where
  /-- Point of the right-restricted fiber product.-/
  point : (pullback f (v ≫ g) : Scheme.{u})
  /-- Its image is the specified original point.-/
  map_point : map f g v point = z

namespace At

/-- Choose the right-restricted lift supplied by a point above the original right coordinate.-/
noncomputable def ofPoint (z : (pullback f g : Scheme.{u})) (y : V)
    (h : v y = pullback.snd f g z) : At f g v z :=
  ⟨Classical.choose (exists_preimage f g v z y h),
    Classical.choose_spec (exists_preimage f g v z y h)⟩

end At

/-- A principal kernel for the second projection after an open restriction of the right factor
transports back to the original fiber-product stalk.-/
theorem ker_stalkMap_snd_eq_span_of_restriction
    (w : (pullback f (v ≫ g) : Scheme.{u}))
    (a : V.presheaf.stalk (pullback.snd f (v ≫ g) w))
    (hker : RingHom.ker ((pullback.snd f (v ≫ g)).stalkMap w).hom =
      Ideal.span {a}) :
    RingHom.ker ((pullback.snd f g).stalkMap (map f g v w)).hom =
      Ideal.span {
        principalStalkElementOfIsIsoSquare
          (pullback.snd f g) (pullback.snd f (v ≫ g))
          (map f g v) v (map_snd f g v) w a} := by
  exact ker_stalkMap_eq_span_of_isIso_square
    (pullback.snd f g) (pullback.snd f (v ≫ g))
    (map f g v) v (map_snd f g v) w a hker

namespace At

/-- The first coordinate of a right-restricted lift is the first coordinate of the selected
original fiber-product point.-/
theorem fst_point {z : (pullback f g : Scheme.{u})} (d : At f g v z) :
    pullback.fst f g z = pullback.fst f (v ≫ g) d.point := by
  calc
    pullback.fst f g z = pullback.fst f g (map f g v d.point) :=
      congrArg (pullback.fst f g) d.map_point.symm
    _ = pullback.fst f (v ≫ g) d.point := by
      change (map f g v ≫ pullback.fst f g) d.point = _
      rw [map_fst]

/-- Transport an ambient equation to the first coordinate description used by a
right-restricted lift.-/
noncomputable def ambientStalkElement {z : (pullback f g : Scheme.{u})}
    (d : At f g v z) (a : S.presheaf.stalk (f (pullback.fst f g z))) :
    S.presheaf.stalk (f (pullback.fst f (v ≫ g) d.point)) :=
  (S.presheaf.stalkCongr (.of_eq (congrArg f (fst_point f g v d)))).hom a

/-- Transport a restricted generator to the literal right-factor stalk at the selected original
fiber-product point.-/
noncomputable def stalkElement {z : (pullback f g : Scheme.{u})}
    (d : At f g v z)
    (a : V.presheaf.stalk (pullback.snd f (v ≫ g) d.point)) :
    B.presheaf.stalk (pullback.snd f g z) :=
  (B.presheaf.stalkCongr
    (.of_eq (congrArg (pullback.snd f g) d.map_point))).hom
      (principalStalkElementOfIsIsoSquare
        (pullback.snd f g) (pullback.snd f (v ≫ g))
        (map f g v) v (map_snd f g v) d.point a)

end At

end OpenRightRestriction

/-- A concrete affine open neighbourhood of a specified scheme point.-/
structure AffineNeighbourhoodAt (Y : Scheme.{u}) (y : Y) where
  /-- Coordinate ring of the affine neighbourhood.-/
  R : CommRingCat.{u}
  /-- Open immersion of the affine spectrum into the scheme.-/
  map : Spec R ⟶ Y
  /-- The chosen map is an open immersion.-/
  [isOpenImmersion_map : IsOpenImmersion map]
  /-- Point of the affine spectrum above `y`.-/
  point : Spec R
  /-- The chosen affine point maps to `y`.-/
  map_point : map point = y

attribute [instance] AffineNeighbourhoodAt.isOpenImmersion_map

namespace AffineNeighbourhoodAt

/-- Every scheme point admits a concrete affine open neighbourhood.-/
theorem nonempty (Y : Scheme.{u}) (y : Y) : Nonempty (AffineNeighbourhoodAt Y y) := by
  obtain ⟨R, v, hv, p, hp⟩ := Scheme.exists_Spec_apply_eq y
  exact ⟨{ R := R, map := v, isOpenImmersion_map := hv, point := p, map_point := hp }⟩

/-- Choose an affine open neighbourhood of a scheme point.-/
noncomputable def choose (Y : Scheme.{u}) (y : Y) : AffineNeighbourhoodAt Y y :=
  Classical.choice (nonempty Y y)

/-- An affine neighbourhood of the right coordinate canonically lifts a fiber-product point to
the corresponding right-restricted fiber product.-/
noncomputable def rightRestrictionAt
    {A B S : Scheme.{u}} (f : A ⟶ S) (g : B ⟶ S)
    (z : (pullback f g : Scheme.{u}))
    (d : AffineNeighbourhoodAt B (pullback.snd f g z)) :
    OpenRightRestriction.At f g d.map z :=
  OpenRightRestriction.At.ofPoint f g d.map z d.point d.map_point

end AffineNeighbourhoodAt

/-- An affine chart for a morphism into the target of a principal open-pullback chart.  Together
with the principal chart, this identifies its base change with the universal affine principal
base-change model.-/
structure AffineBaseChange (c : PrincipalOpenPullbackChart i t)
    (V : Scheme.{u}) (g : V ⟶ U) where
  /-- Coordinate ring of the affine base-change source.-/
  S : Type u
  /-- The coordinate ring is commutative.-/
  [commRing_S : CommRing S]
  /-- Coordinate-ring map inducing the morphism to the principal chart target.-/
  [algebra_R_S : Algebra c.R S]
  /-- Identification of the base-change source with its affine spectrum.-/
  targetIso : V ≅ Spec (.of S)
  /-- Compatibility of the affine identifications with the base-change morphism.-/
  commutes : targetIso.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap c.R S)) =
    g ≫ c.targetIso.hom

attribute [instance]
  AffineBaseChange.commRing_S AffineBaseChange.algebra_R_S

namespace AffineBaseChange

variable {V : Scheme.{u}} {g : V ⟶ U} {c : PrincipalOpenPullbackChart i t}

/-- Any chosen affine spectrum presentation of the base-change source canonically determines
the coordinate-ring map and hence the `AffineBaseChange` structure.-/
noncomputable def ofTargetIso
    (c : PrincipalOpenPullbackChart i t) (V : Scheme.{u}) (g : V ⟶ U)
    (S : Type u) [CommRing S] (eV : V ≅ Spec (.of S)) :
    c.AffineBaseChange V g := by
  let φ : c.R →+* S :=
    (Spec.preimage (eV.inv ≫ g ≫ c.targetIso.hom)).hom
  letI : Algebra c.R S := φ.toAlgebra
  exact
    { S := S
      targetIso := eV
      commutes := by
        have hφ :
            Spec.map (CommRingCat.ofHom φ) =
              eV.inv ≫ g ≫ c.targetIso.hom := by
          simpa only [φ, CommRingCat.ofHom_hom] using
            Spec.map_preimage (eV.inv ≫ g ≫ c.targetIso.hom)
        change eV.hom ≫ Spec.map (CommRingCat.ofHom φ) =
          g ≫ c.targetIso.hom
        rw [hφ]
        simp }

/-- In particular, an affine base-change source supplies the required chart automatically via
its canonical spectrum of global sections.-/
noncomputable def ofIsAffine
    (c : PrincipalOpenPullbackChart i t) (V : Scheme.{u}) (g : V ⟶ U)
    [IsAffine V] : c.AffineBaseChange V g :=
  ofTargetIso c V g Γ(V, ⊤) V.isoSpec

/-- A concrete affine neighbourhood in any right factor automatically supplies affine
base-change data for the composite morphism into the principal chart target.-/
noncomputable def ofNeighbourhood
    (c : PrincipalOpenPullbackChart i t) {Y : Scheme.{u}} (g : Y ⟶ U) (y : Y)
    (d : AffineNeighbourhoodAt Y y) :
    c.AffineBaseChange (Spec d.R) (d.map ≫ g) :=
  ofTargetIso c (Spec d.R) (d.map ≫ g) d.R (Iso.refl _)

/-- The base change of the restricted principal morphism is isomorphic to the universal affine
principal pullback.-/
noncomputable def pullbackIso (b : c.AffineBaseChange V g) :
    pullback g (pullback.snd i t) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap c.R b.S)))
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span {c.equation})))) :=
  asIso (pullback.map g (pullback.snd i t)
    (Spec.map (CommRingCat.ofHom (algebraMap c.R b.S)))
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {c.equation}))))
    b.targetIso.hom c.sourceIso.hom c.targetIso.hom
    b.commutes.symm c.commutes.symm)

/-- The pullback isomorphism commutes with the first projections to the two affine targets.-/
@[reassoc (attr := simp)]
theorem pullbackIso_hom_fst (b : c.AffineBaseChange V g) :
    b.pullbackIso.hom ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap c.R b.S)))
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span {c.equation})))) =
    pullback.fst g (pullback.snd i t) ≫ b.targetIso.hom := by
  change pullback.lift _ _ _ ≫ _ = _
  exact pullback.lift_fst _ _ _

/-- The pullback isomorphism commutes with the second projections to the two presentations of
the restricted principal source.-/
@[reassoc (attr := simp)]
theorem pullbackIso_hom_snd (b : c.AffineBaseChange V g) :
    b.pullbackIso.hom ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap c.R b.S)))
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span {c.equation})))) =
    pullback.snd g (pullback.snd i t) ≫ c.sourceIso.hom := by
  change pullback.lift _ _ _ ≫ _ = _
  exact pullback.lift_snd _ _ _

/-- The affine principal pullback equation transported through the base-change chart to the
literal target stalk of the actual first projection.-/
noncomputable def stalkElement (b : c.AffineBaseChange V g)
    (z : (pullback g (pullback.snd i t) : Scheme.{u})) :
    V.presheaf.stalk (pullback.fst g (pullback.snd i t) z) :=
  principalStalkElementOfArrowIso
    (pullback.fst g (pullback.snd i t))
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap c.R b.S)))
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {c.equation})))))
    b.pullbackIso b.targetIso b.pullbackIso_hom_fst z
    (principalPullbackStalkElement c.R b.S c.equation (b.pullbackIso.hom z))

end AffineBaseChange

namespace AffineNeighbourhoodAt

variable {Y : Scheme.{u}} (g : Y ⟶ U) (c : PrincipalOpenPullbackChart i t)

/-- The specified principal generator obtained by choosing an affine neighbourhood of the right
coordinate, applying the affine base-change theorem there, and transporting back through the
right-factor open restriction.-/
noncomputable def principalBaseChangeStalkElement
    (z : (pullback (pullback.snd i t) g : Scheme.{u}))
    (d : AffineNeighbourhoodAt Y
      (pullback.snd (pullback.snd i t) g z)) :
    Y.presheaf.stalk (pullback.snd (pullback.snd i t) g z) :=
  let e := d.rightRestrictionAt (pullback.snd i t) g z
  OpenRightRestriction.At.stalkElement (pullback.snd i t) g d.map e
    (pullbackBaseChangeSndStalkElement
      (pullback.snd i t) (d.map ≫ g) e.point
      (c.localStalkElement
        (pullback.fst (pullback.snd i t) (d.map ≫ g) e.point)))

end AffineNeighbourhoodAt

/-- A principal open-pullback chart together with a chosen point above `z`.  This removes the
nested pullback point from downstream statements while retaining the exact geometric witness
that the chart covers `z`.-/
structure At (c : PrincipalOpenPullbackChart i t) (z : Z) where
  /-- A point of the restricted source above `z`.-/
  point : (pullback i t : Scheme.{u})
  /-- The chosen restricted point lies over `z`.-/
  fst_point : pullback.fst i t point = z

namespace At

/-- A point of the target open lying over `i(z)` canonically supplies a point of the open
pullback above `z`.-/
noncomputable def ofPoint (c : PrincipalOpenPullbackChart i t) (z : Z) (u : U)
    (h : i z = t u) : c.At z :=
  let w := Classical.choose (Scheme.Pullback.exists_preimage_pullback z u h)
  ⟨w, (Classical.choose_spec
    (Scheme.Pullback.exists_preimage_pullback z u h)).1⟩

/-- The chart equation at a chosen restricted point, transported to the literal stalk at `i(z)`
rather than the propositionally equal stalk at the first projection of that point.-/
noncomputable def stalkElement {z : Z} {c : PrincipalOpenPullbackChart i t} (a : c.At z) :
    X.presheaf.stalk (i z) :=
  (X.presheaf.stalkCongr (.of_eq (congrArg i a.fst_point))).hom
    (c.stalkElement a.point)

end At

namespace OpenIntersectionRestriction.At

variable {Y : Scheme.{u}} (j : Y ⟶ X)

/-- The first coordinate of a point lifted to the intersection over a common open target is a
pointed instance of the original principal chart at the literal global first-factor point.-/
noncomputable def leftChartAt {z : (pullback i j : Scheme.{u})}
    (d : OpenIntersectionRestriction.At (i := i) (t := t) j z)
    (c : PrincipalOpenPullbackChart i t) :
    PrincipalOpenPullbackChart.At c (pullback.fst i j z) :=
  ⟨pullback.fst (pullback.snd i t) (pullback.snd j t) d.point,
    OpenIntersectionRestriction.At.left_point (i := i) (t := t) j d⟩

/-- The second coordinate of a point lifted to the intersection over a common open target is a
pointed instance of a principal chart on the original second closed factor.-/
noncomputable def rightChartAt {z : (pullback i j : Scheme.{u})}
    (d : OpenIntersectionRestriction.At (i := i) (t := t) j z)
    (c : PrincipalOpenPullbackChart j t) :
    PrincipalOpenPullbackChart.At c (pullback.snd i j z) :=
  ⟨pullback.snd (pullback.snd i t) (pullback.snd j t) d.point,
    OpenIntersectionRestriction.At.right_point (i := i) (t := t) j d⟩

end OpenIntersectionRestriction.At

end PrincipalOpenPullbackChart

end AlgebraicGeometry.Chow
