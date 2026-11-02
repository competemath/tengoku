/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.PrincipalPullbackKernel
import Tengoku.Seed.AlgebraicGeometry.Pullbacks
import Tengoku.Seed.RingTheory.TensorProduct.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base change of affine principal closed immersions

The fibred product of `Spec S → Spec R` with the principal closed immersion
`Spec(R/(a)) → Spec R` is identified with `Spec(S/(φ(a)))`.  Under this identification the first
projection is the principal quotient map.  We then transport the quotient-chart equation to the
actual first-projection target stalk and prove directly that it generates the stalk-map kernel.

This closes the affine base-change step needed to apply the principal-divisor/local-length formula
to pullback projections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open TensorProduct Algebra.TensorProduct

universe u

namespace AlgebraicGeometry.Chow

/-- The canonical map carrying an ambient stalk at the image of the second pullback projection
to the target stalk of the first projection.  The pullback condition supplies the necessary
transport between the two descriptions of the ambient point.-/
noncomputable def pullbackBaseChangeStalkMap
    {X Z Y : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    (z : (pullback f i : Scheme.{u})) :
    Y.presheaf.stalk (i (pullback.snd f i z)) ⟶
      X.presheaf.stalk (pullback.fst f i z) :=
  (Y.presheaf.stalkCongr (.of_eq (by
    change (pullback.snd f i ≫ i) z = (pullback.fst f i ≫ f) z
    rw [pullback.condition]))).hom ≫
      f.stalkMap (pullback.fst f i z)

/-- A stalk element on the original ambient scheme, transported canonically to the target stalk
of the base-changed closed immersion.-/
noncomputable def pullbackBaseChangeStalkElement
    {X Z Y : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    (z : (pullback f i : Scheme.{u}))
    (a : Y.presheaf.stalk (i (pullback.snd f i z))) :
    X.presheaf.stalk (pullback.fst f i z) :=
  (pullbackBaseChangeStalkMap f i z).hom a

/-- Second-projection version of `pullbackBaseChangeStalkMap`: it carries an ambient stalk at
the image of the first factor to the target stalk of the second projection.-/
noncomputable def pullbackBaseChangeSndStalkMap
    {Z X Y : Scheme.{u}} (i : Z ⟶ Y) (f : X ⟶ Y)
    (z : (pullback i f : Scheme.{u})) :
    Y.presheaf.stalk (i (pullback.fst i f z)) ⟶
      X.presheaf.stalk (pullback.snd i f z) :=
  (Y.presheaf.stalkCongr (.of_eq (by
    change (pullback.fst i f ≫ i) z = (pullback.snd i f ≫ f) z
    rw [pullback.condition]))).hom ≫
      f.stalkMap (pullback.snd i f z)

/-- An original ambient stalk element transported to the target stalk of the second pullback
projection.-/
noncomputable def pullbackBaseChangeSndStalkElement
    {Z X Y : Scheme.{u}} (i : Z ⟶ Y) (f : X ⟶ Y)
    (z : (pullback i f : Scheme.{u}))
    (a : Y.presheaf.stalk (i (pullback.fst i f z))) :
    X.presheaf.stalk (pullback.snd i f z) :=
  (pullbackBaseChangeSndStalkMap i f z).hom a

/-- Base change of the principal quotient `R/(a)` along `R → S`: the tensor product is the
principal quotient of `S` by the image of `a`.-/
noncomputable def principalBaseChangeAlgEquiv
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    (S ⧸ Ideal.span {algebraMap R S a}) ≃ₐ[S]
      S ⊗[R] (R ⧸ Ideal.span {a}) :=
  (Ideal.quotientEquivAlgOfEq S (by
    rw [Ideal.map_span, Set.image_singleton])).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (Ideal.span {a}))

/-- The affine fibred product with `Spec(R/(a))` is `Spec(S/(φ(a)))`.-/
noncomputable def principalPullbackSpecIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) ≅
        Spec (.of (S ⧸ Ideal.span {algebraMap R S a})) :=
  pullbackSpecIso R S (R ⧸ Ideal.span {a}) ≪≫
    Scheme.Spec.mapIso
      (principalBaseChangeAlgEquiv R S a).toRingEquiv.toCommRingCatIso.op

/-- Under `principalPullbackSpecIso`, the first pullback projection is the quotient map by the
base-changed equation, stated using the inverse of the isomorphism.-/
@[reassoc]
theorem principalPullbackSpecIso_inv_fst
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    (principalPullbackSpecIso R S a).inv ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {algebraMap R S a}))) := by
  rw [principalPullbackSpecIso, Iso.trans_inv, Category.assoc,
    pullbackSpecIso_inv_fst]
  simp only [Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op]
  rw [← Spec.map_comp]
  congr 1
  ext s
  change (principalBaseChangeAlgEquiv R S a).symm (s ⊗ₜ[R] 1) =
    Ideal.Quotient.mk (Ideal.span {algebraMap R S a}) s
  simp only [principalBaseChangeAlgEquiv]
  change (Ideal.quotientEquivAlgOfEq S (by
    rw [Ideal.map_span, Set.image_singleton]))
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
      (Ideal.span {a})).symm (s ⊗ₜ[R] 1)) = _
  rw [show (1 : R ⧸ Ideal.span {a}) =
    Ideal.Quotient.mk (Ideal.span {a}) 1 by rfl]
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  simp

/-- Under `principalPullbackSpecIso`, the first pullback projection is the quotient map by the
base-changed equation, stated using the forward isomorphism.-/
@[reassoc (attr := simp)]
theorem principalPullbackSpecIso_hom_fst
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    (principalPullbackSpecIso R S a).hom ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {algebraMap R S a}))) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) := by
  rw [← principalPullbackSpecIso_inv_fst, Iso.hom_inv_id_assoc]

/-- Precomposing a scheme morphism by an isomorphism does not change the kernel of its stalk map.-/
theorem ker_stalkMap_comp_of_isIso
    {Z Y X : Scheme.{u}} (f : Z ⟶ Y) [IsIso f] (g : Y ⟶ X) (z : Z) :
    RingHom.ker ((f ≫ g).stalkMap z).hom =
      RingHom.ker (g.stalkMap (f z)).hom := by
  rw [Scheme.Hom.stalkMap_comp]
  change RingHom.ker ((f.stalkMap z).hom.comp
    (g.stalkMap (f z)).hom) = _
  exact RingHom.ker_comp_of_injective _
    (asIso (f.stalkMap z)).commRingCatIsoToRingEquiv.injective

/-- In the quotient chart for the principal pullback, the first projection's stalk kernel is
generated by the base-changed equation.-/
theorem ker_stalkMap_principalPullbackSpecIso_hom_comp
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (a : R)
    (z : (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) : Scheme.{u})) :
    RingHom.ker (((principalPullbackSpecIso R S a).hom ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {algebraMap R S a})))).stalkMap z).hom =
      Ideal.span {principalQuotientStalkElement (algebraMap R S a)
        ((principalPullbackSpecIso R S a).hom z)} := by
  rw [ker_stalkMap_comp_of_isIso]
  exact ker_stalkMap_Spec_quotient_span_singleton _ _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism between the target stalks obtained from equality of the actual
first projection and its principal-quotient chart presentation.-/
noncomputable def principalPullbackStalkIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (a : R)
    (z : (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) : Scheme.{u})) :
    (Spec (.of S)).presheaf.stalk
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) z) ≅
      (Spec (.of S)).presheaf.stalk
        (((principalPullbackSpecIso R S a).hom ≫
          Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (Ideal.span {algebraMap R S a})))) z) :=
  (Spec (.of S)).presheaf.stalkCongr (.of_eq (by
    rw [principalPullbackSpecIso_hom_fst]))

/-- The equation defining the affine principal pullback, transported from the quotient chart to
the actual first-projection target stalk.-/
noncomputable def principalPullbackStalkElement
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (a : R)
    (z : (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) : Scheme.{u})) :
    (Spec (.of S)).presheaf.stalk
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) z) :=
  (principalPullbackStalkIso R S a z).inv
    (principalQuotientStalkElement (algebraMap R S a)
      ((principalPullbackSpecIso R S a).hom z))

set_option backward.isDefEq.respectTransparency false in
/-- The stalk kernel of the actual first projection in an affine principal pullback is generated
by the transported base-changed equation.-/
theorem ker_stalkMap_pullback_fst_principal
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (a : R)
    (z : (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) : Scheme.{u})) :
    RingHom.ker ((pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {a}))))).stalkMap z).hom =
      Ideal.span {principalPullbackStalkElement R S a z} := by
  let f := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))
  let g := (principalPullbackSpecIso R S a).hom ≫
    Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {algebraMap R S a})))
  have hfg : f = g := (principalPullbackSpecIso_hom_fst R S a).symm
  rw [Scheme.Hom.stalkMap_congr_hom f g hfg]
  change RingHom.ker ((g.stalkMap z).hom.comp
    (principalPullbackStalkIso R S a z).hom.hom) = _
  rw [← RingHom.comap_ker]
  rw [ker_stalkMap_principalPullbackSpecIso_hom_comp]
  let e := (principalPullbackStalkIso R S a z).commRingCatIsoToRingEquiv
  change (Ideal.span {principalQuotientStalkElement (algebraMap R S a)
    ((principalPullbackSpecIso R S a).hom z)}).comap e.toRingHom =
      Ideal.span {e.symm (principalQuotientStalkElement (algebraMap R S a)
        ((principalPullbackSpecIso R S a).hom z))}
  calc
    _ = (Ideal.span {principalQuotientStalkElement (algebraMap R S a)
      ((principalPullbackSpecIso R S a).hom z)}).map e.symm := by
        exact (Ideal.map_symm e).symm
    _ = _ := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl

/-- If the base-changed equation is nonzero in a domain, its transport to the actual first-
projection target stalk is nonzero.-/
theorem principalPullbackStalkElement_ne_zero
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsDomain S]
    (a : R) (ha : algebraMap R S a ≠ 0)
    (z : (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) : Scheme.{u})) :
    principalPullbackStalkElement R S a z ≠ 0 := by
  exact (map_ne_zero_iff _
    (principalPullbackStalkIso R S a z).symm.commRingCatIsoToRingEquiv.injective).mpr
      (principalQuotientStalkElement_ne_zero (algebraMap R S a) ha
        ((principalPullbackSpecIso R S a).hom z))

end AlgebraicGeometry.Chow
