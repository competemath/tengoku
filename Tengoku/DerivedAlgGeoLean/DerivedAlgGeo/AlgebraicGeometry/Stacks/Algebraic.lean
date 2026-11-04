/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.AlgebraicGeometry.AffineSpace
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FinitePresentation
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Smooth
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Stacks.Representable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scheme morphisms and big-Zariski stack presentation data

This file starts the algebraicity layer with two pieces of data that retain
their geometric content:

* a scheme morphism induces a pullback-compatible morphism between the
  corresponding representable big-Zariski stacks;
* a property of a representable stack morphism is required on the actual
  structure morphism of every representing scheme.

The presentation structure at the end of this file is deliberately named for
the big Zariski topology.  It is useful geometric data, but it is not the
standard definition of an algebraic stack: no fppf or étale descent theorem is
proved here, and the diagonal is represented by schemes rather than algebraic
spaces.  No Artin representability theorem or opaque algebraicity proposition
is introduced.

The fppf and étale descent level lives in
`DerivedAlgGeo.AlgebraicGeometry.Stacks.Descent`, which also shows that a
smooth surjection is an fppf covering family.  That module does not change
anything here: the diagonal below is still represented by schemes, and the
presentations below are still big-Zariski presentations.

## Which declarations here fix the topology, and which do not

The representability vocabulary -- `StackMorphism.HasRepresentableProperty`
with its `IsLocallyOfFinitePresentation`, `IsSmoothSurjective` and
`IsOpenImmersion` specializations, and
`StackInGroupoids.HasRepresentableDiagonal` with its fiber representation --
says nothing about which covering families the stack condition quantifies
over.  Each is a statement about the *representing scheme morphisms* of a
stack morphism's fibers, so each is stated for an arbitrary Grothendieck
topology `J` on `Scheme` and reads identically at Zariski, étale and fppf.

What genuinely is Zariski is everything named for it: the
`representableZariski*` constructions, whose descent comes from
`Scheme.zariskiTopology` being subcanonical, and `ZariskiStackPresentation`
and `ZariskiStackPresentationOver`, whose names record exactly the gap
between what they supply and an algebraic stack.

The split is deliberate. Raising the presentations to fppf is SF9.2 (#522)
work, and it should not also have to widen the vocabulary it is stated in.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Bicategory
open Opposite

noncomputable section

universe u

/-- A scheme morphism induces the corresponding morphism between
representable big-Zariski stacks by postcomposition on every test scheme.-/
def representableZariskiStackMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    StackMorphism (representableZariskiStack X)
      (representableZariskiStack Y) :=
  StackInGroupoids.representableMap Scheme.zariskiTopology f

/--
@isnad1 id=eq.0h5v.s9.f017ebfda601 from=translated src=- shape=5192433c vocab=9231495c
-/
@[simp]
theorem representableZariskiStackMap_obj {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : T ⟶ X) :
    ((representableZariskiStackMap f).app T).obj
        (representableZariskiObject g) =
      representableZariskiObject (g ≫ f) :=
  rfl

/-- Three scheme-induced stack morphisms compose through Mathlib's strong
transformation composition, with the expected pointwise action.  The
associator and unitors for this composition are the ones supplied by the
pseudofunctor bicategory.
@isnad1 id=eq.0h9v.s9.ae092c7c94fe from=translated src=- shape=b27f8104 vocab=fee72f67
-/
@[simp]
theorem representableZariskiStackMap_tripleComp_obj
    {W X Y Z T : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (x : T ⟶ W) :
    ((((representableZariskiStackMap f).comp
      (representableZariskiStackMap g)).comp
        (representableZariskiStackMap h)).app T).obj
          (representableZariskiObject x) =
      representableZariskiObject (((x ≫ f) ≫ g) ≫ h) :=
  rfl

namespace RepresentableZariskiStackMap

variable {X Y S : Scheme.{u}} (f : X ⟶ Y)
  (y : Discrete (S ⟶ Y))

/-- The ordinary scheme fiber product representing the fiber of a
representable-stack morphism over `y : S ⟶ Y`.-/
def fiberProduct : Over S :=
  Over.mk (pullback.snd f y.as)

private def fiberObject (T : Over S)
    (a : T ⟶ fiberProduct f y) :
    StructuredArrow
      (((representableZariskiStack Y).presheaf.map T.hom.op.toLoc).toFunctor.obj y)
      ((representableZariskiStackMap f).app T.left) :=
  StructuredArrow.mk (Discrete.eqToHom (by
    change T.hom ≫ y.as = (a.left ≫ pullback.fst f y.as) ≫ f
    have ha : a.left ≫ pullback.snd f y.as = T.hom := a.w
    calc
      T.hom ≫ y.as = (a.left ≫ pullback.snd f y.as) ≫ y.as :=
        congrArg (fun k ↦ k ≫ y.as) ha.symm
      _ = a.left ≫ (pullback.snd f y.as ≫ y.as) := Category.assoc ..
      _ = a.left ≫ (pullback.fst f y.as ≫ f) :=
        congrArg (fun k ↦ a.left ≫ k)
          (pullback.condition (f := f) (g := y.as)).symm
      _ = (a.left ≫ pullback.fst f y.as) ≫ f := (Category.assoc ..).symm))

/-- Yoneda's fiber-product comparison as a functor into the actual groupoid
fiber of the induced stack morphism.-/
def fiberFunctor (T : Over S) :
    Discrete (T ⟶ fiberProduct f y) ⥤
      (representableZariskiStackMap f).FiberCategory y T :=
  Core.functorToCore (Discrete.functor (fiberObject f y T))

/--
@isnad1 id=faithful.0h6v.s12.70d88100c905 from=translated src=- shape=32b07dfd vocab=5b59ccfc
-/
instance fiberFunctor_faithful (T : Over S) :
    (fiberFunctor f y T).Faithful where
  map_injective _ := Subsingleton.elim _ _

/--
@isnad1 id=full.0h6v.s12.c150e20eb41d from=translated src=- shape=32b07dfd vocab=ed74cf2e
-/
instance fiberFunctor_full (T : Over S) :
    (fiberFunctor f y T).Full where
  map_surjective {a b} h := by
    have hfst : a.as.left ≫ pullback.fst f y.as =
        b.as.left ≫ pullback.fst f y.as :=
      Discrete.eq_of_hom h.iso.hom.right
    have hsnd : a.as.left ≫ pullback.snd f y.as =
        b.as.left ≫ pullback.snd f y.as :=
      a.as.w.trans b.as.w.symm
    have hab : a.as = b.as := by
      apply CostructuredArrow.hom_ext
      apply pullback.hom_ext
      · exact hfst
      · exact hsnd
    refine ⟨eqToHom (Discrete.ext hab), ?_⟩
    letI : IsDiscrete
        ((representableZariskiStack X).presheaf.obj (.mk (op T.left))) := by
      exact discretePseudofunctor_obj_isDiscrete (yoneda.obj X) _
    apply Core.hom_ext
    apply StructuredArrow.hom_ext
    apply Subsingleton.elim

/--
@isnad1 id=esssurj.0h6v.s12.d3ebff4ac0e6 from=translated src=- shape=32b07dfd vocab=2cae9e58
-/
instance fiberFunctor_essSurj (T : Over S) :
    (fiberFunctor f y T).EssSurj := by
  constructor
  intro z
  let x : T.left ⟶ X := z.of.right.as
  have hxy : T.hom ≫ y.as = x ≫ f :=
    Discrete.eq_of_hom z.of.hom
  let a : T ⟶ fiberProduct f y :=
    Over.homMk (pullback.lift x T.hom hxy.symm)
      (pullback.lift_snd x T.hom hxy.symm)
  refine ⟨Discrete.mk a, ?_⟩
  apply Nonempty.intro
  apply Core.isoMk
  refine StructuredArrow.isoMk (Discrete.eqToIso (by
    change (pullback.lift x T.hom hxy.symm ≫ pullback.fst f y.as) = x
    exact pullback.lift_fst x T.hom hxy.symm)) ?_
  letI : IsDiscrete
      ((representableZariskiStack Y).presheaf.obj (.mk (op T.left))) := by
    exact discretePseudofunctor_obj_isDiscrete (yoneda.obj Y) _
  apply Subsingleton.elim

/-- The fiber of a morphism between representable stacks is represented by
the ordinary scheme fiber product, with its full Yoneda universal property.-/
def fiberRepresentation :
    (representableZariskiStackMap f).FiberRepresentation y where
  representing := fiberProduct f y
  fiberEquivalence T := by
    letI := fiberFunctor_faithful f y T
    letI := fiberFunctor_full f y T
    letI := fiberFunctor_essSurj f y T
    letI : (fiberFunctor f y T).IsEquivalence :=
      ⟨inferInstance, inferInstance, inferInstance⟩
    exact (fiberFunctor f y T).asEquivalence

end RepresentableZariskiStackMap

/-- A represented fiber together with a property of its actual structure
morphism to the test scheme.-/
structure StackMorphism.FiberRepresentationWithProperty
    {J : GrothendieckTopology Scheme.{u}}
    {F G : StackInGroupoids Scheme.{u} J}
    (f : StackMorphism F G) (P : MorphismProperty Scheme.{u})
    {S : Scheme.{u}} (y : G.presheaf.obj (.mk (op S)))
    extends f.FiberRepresentation y where
  /-- The geometric property is asserted on the representing scheme
  morphism, not on an abstract stack-level token.-/
  property : P representing.hom

/-- A stack morphism is representable with property `P` when every one of its
fibers has a representing scheme whose structure morphism satisfies `P`.-/
class StackMorphism.HasRepresentableProperty
    {J : GrothendieckTopology Scheme.{u}}
    {F G : StackInGroupoids Scheme.{u} J}
    (P : MorphismProperty Scheme.{u}) (f : StackMorphism F G) : Prop where
  representation {S : Scheme.{u}}
    (y : G.presheaf.obj (.mk (op S))) :
    Nonempty (StackMorphism.FiberRepresentationWithProperty f P y)

namespace StackMorphism

variable {J : GrothendieckTopology Scheme.{u}}
  {F G : StackInGroupoids Scheme.{u} J}
  {P Q : MorphismProperty Scheme.{u}} {f : StackMorphism F G}

/-- Forgetting the geometric property recovers ordinary representability.
@isnad1 id=isrepres.0h5v.s5.101e677f3ab5 from=translated src=- shape=eda911aa vocab=9edd81df
-/
theorem isRepresentable_of_hasRepresentableProperty
    [HasRepresentableProperty P f] : f.IsRepresentable := by
  constructor
  intro S y
  obtain ⟨R⟩ := HasRepresentableProperty.representation (P := P) (f := f) y
  exact ⟨R.toFiberRepresentation⟩

/-- Representable properties are monotone under implication of the underlying
scheme-morphism properties.
@isnad1 id=hasrepre.1h6v.s6.34e0407dc89b from=translated src=- shape=57e52586 vocab=1546201b
-/
theorem hasRepresentableProperty_mono (hPQ : P ≤ Q)
    [HasRepresentableProperty P f] : HasRepresentableProperty Q f := by
  constructor
  intro S y
  obtain ⟨R⟩ := HasRepresentableProperty.representation (P := P) (f := f) y
  exact ⟨{ R.toFiberRepresentation with property := hPQ _ R.property }⟩

end StackMorphism

/-- A base-change-stable scheme-morphism property passes to the induced
morphism of representable stacks because each representing morphism is the
corresponding scheme-theoretic pullback.
@isnad1 id=hasrepre.0h5v.s5.d4b4a5080bfb from=translated src=- shape=a0314333 vocab=16f4c0b6
-/
theorem representableZariskiStackMap_hasRepresentableProperty
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : P f) :
    StackMorphism.HasRepresentableProperty P (representableZariskiStackMap f) := by
  constructor
  intro S y
  exact ⟨{
    RepresentableZariskiStackMap.fiberRepresentation f y with
    property := P.pullback_snd f y.as hf }⟩

/-- Local finite presentation for stack morphisms is measured on the actual
representing scheme morphisms of all fibers.-/
abbrev StackMorphism.IsLocallyOfFinitePresentation
    {J : GrothendieckTopology Scheme.{u}}
    {F G : StackInGroupoids Scheme.{u} J}
    (f : StackMorphism F G) : Prop :=
  StackMorphism.HasRepresentableProperty @LocallyOfFinitePresentation f

/-- A smooth-surjective stack cover is representable and every representing
scheme morphism is both smooth and surjective.-/
abbrev StackMorphism.IsSmoothSurjective
    {J : GrothendieckTopology Scheme.{u}}
    {F G : StackInGroupoids Scheme.{u} J}
    (f : StackMorphism F G) : Prop :=
  StackMorphism.HasRepresentableProperty (@Smooth ⊓ @Surjective) f

/-- An open immersion of stacks is representable and is an open immersion
on every actual scheme representing one of its fibers.-/
abbrev StackMorphism.IsOpenImmersion
    {J : GrothendieckTopology Scheme.{u}}
    {F G : StackInGroupoids Scheme.{u} J}
    (f : StackMorphism F G) : Prop :=
  StackMorphism.HasRepresentableProperty @AlgebraicGeometry.IsOpenImmersion f

/-- The identity structural morphism of every representable stack is locally
of finite presentation on all actual fiber schemes.
@isnad1 id=islocall.0h1v.s4.0f36e57685fe from=translated src=- shape=8fb6d0a2 vocab=258147d8
-/
theorem representableZariskiStackMap_id_isLocallyOfFinitePresentation
    (X : Scheme.{u}) :
    StackMorphism.IsLocallyOfFinitePresentation
      (representableZariskiStackMap (𝟙 X)) :=
  representableZariskiStackMap_hasRepresentableProperty
    @LocallyOfFinitePresentation (𝟙 X) inferInstance

/-- A scheme-theoretic open immersion induces an open immersion of its
representable big-Zariski stacks, checked on the actual pullback schemes.
@isnad1 id=isopenim.0h3v.s4.5f97d0055d10 from=translated src=- shape=8026b8c4 vocab=28e31b3d
-/
theorem representableZariskiStackMap_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    StackMorphism.IsOpenImmersion (representableZariskiStackMap f) :=
  representableZariskiStackMap_hasRepresentableProperty
    @AlgebraicGeometry.IsOpenImmersion f inferInstance

/-! ## Diagonal representability and big-Zariski presentations -/

/-- A scheme representing the isomorphisms between the pullbacks of two
objects of a stack.  The equivalence is the pointwise Yoneda universal
property of the representing object over the test scheme.-/
structure StackInGroupoids.DiagonalFiberRepresentation
    {J : GrothendieckTopology Scheme.{u}}
    (F : StackInGroupoids Scheme.{u} J)
    {S : Scheme.{u}} (x y : F.presheaf.obj (.mk (op S))) where
  /-- The scheme of isomorphisms over `S`.-/
  representing : Over S
  /-- Arrows to the representing scheme classify actual isomorphisms after
  pullback.-/
  isomorphismEquiv (T : Over S) :
    (T ⟶ representing) ≃
      (((F.presheaf.map T.hom.op.toLoc).toFunctor.obj x) ≅
        ((F.presheaf.map T.hom.op.toLoc).toFunctor.obj y)
      )

/-- A stack has representable diagonal when every pair of objects has an
actual scheme representing its isomorphism functor.-/
class StackInGroupoids.HasRepresentableDiagonal
    {J : GrothendieckTopology Scheme.{u}}
    (F : StackInGroupoids Scheme.{u} J) : Prop where
  representation {S : Scheme.{u}}
    (x y : F.presheaf.obj (.mk (op S))) :
    Nonempty
      (AlgebraicGeometry.StackInGroupoids.DiagonalFiberRepresentation F x y)

/-- A provisional big-Zariski stack presentation: effective Zariski descent,
a diagonal represented by schemes, and a scheme atlas whose every fiber is
represented by a smooth-surjective scheme morphism.

This is not called `AlgebraicStack`: the standard notion requires fppf descent
or an equivalent étale formulation, and usually asks for the diagonal to be
representable by algebraic spaces.-/
structure ZariskiStackPresentation where
  /-- The underlying big-Zariski stack in groupoids.-/
  toStackInGroupoids : StackInGroupoids Scheme.{u} Scheme.zariskiTopology
  /-- The diagonal is represented by schemes via its isomorphism functors.
  The scheme-level representability is explicit because it is stronger than
  the usual algebraic-space diagonal condition.-/
  schemeDiagonal : AlgebraicGeometry.StackInGroupoids.HasRepresentableDiagonal
    toStackInGroupoids
  /-- The scheme presenting the stack.-/
  atlasScheme : Scheme.{u}
  /-- The atlas morphism from the corresponding representable stack.-/
  atlas : StackMorphism (representableZariskiStack atlasScheme)
    toStackInGroupoids
  /-- Every base change of the atlas is an actual smooth-surjective scheme
  morphism.-/
  atlasSmoothSurjective : StackMorphism.IsSmoothSurjective atlas

/-- A big-Zariski stack presentation locally of finite presentation over a
base scheme, expressed by an actual stack morphism whose every fiber has a
locally-finite-presentation representing scheme morphism.-/
structure ZariskiStackPresentationOver (S : Scheme.{u}) where
  /-- The underlying big-Zariski presentation.-/
  toZariskiStackPresentation : ZariskiStackPresentation
  /-- Its structural morphism to the representable stack of the base.-/
  structureMorphism : StackMorphism
    toZariskiStackPresentation.toStackInGroupoids
      (representableZariskiStack S)
  /-- Local finite presentation is checked on all scheme representatives of
  the structural morphism.-/
  locallyOfFinitePresentation :
    StackMorphism.IsLocallyOfFinitePresentation structureMorphism

end

end AlgebraicGeometry
