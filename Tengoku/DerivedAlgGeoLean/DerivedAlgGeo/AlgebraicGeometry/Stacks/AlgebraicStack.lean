/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Stacks.Algebraic
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Stacks.Descent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stack presentations at the fppf level

`Stacks/Algebraic.lean` builds presentation data -- a representable diagonal,
an atlas scheme, a smooth-surjective atlas, and local finite presentation over
a base -- and says of it, in its own words, that it is not an algebraic stack:
the standard notion asks for fppf descent, and that file only ever asks for
Zariski descent.

`Stacks/Representable.lean` supplies `representableFppfStack`,
whose stack condition is Mathlib's fpqc descent theorem for representable
presheaves restricted along `Scheme.fppfTopology ≤ Scheme.fpqcTopology`.

This file puts the two together. The presentations below are the same data as
the big-Zariski ones, over stacks whose descent is fppf.

## What is and is not claimed

The diagonal here is represented by **schemes**, not by algebraic spaces. That
is stronger than the usual condition, not weaker, so a presentation in this
file is more than the definition asks for on that axis -- but it also means
these are not literally the standard `AlgebraicStack` of the literature, and
they are not named as though they were. No Artin representability theorem is
postulated, here or anywhere below it: every atlas, diagonal and finiteness
datum is an actual scheme morphism statement carried in the structure.

## Why the fppf layer costs almost nothing here

`representableFppfStack X` and `representableZariskiStack X` have *the same*
presheaf -- both are `discretePseudofunctor (yoneda.obj X)`, and
`representableFppfStack_presheaf` proves it by `rfl`. They differ only in
which descent theorem they carry, which is a `Prop` field.

A `StackMorphism`, its `FiberRepresentation`, and the representability
vocabulary generalized over an arbitrary topology in `Stacks/Algebraic.lean`
all speak about presheaves and about representing scheme morphisms. None
mentions a covering family. So the fppf morphism *is* the Zariski morphism,
and the constructions below are definitional transports rather than new
proofs. That is the content of `representableFppfStackMap_eq_zariski`: it is
`rfl`, and it is stated precisely so the reader does not have to take the
claim on trust.

This is not a claim that fppf descent is free. It is the observation that the
work of proving it was already done in `Stacks/Descent.lean`, and that
nothing in the presentation vocabulary needed redoing once it stopped naming
a topology it never used.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open Opposite

noncomputable section

universe u

/-! ## The fppf representable stack map -/

/-- A scheme morphism induces the corresponding morphism of representable
big-fppf stacks.

This is the big-Zariski morphism unchanged: the two stacks have the same
presheaf, and a `StackMorphism` is data about presheaves.-/
def representableFppfStackMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    StackMorphism (representableFppfStack X) (representableFppfStack Y) :=
  StackInGroupoids.representableMap Scheme.fppfTopology f

/-- The fppf and Zariski representable stack maps of a scheme morphism are the
same data. Stated, rather than left implicit, because every transport below
relies on it.
@isnad1 id=eq.0h3v.s4.cca97ae34b97 from=translated src=- shape=840734e3 vocab=643777c8
-/
theorem representableFppfStackMap_eq_zariski {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (representableFppfStackMap f : StackMorphism _ _) =
      representableZariskiStackMap f :=
  rfl

/-- A base-change-stable scheme-morphism property passes to the induced
morphism of representable fppf stacks, checked on the actual representing
scheme morphisms.
@isnad1 id=hasrepre.0h5v.s5.1d4b40fc336e from=translated src=- shape=a0314333 vocab=7f5173cf
-/
theorem representableFppfStackMap_hasRepresentableProperty
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : P f) :
    StackMorphism.HasRepresentableProperty P (representableFppfStackMap f) := by
  constructor
  intro S y
  exact ⟨{ representing :=
             (RepresentableZariskiStackMap.fiberRepresentation f y).representing
           fiberEquivalence :=
             (RepresentableZariskiStackMap.fiberRepresentation f y).fiberEquivalence
           property := P.pullback_snd f y.as hf }⟩

/-- A locally finitely presented scheme morphism induces a locally finitely
presented morphism of representable fppf stacks.
@isnad1 id=islocall.0h3v.s4.b0e470c91061 from=translated src=- shape=8026b8c4 vocab=8d39e0f6
-/
theorem representableFppfStackMap_isLocallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    StackMorphism.IsLocallyOfFinitePresentation (representableFppfStackMap f) :=
  representableFppfStackMap_hasRepresentableProperty
    @LocallyOfFinitePresentation f inferInstance

/-- A scheme-theoretic open immersion induces an open immersion of
representable fppf stacks.
@isnad1 id=isopenim.0h3v.s4.5f60b169fb68 from=translated src=- shape=8026b8c4 vocab=6886e7e1
-/
theorem representableFppfStackMap_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    StackMorphism.IsOpenImmersion (representableFppfStackMap f) :=
  representableFppfStackMap_hasRepresentableProperty
    @AlgebraicGeometry.IsOpenImmersion f inferInstance

/-! ## Fppf presentations -/

/-- Presentation data for a big-fppf stack: a representable diagonal, an
atlas scheme, and an atlas whose every base change is an actual
smooth-surjective scheme morphism.

Not called `AlgebraicStack`: the diagonal here is represented by schemes
rather than by algebraic spaces, which is a different -- stronger --
condition than the standard definition asks for.-/
structure FppfStackPresentation where
  /-- The underlying big-fppf stack in groupoids.-/
  toStackInGroupoids : StackInGroupoids Scheme.{u} Scheme.fppfTopology
  /-- The diagonal is represented by schemes via its isomorphism functors.-/
  schemeDiagonal : AlgebraicGeometry.StackInGroupoids.HasRepresentableDiagonal
    toStackInGroupoids
  /-- The scheme presenting the stack.-/
  atlasScheme : Scheme.{u}
  /-- The atlas morphism from the corresponding representable fppf stack.-/
  atlas : StackMorphism (representableFppfStack atlasScheme) toStackInGroupoids
  /-- Every base change of the atlas is an actual smooth-surjective scheme
  morphism.-/
  atlasSmoothSurjective : StackMorphism.IsSmoothSurjective atlas

/-- An fppf stack presentation locally of finite presentation over a base
scheme, with local finite presentation checked on all scheme representatives
of the structural morphism.-/
structure FppfStackPresentationOver (S : Scheme.{u}) where
  /-- The underlying fppf presentation.-/
  toFppfStackPresentation : FppfStackPresentation
  /-- Its structural morphism to the representable fppf stack of the base.-/
  structureMorphism : StackMorphism
    toFppfStackPresentation.toStackInGroupoids
      (representableFppfStack S)
  /-- Local finite presentation, on every scheme representative.-/
  locallyOfFinitePresentation :
    StackMorphism.IsLocallyOfFinitePresentation structureMorphism

end

end AlgebraicGeometry
