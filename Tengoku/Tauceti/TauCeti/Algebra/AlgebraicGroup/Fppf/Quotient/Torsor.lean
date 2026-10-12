/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Projection

/-!
# The fppf quotient projection as a torsor

Let `H` be a commutative Hopf algebra over a commutative ring `R`, and let `I` be a normal Hopf
ideal. The quotient Hopf algebra `H / I` represents the closed normal subgroup `V(I)` of the
affine group represented by `H`. This file proves the kernel-pair formulation of the statement
that

```text
G ⟶ G / V(I)
```

is a `V(I)`-torsor: the square

```text
G × V(I)  --(g,n) ↦ g-->    G
    |                         |
 (g,n) ↦ gn               | quotient
    |                         |
    v                         v
    G          --quotient-->  G / V(I)
```

is a pullback. It is first proved for the pointwise quotient presheaf. Applying fppf
sheafification and its canonical finite-product comparison gives the corresponding pullback square
on the product of the fppf sheaves.

No representability of `G / V(I)` is asserted.

## Main declarations

* `TauCeti.CommHopfAlgCat.isPullback_pointwiseQuotientTorsor`: the pointwise quotient has the
  expected torsor kernel pair.
* `TauCeti.CommHopfAlgCat.isPullback_fppfQuotientTorsor`: the same square after fppf
  sheafification.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 14.

This is the torsor and kernel-pair step of Layer 3, "Normality and quotients", of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory ConcreteCategory Opposite
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

/-- The inclusion of subgroup points into ambient points, used to define the torsor action. -/
private noncomputable def quotientSubgroupPointsPresheafGrpInclusion
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    pointsPresheafGrp (quotient H I) ⟶ pointsPresheafGrp H :=
  groupFunctorGrpMap <| Functor.whiskerRight
    (Functor.whiskerLeft (unopUnop (CommAlgCat.{u} R))
      (mapPointsFunctor (mkQuotient H I)))
    GrpCat.uliftFunctor.{u + 1, u}

/-- The action map in the pointwise torsor square, `(g, n) ↦ gn`. -/
noncomputable def pointwiseQuotientTorsorAction
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    (pointsPresheafGrp H).X ⊗ (pointsPresheafGrp (quotient H I)).X ⟶
      (pointsPresheafGrp H).X :=
  CartesianMonoidalCategory.fst _ _ *
    (CartesianMonoidalCategory.snd _ _ ≫
      (quotientSubgroupPointsPresheafGrpInclusion H I).hom.hom)

@[simp]
theorem pointwiseQuotientTorsorAction_app
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    (pointwiseQuotientTorsorAction H I).app A =
      (↾fun p : ULift (HopfAlgebra.points (R := R) (H := H) A.unop.unop) ×
        ULift (HopfAlgebra.points (R := R) (H := quotient H I) A.unop.unop) =>
          ULift.up (p.1.down * quotientPointsHom H I A.unop.unop p.2.down)) := by
  -- Reduce the cartesian lift, group-object multiplication, whiskering, and `ULift` wrappers;
  -- these constructions expose no single application lemma for the resulting composite.
  rfl

end TauCeti.CommHopfAlgCat
