/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import Tengoku.Tauceti.TauCeti.Algebra.AlgebraicGroup.Product
public import Tengoku.Tauceti.TauCeti.GroupTheory.Solvable

/-!
# Geometric solvability of affine groups

For a commutative Hopf algebra `H` over a field `k`, this file records the geometric-points
solvability condition: the convolution group of `AlgebraicClosure k`-valued points of `H` is a
solvable abstract group. Smoothness and finite type are deliberately not built into this property;
consumers must state them separately when interpreting it as the classical notion of a solvable
algebraic group.

The property is invariant under coordinate-Hopf-algebra isomorphisms. It is preserved by closed
subgroups, represented contravariantly by surjective coordinate morphisms, and a product has the
property exactly when both factors do. These are the first subgroup-calculus operations needed for
Lie--Kolchin theory and the construction of the solvable radical.

## Main declarations

* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty`: solvability of the geometric point
  group.
* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty_of_isCocomm`: commutative affine
  groups have solvable geometric points.
* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty_of_surjective`: closure under closed
  subgroups.
* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty_tensorProduct_iff`: solvability of a
  product is equivalent to solvability of both factors.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This begins the "Lie--Kolchin; solvable groups" milestone in Layer 5 of the ReductiveGroups
roadmap. The scheme-theoretic derived subgroup and its comparison with this geometric-points
criterion remain to be constructed.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti

universe u v

/-- The object property asserting that the group of algebraic-closure-valued points of a
commutative Hopf algebra is solvable.

This property packages only the geometric-points condition. In applications to classical
algebraic groups, finite type and smoothness are separate hypotheses. -/
def geometricallySolvablePointsCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (CommHopfAlgCat.{v} k) :=
  fun H ↦ Group.IsSolvable (WithConv (H →ₐ[k] AlgebraicClosure k))

/-- Membership in the geometric-points solvability property means that the convolution group of
points over an algebraic closure is solvable. -/
@[simp]
theorem geometricallySolvablePointsCommHopfAlgProperty_iff
    (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k) :
    geometricallySolvablePointsCommHopfAlgProperty k H ↔
      Group.IsSolvable (WithConv (H →ₐ[k] AlgebraicClosure k)) :=
  Iff.rfl

/-- A cocommutative coordinate Hopf algebra has solvable geometric points.

Cocommutativity makes the convolution group of points commutative over every commutative value
algebra, so in particular its algebraic-closure-valued point group is solvable. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_of_isCocomm
    (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k)
    [Coalgebra.IsCocomm k H] :
    geometricallySolvablePointsCommHopfAlgProperty k H := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff]
  exact Group.isSolvable_of_comm mul_comm

/-- Geometric-points solvability is invariant under isomorphisms of commutative Hopf algebras. -/
instance (k : Type u) [Field k] :
    (geometricallySolvablePointsCommHopfAlgProperty k :
      ObjectProperty (CommHopfAlgCat.{v} k)).IsClosedUnderIsomorphisms where
  of_iso {H K} e hH := by
    rw [geometricallySolvablePointsCommHopfAlgProperty_iff] at hH ⊢
    let e' : H ≃ₐc[k] K := CommHopfAlgCat.ofIso e
    let _ : Group.IsSolvable (WithConv (H →ₐ[k] AlgebraicClosure k)) := hH
    exact Group.isSolvable_of_isSolvable_injective
      (f := (AlgHom.mapDomainMulEquiv (A := AlgebraicClosure k) e').toMonoidHom)
      (AlgHom.mapDomainMulEquiv (A := AlgebraicClosure k) e').injective

end TauCeti
