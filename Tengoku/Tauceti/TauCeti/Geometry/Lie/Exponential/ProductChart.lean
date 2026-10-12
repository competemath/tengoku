/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Geometry.Lie.Exponential.Derivative.Basic
public import Tengoku.Tauceti.TauCeti.Geometry.Manifold.LocalDiffeomorph

/-!
# Complementary exponential-product charts

For linear subspaces `p` and `q` of the Lie algebra of a finite-dimensional real Lie group, define
the ordered product

`(X, Y) ↦ lieExp X * lieExp Y`

The definition, its smoothness, and its derivative formula hold for arbitrary `p` and `q`. When
they are complementary, the map is a local diffeomorphism at `(0, 0)`, with derivative the addition
equivalence `p × q ≃ Lie(G)` transported through the canonical tangent-space coordinates.

This is the local product chart used to compare a subgroup with a linear complement of its
infinitesimal directions. The result is stated for arbitrary complementary subspaces, independently
of any subgroup.

## Main definitions

* `Submodule.lieExpMulLieExp`: the ordered product of the exponentials of two linear coordinates.

## Main results

* `Submodule.contMDiff_lieExpMulLieExp`: the exponential-product map is globally smooth.
* `Submodule.groupLieAlgebraEquivModelVectorSpace_mfderiv_lieExpMulLieExp_zero_apply`:
  for arbitrary subspaces, the derivative at zero sends a tangent vector to the coordinate of
  the sum of its two source components.
* `Submodule.hasMFDerivAt_lieExpMulLieExp_zero_of_isCompl`: for complementary subspaces, the
  derivative is the canonical addition equivalence in tangent-space coordinates.
* `Submodule.isLocalDiffeomorphAt_lieExpMulLieExp_zero_of_isCompl`: complementary subspaces give a
  local exponential-product chart at the identity.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
-/

public section

noncomputable section

namespace Submodule

open Function Manifold
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothnessThree

/-- The ordered product `(X, Y) ↦ lieExp X * lieExp Y` for two Lie-algebra subspaces, with the
`p`-coordinate exponential as the left factor. -/
def lieExpMulLieExp (p q : Submodule ℝ (LeftInvariantDerivation I G)) (z : p × q) : G :=
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  lieExp (I := I) (G := G) (z.1 : LeftInvariantDerivation I G) *
    lieExp (I := I) (G := G) (z.2 : LeftInvariantDerivation I G)

/-- The exponential-product map evaluates by exponentiating its two coordinates in order. -/
@[simp]
theorem lieExpMulLieExp_apply (p q : Submodule ℝ (LeftInvariantDerivation I G)) (z : p × q) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
    let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
    lieExpMulLieExp (I := I) (G := G) p q z =
      lieExp (z.1 : LeftInvariantDerivation I G) *
        lieExp (z.2 : LeftInvariantDerivation I G) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  dsimp only
  rfl

/-- The exponential-product map sends the zero pair to the group identity. -/
theorem lieExpMulLieExp_zero (p q : Submodule ℝ (LeftInvariantDerivation I G)) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
    let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
    lieExpMulLieExp (I := I) (G := G) p q 0 = 1 := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  rw [lieExpMulLieExp_apply]
  simp

end Submodule
