/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.ProjectiveSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinate transition data for twists on projective space

This file constructs the standard affine-coordinate descent substrate for the twisting sheaves
`O(d)` on projective space.  On `D₊(XᵢXⱼ)` the transition from the `i`th frame to the `j`th
frame is the unit `(Xⱼ / Xᵢ)^d`.  The fraction is represented inside Mathlib's degree-zero
homogeneous localization, its inverse is constructed explicitly, and the transition is packaged
as an automorphism of a free rank-one module.

On `D₊(XᵢXⱼXₗ)` the three restriction maps are explicit homogeneous-localization maps.  The
coordinate ratios and all of their integral powers satisfy the Čech cocycle there.  Thus the
remaining construction of `O(d)` is genuinely a sheaf-gluing step; it no longer needs any
unformalized algebra about graded shifts or coordinate transitions.

This module deliberately does not name the resulting global sheaf before that gluing has been
implemented.  In particular, no private Čech cohomology is introduced: the eventual global
object will feed the existing Ext-based `Scheme.Modules.H`.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace SchemeProjectiveSpace

attribute [local instance] gradedAlgebra

variable (k : Type u) [CommRing k] (n : ℕ)

/-- The coordinate ring of the standard affine chart `D₊(Xᵢ)`.-/
abbrev CoordinateChartRing (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (grading k n) (coordinate k n i)

/-- Every integral twist has a chosen free rank-one module on the `i`th coordinate chart.
The integer is retained in the type of the construction so these local frames can be glued with
the degree-dependent transitions below.-/
abbrev CoordinateTwistModule (_d : ℤ) (i : Fin (n + 1)) :=
  ModuleCat.of (CoordinateChartRing k n i) (CoordinateChartRing k n i)

/-- The homogeneous equation cutting out the overlap `D₊(Xᵢ) ∩ D₊(Xⱼ)`.-/
def coordinateOverlapEquation (i j : Fin (n + 1)) : Polynomial k n :=
  coordinate k n i * coordinate k n j

/-- The overlap equation `XᵢXⱼ` is homogeneous of degree two.-/
theorem coordinateOverlapEquation_mem_degree_two (i j : Fin (n + 1)) :
    coordinateOverlapEquation k n i j ∈ grading k n 2 := by
  simpa [coordinateOverlapEquation] using
    SetLike.mul_mem_graded (coordinate_mem_degree_one k n i)
      (coordinate_mem_degree_one k n j)

/-- The degree-zero homogeneous coordinate ring of `D₊(XᵢXⱼ)`.-/
abbrev CoordinateOverlapRing (i j : Fin (n + 1)) :=
  HomogeneousLocalization.Away (grading k n) (coordinateOverlapEquation k n i j)

/-- The ratio `Xⱼ / Xᵢ` on `D₊(XᵢXⱼ)`, represented as
`Xⱼ² / (XᵢXⱼ)` in the degree-zero homogeneous localization.-/
def coordinateOverlapRatio (i j : Fin (n + 1)) : CoordinateOverlapRing k n i j :=
  HomogeneousLocalization.Away.mk (grading k n)
    (coordinateOverlapEquation_mem_degree_two k n i j) 1
    (coordinate k n j ^ 2) (by
      simpa using SetLike.pow_mem_graded 2 (coordinate_mem_degree_one k n j))

/-- The inverse ratio `Xᵢ / Xⱼ` on `D₊(XᵢXⱼ)`.-/
def coordinateOverlapRatioInv (i j : Fin (n + 1)) : CoordinateOverlapRing k n i j :=
  HomogeneousLocalization.Away.mk (grading k n)
    (coordinateOverlapEquation_mem_degree_two k n i j) 1
    (coordinate k n i ^ 2) (by
      simpa using SetLike.pow_mem_graded 2 (coordinate_mem_degree_one k n i))

/-- The two explicit coordinate ratios multiply to one.-/
theorem coordinateOverlapRatio_mul_inv (i j : Fin (n + 1)) :
    coordinateOverlapRatio k n i j * coordinateOverlapRatioInv k n i j = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, coordinateOverlapRatio,
    coordinateOverlapRatioInv, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_one, Localization.mk_mul]
  rw [← Localization.mk_one]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, mul_one, pow_one]
  change coordinate k n j ^ 2 * coordinate k n i ^ 2 =
    (coordinate k n i * coordinate k n j) *
      (coordinate k n i * coordinate k n j)
  ring

/-- The inverse coordinate ratio also multiplies the forward ratio to one.-/
theorem coordinateOverlapRatio_inv_mul (i j : Fin (n + 1)) :
    coordinateOverlapRatioInv k n i j * coordinateOverlapRatio k n i j = 1 := by
  rw [mul_comm]
  exact coordinateOverlapRatio_mul_inv k n i j

/-- The coordinate ratio `Xⱼ / Xᵢ` as a unit of the overlap ring.-/
def coordinateOverlapRatioUnit (i j : Fin (n + 1)) :
    (CoordinateOverlapRing k n i j)ˣ where
  val := coordinateOverlapRatio k n i j
  inv := coordinateOverlapRatioInv k n i j
  val_inv := coordinateOverlapRatio_mul_inv k n i j
  inv_val := coordinateOverlapRatio_inv_mul k n i j

@[simp]
theorem coordinateOverlapRatioUnit_val (i j : Fin (n + 1)) :
    (coordinateOverlapRatioUnit k n i j : CoordinateOverlapRing k n i j) =
      coordinateOverlapRatio k n i j := rfl

/-- The transition unit `(Xⱼ / Xᵢ)^d` for the integral twist `O(d)`.-/
def twistTransitionUnit (d : ℤ) (i j : Fin (n + 1)) :
    (CoordinateOverlapRing k n i j)ˣ :=
  coordinateOverlapRatioUnit k n i j ^ d

@[simp]
theorem twistTransitionUnit_zero (i j : Fin (n + 1)) :
    twistTransitionUnit k n 0 i j = 1 := by
  simp [twistTransitionUnit]

@[simp]
theorem twistTransitionUnit_neg (d : ℤ) (i j : Fin (n + 1)) :
    twistTransitionUnit k n (-d) i j = (twistTransitionUnit k n d i j)⁻¹ := by
  exact zpow_neg _ d

/-- Multiplication by a unit is an automorphism of the free rank-one module.-/
def unitMulLinearEquiv {R : Type u} [CommRing R] (a : Rˣ) : R ≃ₗ[R] R where
  toFun x := (a : R) * x
  invFun x := (a⁻¹ : Rˣ) * x
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by rw [mul_add]
  map_smul' r x := by simp [smul_eq_mul, mul_comm, mul_left_comm]

/-- The overlap automorphism of the local free rank-one module defining the `O(d)` transition.-/
def twistTransitionLinearEquiv (d : ℤ) (i j : Fin (n + 1)) :
    CoordinateOverlapRing k n i j ≃ₗ[CoordinateOverlapRing k n i j]
      CoordinateOverlapRing k n i j :=
  unitMulLinearEquiv (twistTransitionUnit k n d i j)

@[simp]
theorem twistTransitionLinearEquiv_apply (d : ℤ) (i j : Fin (n + 1))
    (x : CoordinateOverlapRing k n i j) :
    twistTransitionLinearEquiv k n d i j x =
      (twistTransitionUnit k n d i j : CoordinateOverlapRing k n i j) * x := rfl

@[simp]
theorem twistTransitionLinearEquiv_one (d : ℤ) (i j : Fin (n + 1)) :
    twistTransitionLinearEquiv k n d i j 1 =
      (twistTransitionUnit k n d i j : CoordinateOverlapRing k n i j) := by
  simp

/-- The homogeneous equation cutting out the triple overlap
`D₊(Xᵢ) ∩ D₊(Xⱼ) ∩ D₊(Xₗ)`.-/
def coordinateTripleEquation (i j l : Fin (n + 1)) : Polynomial k n :=
  coordinate k n i * coordinate k n j * coordinate k n l

/-- The triple-overlap equation is homogeneous of degree three.-/
theorem coordinateTripleEquation_mem_degree_three (i j l : Fin (n + 1)) :
    coordinateTripleEquation k n i j l ∈ grading k n 3 := by
  simpa [coordinateTripleEquation] using
    SetLike.mul_mem_graded
      (SetLike.mul_mem_graded (coordinate_mem_degree_one k n i)
        (coordinate_mem_degree_one k n j))
      (coordinate_mem_degree_one k n l)

/-- The degree-zero homogeneous coordinate ring of the triple overlap.-/
abbrev CoordinateTripleRing (i j l : Fin (n + 1)) :=
  HomogeneousLocalization.Away (grading k n) (coordinateTripleEquation k n i j l)

/-- The restriction of `Xⱼ / Xᵢ` to the ordered triple overlap.-/
def coordinateTripleRatioIJ (i j l : Fin (n + 1)) :
    CoordinateTripleRing k n i j l :=
  HomogeneousLocalization.Away.mk (grading k n)
    (coordinateTripleEquation_mem_degree_three k n i j l) 1
    (coordinate k n j ^ 2 * coordinate k n l) (by
      simpa using SetLike.mul_mem_graded
        (SetLike.pow_mem_graded 2 (coordinate_mem_degree_one k n j))
        (coordinate_mem_degree_one k n l))

/-- The restriction of `Xₗ / Xⱼ` to the ordered triple overlap.-/
def coordinateTripleRatioJL (i j l : Fin (n + 1)) :
    CoordinateTripleRing k n i j l :=
  HomogeneousLocalization.Away.mk (grading k n)
    (coordinateTripleEquation_mem_degree_three k n i j l) 1
    (coordinate k n l ^ 2 * coordinate k n i) (by
      simpa using SetLike.mul_mem_graded
        (SetLike.pow_mem_graded 2 (coordinate_mem_degree_one k n l))
        (coordinate_mem_degree_one k n i))

/-- The restriction of `Xₗ / Xᵢ` to the ordered triple overlap.-/
def coordinateTripleRatioIL (i j l : Fin (n + 1)) :
    CoordinateTripleRing k n i j l :=
  HomogeneousLocalization.Away.mk (grading k n)
    (coordinateTripleEquation_mem_degree_three k n i j l) 1
    (coordinate k n l ^ 2 * coordinate k n j) (by
      simpa using SetLike.mul_mem_graded
        (SetLike.pow_mem_graded 2 (coordinate_mem_degree_one k n l))
        (coordinate_mem_degree_one k n j))

/-- Restriction from the `ij` overlap ring to the ordered `ijl` triple-overlap ring.-/
def coordinateOverlapToTripleIJ (i j l : Fin (n + 1)) :
    CoordinateOverlapRing k n i j →+* CoordinateTripleRing k n i j l :=
  HomogeneousLocalization.awayMap (grading k n)
    (coordinate_mem_degree_one k n l) (by
      simp only [coordinateTripleEquation, coordinateOverlapEquation])

/-- Restriction from the `jl` overlap ring to the ordered `ijl` triple-overlap ring.-/
def coordinateOverlapToTripleJL (i j l : Fin (n + 1)) :
    CoordinateOverlapRing k n j l →+* CoordinateTripleRing k n i j l :=
  HomogeneousLocalization.awayMap (grading k n)
    (coordinate_mem_degree_one k n i) (by
      simp only [coordinateTripleEquation, coordinateOverlapEquation]
      ring)

/-- Restriction from the `il` overlap ring to the ordered `ijl` triple-overlap ring.-/
def coordinateOverlapToTripleIL (i j l : Fin (n + 1)) :
    CoordinateOverlapRing k n i l →+* CoordinateTripleRing k n i j l :=
  HomogeneousLocalization.awayMap (grading k n)
    (coordinate_mem_degree_one k n j) (by
      simp only [coordinateTripleEquation, coordinateOverlapEquation]
      ring)

@[simp]
theorem coordinateOverlapToTripleJL_ratio (i j l : Fin (n + 1)) :
    coordinateOverlapToTripleJL k n i j l (coordinateOverlapRatio k n j l) =
      coordinateTripleRatioJL k n i j l := by
  apply HomogeneousLocalization.val_injective
  unfold coordinateOverlapToTripleJL coordinateOverlapRatio coordinateTripleRatioJL
  unfold HomogeneousLocalization.Away.mk
  rw [HomogeneousLocalization.val_awayMap_mk]
  simp only [HomogeneousLocalization.val_mk, pow_one]

@[simp]
theorem coordinateOverlapToTripleIL_ratio (i j l : Fin (n + 1)) :
    coordinateOverlapToTripleIL k n i j l (coordinateOverlapRatio k n i l) =
      coordinateTripleRatioIL k n i j l := by
  apply HomogeneousLocalization.val_injective
  unfold coordinateOverlapToTripleIL coordinateOverlapRatio coordinateTripleRatioIL
  unfold HomogeneousLocalization.Away.mk
  rw [HomogeneousLocalization.val_awayMap_mk]
  simp only [HomogeneousLocalization.val_mk, pow_one]

/-- The `ij` coordinate-ratio unit restricted to the ordered triple overlap.-/
def coordinateOverlapRatioTripleUnitIJ (i j l : Fin (n + 1)) :
    (CoordinateTripleRing k n i j l)ˣ :=
  Units.map (coordinateOverlapToTripleIJ k n i j l).toMonoidHom
    (coordinateOverlapRatioUnit k n i j)

/-- The `jl` coordinate-ratio unit restricted to the ordered triple overlap.-/
def coordinateOverlapRatioTripleUnitJL (i j l : Fin (n + 1)) :
    (CoordinateTripleRing k n i j l)ˣ :=
  Units.map (coordinateOverlapToTripleJL k n i j l).toMonoidHom
    (coordinateOverlapRatioUnit k n j l)

/-- The `il` coordinate-ratio unit restricted to the ordered triple overlap.-/
def coordinateOverlapRatioTripleUnitIL (i j l : Fin (n + 1)) :
    (CoordinateTripleRing k n i j l)ˣ :=
  Units.map (coordinateOverlapToTripleIL k n i j l).toMonoidHom
    (coordinateOverlapRatioUnit k n i l)

end SchemeProjectiveSpace
