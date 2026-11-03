import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowComponents
import Tengoku.Seed.Tactic.Abel
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowComponentEquivalence.right_quadratic_implies_anchored_equation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowComponentEquivalence.anchored_equation_implies_weighted_cslot` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowComponentEquivalence.cslot_sum_of_normalized_equation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowComponentEquivalence.components_of_goodSolution` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowComponentEquivalence.components_iff_goodSolution` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Reverse reduction for normalized ordinary matrix components

This module proves that, for fixed invertible first components, the
previous component-to-quadratic reduction loses no displayed matrix equation.
It remains an ordinary matrix theorem and makes no Albert-frame assertion.
-/

noncomputable section
namespace AlbertLean.Generic.FourRowComponentEquivalence

open FourRowFrameReduction FourRowComponents
open FourRowUniqueness (GoodSolution)

section Ring

variable {R : Type*} [Ring R]

/-- Reverse the final right multiplication in the forward reduction.-/
theorem right_quadratic_implies_anchored_equation
    (X A0 A0i A1 A2 : R) (hA0i : A0i * A0 = 1)
    (hquad : X ^ 2 + X * ((A0 + A1 - A2) * A0i) + A1 * A0i = 0) :
    X ^ 2 * A0 + X * (A0 + A1 - A2) + A1 = 0 := by
  have hm := congrArg (fun Z : R => Z * A0) hquad
  simpa only [zero_mul, add_mul, mul_assoc, hA0i, mul_one] using hm

/-- Reverse clearing by `X(1+X)`.  Right-inverse laws expand the product; left-inverse laws cancel it.-/
theorem anchored_equation_implies_weighted_cslot
    (X Xi Yi A0 A1 A2 : R)
    (hXiX : Xi * X = 1) (hXXi : X * Xi = 1)
    (hYiOne : Yi * (1 + X) = 1) (hOneYi : (1 + X) * Yi = 1)
    (hanchored : X ^ 2 * A0 + X * (A0 + A1 - A2) + A1 = 0) :
    A0 + Xi * A1 - Yi * A2 = 0 := by
  let W := A0 + Xi * A1 - Yi * A2
  have hXOneXi : X * (1 + X) * Xi = 1 + X := by
    calc
      X * (1 + X) * Xi = (X + X * X) * Xi := by rw [mul_add, mul_one]
      _ = X * Xi + X * X * Xi := by rw [add_mul]
      _ = X * Xi + X * (X * Xi) := by rw [mul_assoc]
      _ = 1 + X := by rw [hXXi, mul_one]
  have hXOneYi : X * (1 + X) * Yi = X := by rw [mul_assoc, hOneYi, mul_one]
  have hid : X ^ 2 * A0 + X * (A0 + A1 - A2) + A1 = X * (1 + X) * W := by
    dsimp only [W]
    calc
      X ^ 2 * A0 + X * (A0 + A1 - A2) + A1 =
          (X * (1 + X)) * A0 + (1 + X) * A1 - X * A2 := by
        simp only [pow_two, mul_add, add_mul, mul_sub, mul_one, one_mul, mul_assoc]
        abel
      _ = (X * (1 + X)) * A0 + (X * (1 + X) * Xi) * A1 -
          (X * (1 + X) * Yi) * A2 := by rw [hXOneXi, hXOneYi]
      _ = X * (1 + X) * (A0 + Xi * A1 - Yi * A2) := by
        simp only [mul_sub, mul_add, mul_assoc]
  have hcleared : X * (1 + X) * W = 0 := hid.symm.trans hanchored
  have hOne : (1 + X) * W = 0 := by
    have hm := congrArg (fun Z : R => Xi * Z) hcleared
    simpa only [mul_zero, ← mul_assoc, hXiX, one_mul] using hm
  have hW : W = 0 := by
    have hm := congrArg (fun Z : R => Yi * Z) hOne
    simpa only [mul_zero, ← mul_assoc, hYiOne, one_mul] using hm
  exact hW

end Ring

section Matrices

variable {K : Type*} [Field K]
abbrev Mat3K (K : Type*) := Matrix (Fin 3) (Fin 3) K

/-- Recover the raw inverse-adjugate sum from its normalized weighted form.-/
theorem cslot_sum_of_normalized_equation
    (a0 X A0 A1 A2 : Mat3K K)
    (ha0 : a0.det ≠ 0) (hX : X.det ≠ 0)
    (hOneX : (1 + X).det ≠ 0)
    (hb1 : (X * a0).det ≠ 0)
    (hb2 : (-(1 + X) * a0).det ≠ 0)
    (hnormalized : A0 + X⁻¹ * A1 - (1 + X)⁻¹ * A2 = 0) :
    cslotSum a0 (X * a0) (-(1 + X) * a0) A0 A1 A2 = 0 := by
  let S := cslotSum a0 (X * a0) (-(1 + X) * a0) A0 A1 A2
  have ha0b1 : a0 * (X * a0)⁻¹ = X⁻¹ := by
    calc
      a0 * (X * a0)⁻¹ = X⁻¹ * (X * a0 * (X * a0)⁻¹) := by
        simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul X
          (isUnit_iff_ne_zero.mpr hX), Matrix.one_mul]
      _ = X⁻¹ := by
        rw [Matrix.mul_nonsing_inv (X * a0) (isUnit_iff_ne_zero.mpr hb1),
          Matrix.mul_one]
  have ha0b2 : a0 * (-(1 + X) * a0)⁻¹ = -(1 + X)⁻¹ := by
    let b2 : Mat3K K := -(1 + X) * a0
    have hb2product : -((1 + X) * (a0 * b2⁻¹)) = 1 := by
      calc
        -((1 + X) * (a0 * b2⁻¹)) = b2 * b2⁻¹ := by
          dsimp only [b2]
          simp only [neg_mul, Matrix.mul_assoc]
        _ = 1 := Matrix.mul_nonsing_inv b2 (isUnit_iff_ne_zero.mpr hb2)
    have hproduct : (1 + X) * (a0 * b2⁻¹) = -1 := by
      calc
        (1 + X) * (a0 * b2⁻¹) = -(-((1 + X) * (a0 * b2⁻¹))) := by simp
        _ = -1 := by rw [hb2product]
    calc
      a0 * (-(1 + X) * a0)⁻¹ =
          (1 + X)⁻¹ * ((1 + X) * (a0 * b2⁻¹)) := by
        dsimp only [b2]
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul (1 + X)
          (isUnit_iff_ne_zero.mpr hOneX), Matrix.one_mul]
      _ = -(1 + X)⁻¹ := by rw [hproduct]; simp
  have ha0S : a0 * S = 0 := by
    dsimp only [S, cslotSum]
    simp only [mul_add, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv a0 (isUnit_iff_ne_zero.mpr ha0),
      ha0b1, ha0b2, Matrix.one_mul]
    simpa only [neg_mul, sub_eq_add_neg] using hnormalized
  have hm := congrArg (fun Z : Mat3K K => a0⁻¹ * Z) ha0S
  simpa only [mul_zero, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul a0 (isUnit_iff_ne_zero.mpr ha0), one_mul] using hm

/-- On fixed nonzero first components, every good right-quadratic solution
recovers all four fields of `ComponentSolution`.-/
theorem components_of_goodSolution
    (a0 a1 a2 X : Mat3K K)
    (ha0 : a0.det ≠ 0) (ha1 : a1.det ≠ 0) (ha2 : a2.det ≠ 0)
    (hX : GoodSolution (componentU a0 a1 a2) (componentV a0 a1)
      (a1.det / a0.det) (a2.det / a0.det) X) :
    ComponentSolution a0 a1 a2 X := by
  have hnX : X.det ≠ 0 := by rw [hX.det_eq]; exact div_ne_zero ha1 ha0
  have hnOne : (1 + X).det ≠ 0 := by
    rw [hX.det_one_add_eq]
    exact neg_ne_zero.mpr (div_ne_zero ha2 ha0)
  have hdetb1 : (X * a0).det = a1.det := by
    rw [Matrix.det_mul, hX.det_eq]
    field_simp [ha0]
  have hdetb2 : (-(1 + X) * a0).det = a2.det := by
    rw [Matrix.det_mul, Matrix.det_neg, hX.det_one_add_eq]
    simp only [Fintype.card_fin]
    norm_num
    field_simp [ha0]
  have hanchored := right_quadratic_implies_anchored_equation
    X a0.adjugate a0.adjugate⁻¹ a1.adjugate a2.adjugate
    (Matrix.nonsing_inv_mul a0.adjugate (isUnit_iff_ne_zero.mpr (by
      rw [Matrix.det_adjugate]
      exact pow_ne_zero 2 ha0)))
    (by simpa only [componentU, componentV, frameU, frameV] using hX.quadratic)
  have hnormalized := anchored_equation_implies_weighted_cslot
    X X⁻¹ (1 + X)⁻¹ a0.adjugate a1.adjugate a2.adjugate
    (Matrix.nonsing_inv_mul X (isUnit_iff_ne_zero.mpr hnX))
    (Matrix.mul_nonsing_inv X (isUnit_iff_ne_zero.mpr hnX))
    (Matrix.nonsing_inv_mul (1 + X) (isUnit_iff_ne_zero.mpr hnOne))
    (Matrix.mul_nonsing_inv (1 + X) (isUnit_iff_ne_zero.mpr hnOne)) hanchored
  refine ⟨hdetb1, hdetb2, ?_, hX.denominator_det_ne_zero⟩
  exact cslot_sum_of_normalized_equation a0 X a0.adjugate a1.adjugate a2.adjugate
    ha0 hnX hnOne (by rw [hdetb1]; exact ha1) (by rw [hdetb2]; exact ha2)
    hnormalized

/-- Exact equivalence on the displayed invertible ordinary-matrix chart.-/
theorem components_iff_goodSolution
    (a0 a1 a2 X : Mat3K K)
    (ha0 : a0.det ≠ 0) (ha1 : a1.det ≠ 0) (ha2 : a2.det ≠ 0) :
    ComponentSolution a0 a1 a2 X ↔
      GoodSolution (componentU a0 a1 a2) (componentV a0 a1)
        (a1.det / a0.det) (a2.det / a0.det) X :=
  ⟨goodSolution_of_components a0 a1 a2 X ha0 ha1 ha2,
    components_of_goodSolution a0 a1 a2 X ha0 ha1 ha2⟩

end Matrices

end AlbertLean.Generic.FourRowComponentEquivalence
