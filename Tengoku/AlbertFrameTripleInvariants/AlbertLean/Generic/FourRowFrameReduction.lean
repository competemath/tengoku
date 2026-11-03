import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowUniqueness
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
import Tengoku.Seed.Tactic.Abel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFrameReduction.weighted_cslot_implies_anchored_equation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFrameReduction.anchored_equation_implies_right_quadratic` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFrameReduction.normalized_cslot_equation_of_sum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFrameReduction.right_quadratic_of_normalized_cslots` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Ordinary matrix reduction from normalized component equations

This module contains only associative `3 x 3` matrix algebra.  The letters
`A0`, `A1`, and `A2` are arbitrary matrices; a later source-bound bridge may
instantiate them by adjugates.  In particular, no hypothesis below is called
an Albert frame and no new Albert model is introduced.
-/

noncomputable section

namespace AlbertLean.Generic.FourRowFrameReduction

section RingElimination

variable {R : Type*} [Ring R]

/-- Clear the two left inverses in the normalized c-slot equation.  Right-inverse
equations suffice; only X and 1+X commute with each other.-/
theorem weighted_cslot_implies_anchored_equation
    (X Xi Yi A0 A1 A2 : R)
    (hXXi : X * Xi = 1) (hOneYi : (1 + X) * Yi = 1)
    (hc : A0 + Xi * A1 - Yi * A2 = 0) :
    X ^ 2 * A0 + X * (A0 + A1 - A2) + A1 = 0 := by
  have hXOneXi : X * (1 + X) * Xi = 1 + X := by
    calc
      X * (1 + X) * Xi = (X + X * X) * Xi := by rw [mul_add, mul_one]
      _ = X * Xi + X * X * Xi := by rw [add_mul]
      _ = X * Xi + X * (X * Xi) := by rw [mul_assoc]
      _ = 1 + X := by rw [hXXi, mul_one]
  have hXOneYi : X * (1 + X) * Yi = X := by
    rw [mul_assoc, hOneYi, mul_one]
  have hm := congrArg (fun Z : R => X * (1 + X) * Z) hc
  simp only [mul_zero] at hm
  calc
    X ^ 2 * A0 + X * (A0 + A1 - A2) + A1 =
        (X * (1 + X)) * A0 + (1 + X) * A1 - X * A2 := by
      simp only [pow_two, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_assoc]
      abel
    _ = (X * (1 + X)) * A0 +
          (X * (1 + X) * Xi) * A1 -
          (X * (1 + X) * Yi) * A2 := by rw [hXOneXi, hXOneYi]
    _ = X * (1 + X) * (A0 + Xi * A1 - Yi * A2) := by
      simp only [mul_sub, mul_add, mul_assoc]
    _ = 0 := hm

/-- Right cancellation by `A0i` puts the anchored equation into the exact
right-quadratic convention used by `FourRowUniqueness.GoodSolution`.-/
theorem anchored_equation_implies_right_quadratic
    (X A0 A0i A1 A2 : R)
    (hA0i : A0 * A0i = 1)
    (hanchored : X ^ 2 * A0 + X * (A0 + A1 - A2) + A1 = 0) :
    X ^ 2 + X * ((A0 + A1 - A2) * A0i) + A1 * A0i = 0 := by
  have hm := congrArg (fun Z : R => Z * A0i) hanchored
  simp only [zero_mul] at hm
  calc
    X ^ 2 + X * ((A0 + A1 - A2) * A0i) + A1 * A0i =
        (X ^ 2 * A0 + X * (A0 + A1 - A2) + A1) * A0i := by
      simp only [add_mul, mul_assoc, hA0i, mul_one]
    _ = 0 := hm

end RingElimination

section Matrices

variable {K : Type*} [Field K]

abbrev Mat3 (K : Type*) := Matrix (Fin 3) (Fin 3) K

/-- The explicit coefficient matrices in the normalized right quadratic.-/
def frameU (A0 A1 A2 : Mat3 K) : Mat3 K :=
  (A0 + A1 - A2) * A0⁻¹

def frameV (A0 A1 : Mat3 K) : Mat3 K :=
  A1 * A0⁻¹

/-- The raw sum of the three c-slots, written using the actual nonsingular
matrix inverse.-/
def cslotSum (b0 b1 b2 A0 A1 A2 : Mat3 K) : Mat3 K :=
  b0⁻¹ * A0 + b1⁻¹ * A1 + b2⁻¹ * A2

/-- Normalizing `b0=a0`, `b1=X*a0`, and `b2=-(1+X)*a0` turns the raw c-slot
sum into the weighted equation used by the short elimination lemma.-/
theorem normalized_cslot_equation_of_sum
    (a0 b0 b1 b2 X A0 A1 A2 : Mat3 K)
    (hb0 : b0 = a0)
    (hb1 : b1 = X * a0)
    (hb2 : b2 = -(1 + X) * a0)
    (hb0ne : b0.det ≠ 0)
    (hb1ne : b1.det ≠ 0) (hb2ne : b2.det ≠ 0)
    (hX : X.det ≠ 0) (hOneX : (1 + X).det ≠ 0)
    (hc : cslotSum b0 b1 b2 A0 A1 A2 = 0) :
    A0 + X⁻¹ * A1 - (1 + X)⁻¹ * A2 = 0 := by
  subst b0
  have ha0b0 : a0 * a0⁻¹ = 1 :=
    Matrix.mul_nonsing_inv a0 (isUnit_iff_ne_zero.mpr hb0ne)
  have ha0b1 : a0 * b1⁻¹ = X⁻¹ := by
    calc
      a0 * b1⁻¹ = X⁻¹ * (X * a0 * b1⁻¹) := by
        simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul X
          (isUnit_iff_ne_zero.mpr hX), Matrix.one_mul]
      _ = X⁻¹ * (b1 * b1⁻¹) := by rw [hb1]
      _ = X⁻¹ := by
        rw [Matrix.mul_nonsing_inv b1 (isUnit_iff_ne_zero.mpr hb1ne),
          Matrix.mul_one]
  have ha0b2 : a0 * b2⁻¹ = -(1 + X)⁻¹ := by
    have hb2product : -((1 + X) * (a0 * b2⁻¹)) = 1 := by
      calc
        -((1 + X) * (a0 * b2⁻¹)) = b2 * b2⁻¹ := by
          rw [hb2]
          simp only [neg_mul, Matrix.mul_assoc]
        _ = 1 := Matrix.mul_nonsing_inv b2 (isUnit_iff_ne_zero.mpr hb2ne)
    have hproduct : (1 + X) * (a0 * b2⁻¹) = -1 := by
      calc
        (1 + X) * (a0 * b2⁻¹) = -(-((1 + X) * (a0 * b2⁻¹))) := by simp
        _ = -1 := by rw [hb2product]
    calc
      a0 * b2⁻¹ = (1 + X)⁻¹ * ((1 + X) * (a0 * b2⁻¹)) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul (1 + X)
          (isUnit_iff_ne_zero.mpr hOneX), Matrix.one_mul]
      _ = -(1 + X)⁻¹ := by rw [hproduct]; simp
  have hm := congrArg (fun Z : Mat3 K => a0 * Z) hc
  simp only [cslotSum, mul_zero, mul_add, ← Matrix.mul_assoc] at hm
  rw [ha0b0, ha0b1, ha0b2, Matrix.one_mul, neg_mul] at hm
  simpa only [sub_eq_add_neg, neg_neg] using hm

/-- Component reduction: the normalized b-slots and vanishing sum of
`b_i⁻¹ A_i` force the exact right quadratic, with explicit `U` and `V`.
All hypotheses are ordinary matrix equalities or determinant nonvanishing.-/
theorem right_quadratic_of_normalized_cslots
    (a0 b0 b1 b2 X A0 A1 A2 : Mat3 K)
    (hb0 : b0 = a0)
    (hb1 : b1 = X * a0)
    (hb2 : b2 = -(1 + X) * a0)
    (hb0ne : b0.det ≠ 0)
    (hb1ne : b1.det ≠ 0) (hb2ne : b2.det ≠ 0)
    (hX : X.det ≠ 0) (hOneX : (1 + X).det ≠ 0)
    (hA0 : A0.det ≠ 0)
    (hc : cslotSum b0 b1 b2 A0 A1 A2 = 0) :
    X ^ 2 + X * frameU A0 A1 A2 + frameV A0 A1 = 0 := by
  have hnormalized := normalized_cslot_equation_of_sum
    a0 b0 b1 b2 X A0 A1 A2 hb0 hb1 hb2 hb0ne hb1ne hb2ne hX hOneX hc
  have hanchored := weighted_cslot_implies_anchored_equation
    X X⁻¹ (1 + X)⁻¹ A0 A1 A2
    (Matrix.mul_nonsing_inv X (isUnit_iff_ne_zero.mpr hX))
    (Matrix.mul_nonsing_inv (1 + X) (isUnit_iff_ne_zero.mpr hOneX))
    hnormalized
  simpa only [frameU, frameV] using
    anchored_equation_implies_right_quadratic X A0 A0⁻¹ A1 A2
      (Matrix.mul_nonsing_inv A0 (isUnit_iff_ne_zero.mpr hA0)) hanchored

end Matrices

end AlbertLean.Generic.FourRowFrameReduction
