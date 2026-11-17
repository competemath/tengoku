/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.Basic
import Tengoku.Seed.NumberTheory.LSeries.Dirichlet
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ArgumentPrinciple.Residues
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ArgumentPrinciple.Rectangles

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit logarithmic-derivative integrals on zeta rectangles

This file defines the actual four oriented paths and the interval-integral
expression which a future residue/argument-principle proof must evaluate.
The definition is fixed independently of the zero count, preventing an
"argument index" from being introduced merely by naming the desired count.
-/

namespace OverflowResidueRH

/-- The analytic logarithmic derivative `zeta' / zeta`, totalized at poles
and zeros in the same way as the underlying Mathlib operations.  Admissible
rectangle boundaries avoid those exceptional points.-/
noncomputable def zetaLogDeriv (z : Complex) : Complex :=
  deriv riemannZeta z / riemannZeta z

/-! ## A uniform, unconditional bound on Backlund's right edge -/

open scoped LSeries.notation ArithmeticFunction

/-- The absolutely convergent von Mangoldt majorant at real part `2`.
It is a single finite constant, independent of the height.-/
noncomputable def backlundRightEdgeLogDerivBound : Real :=
  ∑' n : Nat,
    ‖LSeries.term (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (2 : Complex) n‖

/-- The right-edge majorant is nonnegative.-/
theorem backlundRightEdgeLogDerivBound_nonneg :
    0 ≤ backlundRightEdgeLogDerivBound := by
  unfold backlundRightEdgeLogDerivBound
  exact tsum_nonneg fun _ => norm_nonneg _

/-- The zeta logarithmic derivative is uniformly bounded on the whole
vertical line `Re s = 2` by one height-independent constant.  This uses
Mathlib's von Mangoldt L-series identity and absolute convergence at `2`;
it is stronger than choosing a new compactness constant on each unit
height window.-/
theorem norm_zetaLogDeriv_two_add_mul_I_le (y : Real) :
    ‖zetaLogDeriv ((2 : Complex) + (y : Complex) * Complex.I)‖ ≤
      backlundRightEdgeLogDerivBound := by
  let f : Nat → Complex :=
    fun n => (ArithmeticFunction.vonMangoldt n : Complex)
  let s : Complex := (2 : Complex) + (y : Complex) * Complex.I
  have hsre : s.re = 2 := by
    simp [s]
  have hsumTwo : LSeriesSummable f (2 : Complex) := by
    dsimp [f]
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hsumS : LSeriesSummable f s := by
    exact hsumTwo.of_re_le_re (by rw [hsre]; norm_num)
  have hnorm :
      ‖LSeries f s‖ ≤ ∑' n : Nat, ‖LSeries.term f s n‖ := by
    exact norm_tsum_le_tsum_norm hsumS.norm
  have hterms :
      (fun n : Nat => ‖LSeries.term f s n‖) =
        fun n : Nat => ‖LSeries.term f (2 : Complex) n‖ := by
    funext n
    simp only [LSeries.norm_term_eq]
    rw [hsre]
    norm_num
  rw [hterms] at hnorm
  have hident :
      LSeries f s =
        -(deriv riemannZeta s / riemannZeta s) := by
    have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (s := s) (by rw [hsre]; norm_num)
    simpa [f, neg_div] using h
  have hzeta : zetaLogDeriv s = -LSeries f s := by
    unfold zetaLogDeriv
    rw [hident]
    simp
  simpa [backlundRightEdgeLogDerivBound, f, s, hzeta] using hnorm

namespace ZetaRectangle

/-- Bottom edge, directed from lower left to lower right.-/
noncomputable def bottomEdge (R : ZetaRectangle) (t : Real) : Complex :=
  ⟨R.left + t * (R.right - R.left), R.bottom⟩

/-- Right edge, directed from lower right to upper right.-/
noncomputable def rightEdge (R : ZetaRectangle) (t : Real) : Complex :=
  ⟨R.right, R.bottom + t * (R.top - R.bottom)⟩

/-- Top edge, directed from upper right to upper left.-/
noncomputable def topEdge (R : ZetaRectangle) (t : Real) : Complex :=
  ⟨R.right - t * (R.right - R.left), R.top⟩

/-- Left edge, directed from upper left to lower left.-/
noncomputable def leftEdge (R : ZetaRectangle) (t : Real) : Complex :=
  ⟨R.left, R.top - t * (R.top - R.bottom)⟩

/-- The constant tangent vector of the positively oriented bottom edge.-/
theorem deriv_bottomEdge (R : ZetaRectangle) (t : Real) :
    deriv R.bottomEdge t = (R.right - R.left : Complex) := by
  have hfun : R.bottomEdge = fun u : Real =>
      (R.left : Complex) + u * (R.right - R.left) +
        (R.bottom : Complex) * Complex.I := by
    funext u
    apply Complex.ext <;> simp [bottomEdge]
  rw [hfun]
  have h := ((hasDerivAt_const t (R.left : Complex)).add
    (((hasDerivAt_id (t : Complex)).comp_ofReal).mul_const
      (R.right - R.left))).add_const
        ((R.bottom : Complex) * Complex.I) |>.deriv
  convert h using 1
  · congr 1
  · ring

/-- The constant tangent vector of the positively oriented right edge.-/
theorem deriv_rightEdge (R : ZetaRectangle) (t : Real) :
    deriv R.rightEdge t = (R.top - R.bottom : Complex) * Complex.I := by
  have hfun : R.rightEdge = fun u : Real =>
      (R.right : Complex) +
        ((R.bottom : Complex) + u * (R.top - R.bottom)) * Complex.I := by
    funext u
    apply Complex.ext <;> simp [rightEdge]
  rw [hfun]
  have h := ((hasDerivAt_const t (R.right : Complex)).add
    (((hasDerivAt_const t (R.bottom : Complex)).add
      (((hasDerivAt_id (t : Complex)).comp_ofReal).mul_const
        (R.top - R.bottom))).mul_const Complex.I)).deriv
  convert h using 1
  · congr 1
  · ring

/-- The constant tangent vector of the positively oriented top edge.-/
theorem deriv_topEdge (R : ZetaRectangle) (t : Real) :
    deriv R.topEdge t = -(R.right - R.left : Complex) := by
  have hfun : R.topEdge = fun u : Real =>
      (R.right : Complex) - u * (R.right - R.left) +
        (R.top : Complex) * Complex.I := by
    funext u
    apply Complex.ext <;> simp [topEdge]
  rw [hfun]
  have h := ((hasDerivAt_const t (R.right : Complex)).sub
    (((hasDerivAt_id (t : Complex)).comp_ofReal).mul_const
      (R.right - R.left))).add_const
        ((R.top : Complex) * Complex.I) |>.deriv
  convert h using 1
  · congr 1
  · ring

/-- The constant tangent vector of the positively oriented left edge.-/
theorem deriv_leftEdge (R : ZetaRectangle) (t : Real) :
    deriv R.leftEdge t = -(R.top - R.bottom : Complex) * Complex.I := by
  have hfun : R.leftEdge = fun u : Real =>
      (R.left : Complex) +
        ((R.top : Complex) - u * (R.top - R.bottom)) * Complex.I := by
    funext u
    apply Complex.ext <;> simp [leftEdge]
  rw [hfun]
  have h := ((hasDerivAt_const t (R.left : Complex)).add
    (((hasDerivAt_const t (R.top : Complex)).sub
      (((hasDerivAt_id (t : Complex)).comp_ofReal).mul_const
        (R.top - R.bottom))).mul_const Complex.I)).deriv
  convert h using 1
  · congr 1
  · ring

/-- Integral of `zeta' / zeta` along the bottom edge.-/
noncomputable def bottomLogDerivIntegral (R : ZetaRectangle) : Complex :=
  ∫ t in (0 : Real)..1,
    zetaLogDeriv (R.bottomEdge t) * deriv R.bottomEdge t

/-- Integral of `zeta' / zeta` along the right edge.-/
noncomputable def rightLogDerivIntegral (R : ZetaRectangle) : Complex :=
  ∫ t in (0 : Real)..1,
    zetaLogDeriv (R.rightEdge t) * deriv R.rightEdge t

/-- Integral of `zeta' / zeta` along the top edge.-/
noncomputable def topLogDerivIntegral (R : ZetaRectangle) : Complex :=
  ∫ t in (0 : Real)..1,
    zetaLogDeriv (R.topEdge t) * deriv R.topEdge t

/-- Integral of `zeta' / zeta` along the left edge.-/
noncomputable def leftLogDerivIntegral (R : ZetaRectangle) : Complex :=
  ∫ t in (0 : Real)..1,
    zetaLogDeriv (R.leftEdge t) * deriv R.leftEdge t

/-- The explicit positively oriented rectangle integral of `zeta' / zeta`.
This is the analytic quantity which must be connected to the divisor by a
residue theorem.-/
noncomputable def rectangleLogDerivIntegral (R : ZetaRectangle) : Complex :=
  R.bottomLogDerivIntegral + R.rightLogDerivIntegral +
    R.topLogDerivIntegral + R.leftLogDerivIntegral

/-- Mathlib's standard positively oriented boundary expression for the same
rectangle.  The four terms are bottom, top, right, and left, in the exact
normalization used by `Complex.integral_boundary_rect_eq_zero_of_*`.-/
noncomputable def mathlibBoundaryLogDerivIntegral
    (R : ZetaRectangle) : Complex :=
  rectangleBoundaryIntegral zetaLogDeriv R.left R.right R.bottom R.top

/-- Affine substitution identifies the parameterized bottom-edge integral
with the bottom term in Mathlib's rectangle-boundary convention.-/
theorem bottomLogDerivIntegral_eq_horizontal (R : ZetaRectangle) :
    R.bottomLogDerivIntegral =
      ∫ x in R.left..R.right,
        zetaLogDeriv (x + (R.bottom : Complex) * Complex.I) := by
  unfold bottomLogDerivIntegral
  simp_rw [deriv_bottomEdge]
  have hpath (t : Real) : R.bottomEdge t =
      ((R.left + (R.right - R.left) * t : Real) : Complex) +
        (R.bottom : Complex) * Complex.I := by
    apply Complex.ext <;> simp [bottomEdge, mul_comm]
  simp_rw [hpath]
  rw [intervalIntegral.integral_mul_const]
  have h := intervalIntegral.smul_integral_comp_add_mul
    (fun x : Real => zetaLogDeriv (x + (R.bottom : Complex) * Complex.I))
    (R.right - R.left) R.left (a := (0 : Real)) (b := 1)
  convert h using 1
  · simp [Algebra.smul_def, mul_comm]
  · congr 1 <;> ring

/-- Affine substitution identifies the parameterized right-edge integral
with the right term in Mathlib's rectangle-boundary convention.-/
theorem rightLogDerivIntegral_eq_vertical (R : ZetaRectangle) :
    R.rightLogDerivIntegral = Complex.I *
      ∫ y in R.bottom..R.top,
        zetaLogDeriv ((R.right : Complex) + y * Complex.I) := by
  unfold rightLogDerivIntegral
  simp_rw [deriv_rightEdge]
  have hpath (t : Real) : R.rightEdge t =
      (R.right : Complex) +
        ((R.bottom + (R.top - R.bottom) * t : Real) : Complex) * Complex.I := by
    apply Complex.ext <;> simp [rightEdge, mul_comm]
  simp_rw [hpath]
  rw [intervalIntegral.integral_mul_const]
  have h := intervalIntegral.smul_integral_comp_add_mul
    (fun y : Real => zetaLogDeriv ((R.right : Complex) + y * Complex.I))
    (R.top - R.bottom) R.bottom (a := (0 : Real)) (b := 1)
  calc
    (∫ (t : Real) in 0..1,
        zetaLogDeriv
          ((R.right : Complex) +
            ((R.bottom + (R.top - R.bottom) * t : Real) : Complex) * Complex.I)) *
        ((R.top - R.bottom : Complex) * Complex.I) =
        Complex.I * ((R.top - R.bottom) •
          ∫ (t : Real) in 0..1,
            zetaLogDeriv
              ((R.right : Complex) +
                ((R.bottom + (R.top - R.bottom) * t : Real) : Complex) * Complex.I)) := by
          simp [Algebra.smul_def]
          ring
    _ = Complex.I *
        ∫ y in R.bottom..R.top,
          zetaLogDeriv ((R.right : Complex) + y * Complex.I) := by
      congr 1
      convert h using 1
      congr 1 <;> ring

/-- The complete right edge of the standard rectangle has a genuine
height-uniform linear bound coming from the single von Mangoldt majorant at
`Re s = 2`.  The constant does not depend on `A` or `T`.-/
theorem norm_standard_rightLogDerivIntegral_le
    {A T : Real} (hAT : A < T) :
    ‖(standard A T hAT).rightLogDerivIntegral‖ ≤
      backlundRightEdgeLogDerivBound * (T - A) := by
  rw [rightLogDerivIntegral_eq_vertical]
  simp only [standard_right, standard_bottom, standard_top]
  rw [norm_mul, Complex.norm_I, one_mul]
  calc
    ‖∫ y in A..T,
        zetaLogDeriv ((2 : Complex) + (y : Complex) * Complex.I)‖ ≤
        backlundRightEdgeLogDerivBound * |T - A| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y _hy
      exact norm_zetaLogDeriv_two_add_mul_I_le y
    _ = backlundRightEdgeLogDerivBound * (T - A) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hAT.le)]

/-- Affine substitution and interval reversal identify the parameterized
top-edge integral with the negative top term in Mathlib's convention.-/
theorem topLogDerivIntegral_eq_horizontal (R : ZetaRectangle) :
    R.topLogDerivIntegral = -
      ∫ x in R.left..R.right,
        zetaLogDeriv (x + (R.top : Complex) * Complex.I) := by
  unfold topLogDerivIntegral
  simp_rw [deriv_topEdge]
  have hpath (t : Real) : R.topEdge t =
      ((R.right + (R.left - R.right) * t : Real) : Complex) +
        (R.top : Complex) * Complex.I := by
    apply Complex.ext <;> simp [topEdge]
    ring
  simp_rw [hpath]
  rw [intervalIntegral.integral_mul_const]
  have h := intervalIntegral.smul_integral_comp_add_mul
    (fun x : Real => zetaLogDeriv (x + (R.top : Complex) * Complex.I))
    (R.left - R.right) R.right (a := (0 : Real)) (b := 1)
  have hreverse :
      (R.left - R.right) •
          ∫ (t : Real) in 0..1,
            zetaLogDeriv
              (((R.right + (R.left - R.right) * t : Real) : Complex) +
                (R.top : Complex) * Complex.I) =
        ∫ x in R.right..R.left,
          zetaLogDeriv (x + (R.top : Complex) * Complex.I) := by
    convert h using 1
    congr 1 <;> ring
  calc
    (∫ (t : Real) in 0..1,
        zetaLogDeriv
          (((R.right + (R.left - R.right) * t : Real) : Complex) +
            (R.top : Complex) * Complex.I)) *
        (-(R.right - R.left : Complex)) =
        (R.left - R.right) •
          ∫ (t : Real) in 0..1,
            zetaLogDeriv
              (((R.right + (R.left - R.right) * t : Real) : Complex) +
                (R.top : Complex) * Complex.I) := by
      simp [Algebra.smul_def]
      ring
    _ = ∫ x in R.right..R.left,
          zetaLogDeriv (x + (R.top : Complex) * Complex.I) := hreverse
    _ = -∫ x in R.left..R.right,
          zetaLogDeriv (x + (R.top : Complex) * Complex.I) := by
      exact intervalIntegral.integral_symm R.left R.right

/-- Affine substitution and interval reversal identify the parameterized
left-edge integral with the negative left term in Mathlib's convention.-/
theorem leftLogDerivIntegral_eq_vertical (R : ZetaRectangle) :
    R.leftLogDerivIntegral = -Complex.I *
      ∫ y in R.bottom..R.top,
        zetaLogDeriv ((R.left : Complex) + y * Complex.I) := by
  unfold leftLogDerivIntegral
  simp_rw [deriv_leftEdge]
  have hpath (t : Real) : R.leftEdge t =
      (R.left : Complex) +
        ((R.top + (R.bottom - R.top) * t : Real) : Complex) * Complex.I := by
    apply Complex.ext <;> simp [leftEdge]
    ring
  simp_rw [hpath]
  rw [intervalIntegral.integral_mul_const]
  have h := intervalIntegral.smul_integral_comp_add_mul
    (fun y : Real => zetaLogDeriv ((R.left : Complex) + y * Complex.I))
    (R.bottom - R.top) R.top (a := (0 : Real)) (b := 1)
  have hreverse :
      (R.bottom - R.top) •
          ∫ (t : Real) in 0..1,
            zetaLogDeriv
              ((R.left : Complex) +
                ((R.top + (R.bottom - R.top) * t : Real) : Complex) * Complex.I) =
        ∫ y in R.top..R.bottom,
          zetaLogDeriv ((R.left : Complex) + y * Complex.I) := by
    convert h using 1
    congr 1 <;> ring
  calc
    (∫ (t : Real) in 0..1,
        zetaLogDeriv
          ((R.left : Complex) +
            ((R.top + (R.bottom - R.top) * t : Real) : Complex) * Complex.I)) *
        (-(R.top - R.bottom : Complex) * Complex.I) =
        Complex.I * ((R.bottom - R.top) •
          ∫ (t : Real) in 0..1,
            zetaLogDeriv
              ((R.left : Complex) +
                ((R.top + (R.bottom - R.top) * t : Real) : Complex) * Complex.I)) := by
      simp [Algebra.smul_def]
      ring
    _ = Complex.I *
        ∫ y in R.top..R.bottom,
          zetaLogDeriv ((R.left : Complex) + y * Complex.I) := by
      rw [hreverse]
    _ = -Complex.I *
        ∫ y in R.bottom..R.top,
          zetaLogDeriv ((R.left : Complex) + y * Complex.I) := by
      rw [intervalIntegral.integral_symm R.bottom R.top]
      ring

/-- The hand-written four-path contour integral is definitionally tied to
Mathlib's rectangle-boundary integral after four proved affine substitutions.
Consequently a future residue theorem can be applied without any orientation
or normalization ambiguity.-/
theorem rectangleLogDerivIntegral_eq_mathlibBoundary
    (R : ZetaRectangle) :
    R.rectangleLogDerivIntegral = R.mathlibBoundaryLogDerivIntegral := by
  rw [rectangleLogDerivIntegral, mathlibBoundaryLogDerivIntegral,
    rectangleBoundaryIntegral,
    bottomLogDerivIntegral_eq_horizontal,
    rightLogDerivIntegral_eq_vertical,
    topLogDerivIntegral_eq_horizontal,
    leftLogDerivIntegral_eq_vertical]
  ring

/-- A chosen integer is genuinely realized by the explicit zeta boundary
integral.-/
def RealizesArgumentIndex (R : ZetaRectangle) (k : Int) : Prop :=
  R.rectangleLogDerivIntegral = twoPiI * (k : Complex)

end ZetaRectangle

end OverflowResidueRH
