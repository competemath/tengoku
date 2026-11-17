/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Analysis.Complex.CauchyIntegral
import Tengoku.Seed.Analysis.Calculus.LogDeriv
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.LogDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The exact rectangle-residue boundary

Mathlib currently provides rectangular Cauchy--Goursat theorems, but no
meromorphic residue theorem and no argument principle.  This module records
that boundary precisely:

* `rectangleBoundaryIntegral` is the boundary expression used by Mathlib;
* `rectangleBoundaryIntegral_eq_zero_of_differentiableOn` is a proved wrapper
  around Mathlib's rectangular Cauchy--Goursat theorem; and
* `RectangleResidueIdentity` names, without asserting, the additional
  divisor identity required when the integrand has poles.

The final definition is a proposition, not an axiom or an inhabited data
structure.  Downstream zeta code must receive a proof of it explicitly.
-/

open Set
open scoped Interval

namespace OverflowResidueRH

/-- The contour-normalizing constant `2 * pi * I`.-/
noncomputable def twoPiI : Complex :=
  2 * (Real.pi : Complex) * Complex.I

/-- The contour-normalizing constant is nonzero.
@isnad1 id=ne.0h0v.s3.cdad49716a8a from=translated src=- shape=ffdda526 vocab=d6ee077f
-/
theorem twoPiI_ne_zero : twoPiI ≠ 0 := by
  unfold twoPiI
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-- The standard positively oriented boundary integral of a function on the
axis-parallel rectangle `[left,right] x [bottom,top]`.  This is exactly the
four-term expression occurring in Mathlib's rectangular Cauchy--Goursat
theorems.-/
noncomputable def rectangleBoundaryIntegral
    (g : Complex → Complex) (left right bottom top : Real) : Complex :=
  (∫ x in left..right, g (x + (bottom : Complex) * Complex.I)) -
    (∫ x in left..right, g (x + (top : Complex) * Complex.I)) +
    Complex.I * (∫ y in bottom..top,
      g ((right : Complex) + y * Complex.I)) -
    Complex.I * (∫ y in bottom..top,
      g ((left : Complex) + y * Complex.I))

/-- Mathlib's available rectangle theorem: a function differentiable on the
whole closed rectangle has zero boundary integral.  This is Cauchy--Goursat,
not a residue theorem; it cannot be applied directly to a logarithmic
derivative across its zeros.
@isnad1 id=eq.1h5v.s6.4f2d130971da from=translated src=- shape=092c77dd vocab=4afaf510
-/
theorem rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    {g : Complex → Complex} {left right bottom top : Real}
    (hg : DifferentiableOn Complex g
      ([[left, right]] ×ℂ [[bottom, top]])) :
    rectangleBoundaryIntegral g left right bottom top = 0 := by
  simpa [rectangleBoundaryIntegral] using
    (Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      g (⟨left, bottom⟩ : Complex) (⟨right, top⟩ : Complex) hg)

/-- The missing meromorphic step, stated at its exact mathematical strength:
the boundary integral of a proposed logarithmic derivative is `2*pi*I`
times an integer divisor mass.  This definition does not claim that the
identity holds.-/
def RectangleResidueIdentity
    (logDerivative : Complex → Complex)
    (left right bottom top : Real) (divisorMass : Int) : Prop :=
  rectangleBoundaryIntegral logDerivative left right bottom top =
    twoPiI * (divisorMass : Complex)

/-- Unfolding a supplied residue identity yields the normalized equality.
This small theorem is useful in signatures and makes clear that no existence
claim is hidden in the definition.
@isnad1 id=eq.1h6v.s5.efcd007b3eb0 from=translated src=- shape=2c4819bc vocab=f970e960
-/
theorem RectangleResidueIdentity.boundaryIntegral_eq
    {logDerivative : Complex → Complex}
    {left right bottom top : Real} {divisorMass : Int}
    (H : RectangleResidueIdentity logDerivative
      left right bottom top divisorMass) :
    rectangleBoundaryIntegral logDerivative left right bottom top =
      twoPiI * (divisorMass : Complex) :=
  H

/-! ## A genuine rectangular residue calculation

Mathlib does not yet package a general meromorphic residue theorem, but its
complex logarithm and the real fundamental theorem of calculus are already
enough to evaluate the rectangular contour integral of one linear principal
part.  This is the local calculation needed by a future finite-divisor
argument-principle proof; unlike `RectangleResidueIdentity`, it is completely
inhabited.
-/

/-- On a horizontal line which does not pass through `rho`, integrating the
linear principal part is the difference of two values of the principal
complex logarithm.-/
private theorem integral_inv_horizontal_eq_log_sub
    {a b y : Real} {rho : Complex} (hy : y ≠ rho.im) :
    (∫ x in a..b,
      (((x : Complex) + (y : Complex) * Complex.I - rho)⁻¹)) =
      Complex.log ((b : Complex) + (y : Complex) * Complex.I - rho) -
        Complex.log ((a : Complex) + (y : Complex) * Complex.I - rho) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _hx
    have hlin : HasDerivAt
        (fun u : Real =>
          (u : Complex) + (y : Complex) * Complex.I - rho) 1 x := by
      simpa using
        ((((hasDerivAt_id (x : Complex)).comp_ofReal).add_const
          ((y : Complex) * Complex.I)).sub_const rho)
    have hslit :
        (x : Complex) + (y : Complex) * Complex.I - rho ∈
          Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      right
      have him :
          ((x : Complex) + (y : Complex) * Complex.I - rho).im =
            y - rho.im := by simp
      rw [him]
      exact sub_ne_zero.mpr hy
    simpa [div_eq_mul_inv] using hlin.clog_real hslit
  · apply ContinuousOn.intervalIntegrable
    exact
      (((Complex.continuous_ofReal.add continuous_const).sub continuous_const).inv₀
        (fun x => by
          intro hzero
          apply hy
          have him := congrArg Complex.im hzero
          apply sub_eq_zero.mp
          simpa using him)).continuousOn

/-- On a vertical line strictly to the right of `rho`, the oriented vertical
integral is again a logarithmic endpoint difference.-/
private theorem I_mul_integral_inv_vertical_right_eq_log_sub
    {a b x : Real} {rho : Complex} (hx : rho.re < x) :
    Complex.I * (∫ y in a..b,
      (((x : Complex) + (y : Complex) * Complex.I - rho)⁻¹)) =
      Complex.log ((x : Complex) + (b : Complex) * Complex.I - rho) -
        Complex.log ((x : Complex) + (a : Complex) * Complex.I - rho) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y _hy
    have hlin : HasDerivAt
        (fun u : Real =>
          (x : Complex) + (u : Complex) * Complex.I - rho)
        Complex.I y := by
      simpa using
        (((hasDerivAt_const y (x : Complex)).add
          (((hasDerivAt_id (y : Complex)).comp_ofReal).mul_const Complex.I)).sub_const rho)
    have hslit :
        (x : Complex) + (y : Complex) * Complex.I - rho ∈
          Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simpa using hx
    simpa [div_eq_mul_inv] using hlin.clog_real hslit
  · apply ContinuousOn.intervalIntegrable
    exact
      (continuous_const.mul
        (((continuous_const.add
          (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const).inv₀
          (fun y => by
            intro hzero
            have hre := congrArg Complex.re hzero
            have hxsub : x - rho.re = 0 := by simpa using hre
            have : x = rho.re := sub_eq_zero.mp hxsub
            exact (ne_of_gt hx) this))).continuousOn

/-- On a vertical line strictly to the left of `rho`, `log (-z)` supplies the
branch which avoids the principal logarithm's cut.-/
private theorem I_mul_integral_inv_vertical_left_eq_negLog_sub
    {a b x : Real} {rho : Complex} (hx : x < rho.re) :
    Complex.I * (∫ y in a..b,
      (((x : Complex) + (y : Complex) * Complex.I - rho)⁻¹)) =
      Complex.log (-((x : Complex) + (b : Complex) * Complex.I - rho)) -
        Complex.log (-((x : Complex) + (a : Complex) * Complex.I - rho)) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y _hy
    have hlin : HasDerivAt
        (fun u : Real =>
          -((x : Complex) + (u : Complex) * Complex.I - rho))
        (-Complex.I) y := by
      have hbase : HasDerivAt
          (fun u : Real =>
            (x : Complex) + (u : Complex) * Complex.I - rho)
          Complex.I y := by
        simpa using
          (((hasDerivAt_const y (x : Complex)).add
            (((hasDerivAt_id (y : Complex)).comp_ofReal).mul_const Complex.I)).sub_const rho)
      exact hbase.neg
    have hslit :
        -((x : Complex) + (y : Complex) * Complex.I - rho) ∈
          Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simpa using hx
    have hlog := hlin.clog_real hslit
    have hcoeff :
        (-Complex.I) /
            (-((x : Complex) + (y : Complex) * Complex.I - rho)) =
          Complex.I *
            ((x : Complex) + (y : Complex) * Complex.I - rho)⁻¹ := by
      rw [neg_div_neg_eq]
      rfl
    rw [hcoeff] at hlog
    exact hlog
  · apply ContinuousOn.intervalIntegrable
    exact
      (continuous_const.mul
        (((continuous_const.add
          (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const).inv₀
          (fun y => by
            intro hzero
            have hre := congrArg Complex.re hzero
            have hxsub : x - rho.re = 0 := by simpa using hre
            have : x = rho.re := sub_eq_zero.mp hxsub
            exact (ne_of_lt hx) this))).continuousOn

/-- **Residue of a linear principal part on a rectangle.** If `rho` lies in
the open rectangle, then the positively oriented Mathlib boundary integral
of `z ↦ (z - rho)⁻¹` is exactly `2 * pi * I`.

This theorem isolates what can already be proved from Mathlib's logarithm and
interval-integral API.  A general argument principle still additionally needs
an analytic finite-divisor factorization (or a meromorphic residue theorem).
@isnad1 id=eq.4h5v.s5.22029ceea923 from=translated src=- shape=55aaa130 vocab=553a5c9a
-/
theorem rectangleBoundaryIntegral_inv_sub_eq_twoPiI
    {left right bottom top : Real} {rho : Complex}
    (hleft : left < rho.re) (hright : rho.re < right)
    (hbottom : bottom < rho.im) (htop : rho.im < top) :
    rectangleBoundaryIntegral (fun z => (z - rho)⁻¹)
      left right bottom top = twoPiI := by
  have hbottom_ne : bottom ≠ rho.im := ne_of_lt hbottom
  have htop_ne : top ≠ rho.im := ne_of_gt htop
  rw [rectangleBoundaryIntegral,
    integral_inv_horizontal_eq_log_sub hbottom_ne,
    integral_inv_horizontal_eq_log_sub htop_ne,
    I_mul_integral_inv_vertical_right_eq_log_sub hright,
    I_mul_integral_inv_vertical_left_eq_negLog_sub hleft]
  let zBottom : Complex :=
    (left : Complex) + (bottom : Complex) * Complex.I - rho
  let zTop : Complex :=
    (left : Complex) + (top : Complex) * Complex.I - rho
  have hzBottom_im : zBottom.im < 0 := by
    dsimp [zBottom]
    simpa using hbottom
  have hzTop_im : 0 < zTop.im := by
    dsimp [zTop]
    simpa using htop
  have hlogBottom :
      Complex.log (-zBottom) - Complex.log zBottom =
        (Real.pi : Complex) * Complex.I := by
    rw [Complex.log, Complex.log, norm_neg,
      Complex.arg_neg_eq_arg_add_pi_of_im_neg hzBottom_im]
    push_cast
    ring
  have hlogTop :
      Complex.log zTop - Complex.log (-zTop) =
        (Real.pi : Complex) * Complex.I := by
    rw [Complex.log, Complex.log, norm_neg,
      Complex.arg_neg_eq_arg_sub_pi_of_im_pos hzTop_im]
    push_cast
    ring
  change
    (Complex.log
          ((right : Complex) + (bottom : Complex) * Complex.I - rho) -
        Complex.log zBottom) -
      (Complex.log
          ((right : Complex) + (top : Complex) * Complex.I - rho) -
        Complex.log zTop) +
      (Complex.log
          ((right : Complex) + (top : Complex) * Complex.I - rho) -
        Complex.log
          ((right : Complex) + (bottom : Complex) * Complex.I - rho)) -
      (Complex.log (-zTop) - Complex.log (-zBottom)) = twoPiI
  have hnegBottom : Complex.log (-zBottom) =
      Complex.log zBottom + (Real.pi : Complex) * Complex.I := by
    linear_combination hlogBottom
  have hnegTop : Complex.log (-zTop) =
      Complex.log zTop - (Real.pi : Complex) * Complex.I := by
    linear_combination -hlogTop
  rw [hnegBottom, hnegTop]
  unfold twoPiI
  ring

/-- The linear-principal-part version of
`rectangleBoundaryIntegral_inv_sub_eq_twoPiI`.  In particular, choosing an
integer cast as `c` gives exactly the residue contribution of a zero or pole
with that signed multiplicity.
@isnad1 id=eq.4h6v.s6.d66614414eda from=translated src=- shape=24cf247d vocab=038a6c44
-/
theorem rectangleBoundaryIntegral_const_mul_inv_sub_eq
    {left right bottom top : Real} {rho c : Complex}
    (hleft : left < rho.re) (hright : rho.re < right)
    (hbottom : bottom < rho.im) (htop : rho.im < top) :
    rectangleBoundaryIntegral (fun z => c * (z - rho)⁻¹)
      left right bottom top = twoPiI * c := by
  unfold rectangleBoundaryIntegral
  simp_rw [intervalIntegral.integral_const_mul]
  have h := rectangleBoundaryIntegral_inv_sub_eq_twoPiI
    hleft hright hbottom htop
  unfold rectangleBoundaryIntegral at h
  rw [← h]
  ring

/-- A principal part whose center is outside the closed rectangle has zero
boundary integral, directly by Mathlib's rectangular Cauchy--Goursat
theorem.
@isnad1 id=eq.1h5v.s5.1d55997fbec8 from=translated src=- shape=c35c07b7 vocab=d4bf22c5
-/
theorem rectangleBoundaryIntegral_inv_sub_eq_zero_of_outside
    {left right bottom top : Real} {rho : Complex}
    (hout : ∀ z ∈ ([[left, right]] ×ℂ [[bottom, top]]), z ≠ rho) :
    rectangleBoundaryIntegral (fun z => (z - rho)⁻¹)
      left right bottom top = 0 := by
  apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn
  intro z hz
  exact ((differentiableAt_id.sub (differentiableAt_const rho)).inv
    (sub_ne_zero.mpr (hout z hz))).differentiableWithinAt

/-- Linear version of
`rectangleBoundaryIntegral_inv_sub_eq_zero_of_outside`.
@isnad1 id=eq.1h6v.s6.3e7424ad0580 from=translated src=- shape=1b9a22dc vocab=7b894322
-/
theorem rectangleBoundaryIntegral_const_mul_inv_sub_eq_zero_of_outside
    {left right bottom top : Real} {rho c : Complex}
    (hout : ∀ z ∈ ([[left, right]] ×ℂ [[bottom, top]]), z ≠ rho) :
    rectangleBoundaryIntegral (fun z => c * (z - rho)⁻¹)
      left right bottom top = 0 := by
  calc
    rectangleBoundaryIntegral (fun z => c * (z - rho)⁻¹)
        left right bottom top =
        c * rectangleBoundaryIntegral (fun z => (z - rho)⁻¹)
          left right bottom top := by
      unfold rectangleBoundaryIntegral
      simp_rw [intervalIntegral.integral_const_mul]
      ring
    _ = 0 := by
      rw [rectangleBoundaryIntegral_inv_sub_eq_zero_of_outside hout]
      simp

private theorem intervalIntegrable_const_mul_inv_horizontal
    {a b y : Real} {rho c : Complex} (hy : y ≠ rho.im) :
    IntervalIntegrable
      (fun x : Real =>
        c * ((x : Complex) + (y : Complex) * Complex.I - rho)⁻¹)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact
    (continuous_const.mul
      (((Complex.continuous_ofReal.add continuous_const).sub continuous_const).inv₀
        (fun x => by
          intro hzero
          apply hy
          have him := congrArg Complex.im hzero
          apply sub_eq_zero.mp
          simpa using him))).continuousOn

private theorem intervalIntegrable_const_mul_inv_vertical
    {a b x : Real} {rho c : Complex} (hx : x ≠ rho.re) :
    IntervalIntegrable
      (fun y : Real =>
        c * ((x : Complex) + (y : Complex) * Complex.I - rho)⁻¹)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact
    (continuous_const.mul
      (((continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const).inv₀
        (fun y => by
          intro hzero
          apply hx
          have hre := congrArg Complex.re hzero
          apply sub_eq_zero.mp
          simpa using hre))).continuousOn

/-- A finite sum of linear principal parts.  Repeated centers are allowed,
so an occurrence index can encode analytic multiplicity without first
combining coefficients.-/
noncomputable def finitePrincipalPart {ι : Type*}
    (s : Finset ι) (rho : ι → Complex) (c : ι → Complex) (z : Complex) :
    Complex :=
  ∑ i ∈ s, c i * (z - rho i)⁻¹

private theorem intervalIntegrable_const_mul_inv_horizontal_of_ne
    {a b y : Real} {rho c : Complex}
    (hne : ∀ x ∈ [[a, b]],
      (x : Complex) + (y : Complex) * Complex.I ≠ rho) :
    IntervalIntegrable
      (fun x : Real =>
        c * ((x : Complex) + (y : Complex) * Complex.I - rho)⁻¹)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact
    (continuousOn_const.mul
      (((Complex.continuous_ofReal.add continuous_const).sub continuous_const).continuousOn.inv₀
        (fun x hx => sub_ne_zero.mpr (hne x hx))))

private theorem intervalIntegrable_const_mul_inv_vertical_of_ne
    {a b x : Real} {rho c : Complex}
    (hne : ∀ y ∈ [[a, b]],
      (x : Complex) + (y : Complex) * Complex.I ≠ rho) :
    IntervalIntegrable
      (fun y : Real =>
        c * ((x : Complex) + (y : Complex) * Complex.I - rho)⁻¹)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact
    (continuousOn_const.mul
      (((continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const).continuousOn.inv₀
        (fun y hy => sub_ne_zero.mpr (hne y hy))))

/-- Boundary integration commutes with a finite sum of principal parts as
soon as the four families of edge restrictions are interval-integrable.
@isnad1 id=eq.4h8v.s8.926e2f7c1144 from=translated src=- shape=207c0dde vocab=f83d41e6
-/
theorem rectangleBoundaryIntegral_finitePrincipalPart_eq_sum
    {ι : Type*} (s : Finset ι) (rho : ι → Complex) (c : ι → Complex)
    {left right bottom top : Real}
    (hBottomInt : ∀ i ∈ s, IntervalIntegrable
      (fun x : Real =>
        c i * ((x : Complex) + (bottom : Complex) * Complex.I - rho i)⁻¹)
      MeasureTheory.volume left right)
    (hTopInt : ∀ i ∈ s, IntervalIntegrable
      (fun x : Real =>
        c i * ((x : Complex) + (top : Complex) * Complex.I - rho i)⁻¹)
      MeasureTheory.volume left right)
    (hRightInt : ∀ i ∈ s, IntervalIntegrable
      (fun y : Real =>
        c i * ((right : Complex) + (y : Complex) * Complex.I - rho i)⁻¹)
      MeasureTheory.volume bottom top)
    (hLeftInt : ∀ i ∈ s, IntervalIntegrable
      (fun y : Real =>
        c i * ((left : Complex) + (y : Complex) * Complex.I - rho i)⁻¹)
      MeasureTheory.volume bottom top) :
    rectangleBoundaryIntegral (finitePrincipalPart s rho c)
        left right bottom top =
      ∑ i ∈ s, rectangleBoundaryIntegral
        (fun z => c i * (z - rho i)⁻¹) left right bottom top := by
  classical
  unfold rectangleBoundaryIntegral finitePrincipalPart
  rw [intervalIntegral.integral_finsetSum hBottomInt,
    intervalIntegral.integral_finsetSum hTopInt,
    intervalIntegral.integral_finsetSum hRightInt,
    intervalIntegral.integral_finsetSum hLeftInt]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- A center lies in the open axis-parallel rectangle.-/
def InOpenRectangle (left right bottom top : Real) (rho : Complex) : Prop :=
  left < rho.re ∧ rho.re < right ∧ bottom < rho.im ∧ rho.im < top

open Classical in
/-- General finite rectangular residue formula. Each center is classified as
either strictly inside or outside the whole closed rectangle.  The latter
condition is what a no-zero-on-boundary hypothesis reduces to after splitting
on interior membership.
@isnad1 id=eq.3h8v.s7.5cb6426e7df2 from=translated src=- shape=fa1f3099 vocab=606238aa
-/
theorem rectangleBoundaryIntegral_finitePrincipalPart_eq_insideSum
    {ι : Type*} (s : Finset ι) (rho : ι → Complex) (c : ι → Complex)
    {left right bottom top : Real}
    (hlr : left ≤ right) (hbt : bottom ≤ top)
    (hclass : ∀ i ∈ s,
      InOpenRectangle left right bottom top (rho i) ∨
        (∀ z ∈ ([[left, right]] ×ℂ [[bottom, top]]), z ≠ rho i)) :
    rectangleBoundaryIntegral (finitePrincipalPart s rho c)
        left right bottom top =
      twoPiI * ∑ i ∈ s.filter
        (InOpenRectangle left right bottom top ∘ rho), c i := by
  classical
  have hBottomInt : ∀ i ∈ s, IntervalIntegrable
      (fun x : Real =>
        c i * ((x : Complex) + (bottom : Complex) * Complex.I - rho i)⁻¹)
      MeasureTheory.volume left right := by
    intro i hi
    rcases hclass i hi with hin | hout
    · exact intervalIntegrable_const_mul_inv_horizontal
        (ne_of_lt hin.2.2.1)
    · apply intervalIntegrable_const_mul_inv_horizontal_of_ne
      intro x hx
      apply hout ((x : Complex) + (bottom : Complex) * Complex.I)
      constructor
      · simpa using hx
      · simpa [Set.uIcc_of_le hbt]
  have hTopInt : ∀ i ∈ s, IntervalIntegrable
      (fun x : Real =>
        c i * ((x : Complex) + (top : Complex) * Complex.I - rho i)⁻¹)
      MeasureTheory.volume left right := by
    intro i hi
    rcases hclass i hi with hin | hout
    · exact intervalIntegrable_const_mul_inv_horizontal
        (ne_of_gt hin.2.2.2)
    · apply intervalIntegrable_const_mul_inv_horizontal_of_ne
      intro x hx
      apply hout ((x : Complex) + (top : Complex) * Complex.I)
      constructor
      · simpa using hx
      · simpa [Set.uIcc_of_le hbt]
  have hRightInt : ∀ i ∈ s, IntervalIntegrable
      (fun y : Real =>
        c i * ((right : Complex) + (y : Complex) * Complex.I - rho i)⁻¹)
      MeasureTheory.volume bottom top := by
    intro i hi
    rcases hclass i hi with hin | hout
    · exact intervalIntegrable_const_mul_inv_vertical
        (ne_of_gt hin.2.1)
    · apply intervalIntegrable_const_mul_inv_vertical_of_ne
      intro y hy
      apply hout ((right : Complex) + (y : Complex) * Complex.I)
      constructor
      · simpa [Set.uIcc_of_le hlr]
      · simpa using hy
  have hLeftInt : ∀ i ∈ s, IntervalIntegrable
      (fun y : Real =>
        c i * ((left : Complex) + (y : Complex) * Complex.I - rho i)⁻¹)
      MeasureTheory.volume bottom top := by
    intro i hi
    rcases hclass i hi with hin | hout
    · exact intervalIntegrable_const_mul_inv_vertical
        (ne_of_lt hin.1)
    · apply intervalIntegrable_const_mul_inv_vertical_of_ne
      intro y hy
      apply hout ((left : Complex) + (y : Complex) * Complex.I)
      constructor
      · simpa [Set.uIcc_of_le hlr]
      · simpa using hy
  rw [rectangleBoundaryIntegral_finitePrincipalPart_eq_sum
    s rho c hBottomInt hTopInt hRightInt hLeftInt]
  calc
    (∑ i ∈ s, rectangleBoundaryIntegral
        (fun z => c i * (z - rho i)⁻¹) left right bottom top) =
      ∑ i ∈ s, if InOpenRectangle left right bottom top (rho i)
        then twoPiI * c i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs with hin
      · exact rectangleBoundaryIntegral_const_mul_inv_sub_eq
          hin.1 hin.2.1 hin.2.2.1 hin.2.2.2
      · rcases hclass i hi with hinside | hout
        · exact (hin hinside).elim
        · exact rectangleBoundaryIntegral_const_mul_inv_sub_eq_zero_of_outside hout
    _ = twoPiI * ∑ i ∈ s.filter
          (InOpenRectangle left right bottom top ∘ rho), c i := by
      rw [Finset.mul_sum]
      clear hclass hBottomInt hTopInt hRightInt hLeftInt hlr hbt
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          by_cases hp : InOpenRectangle left right bottom top (rho a)
          · rw [Finset.filter_insert]
            simp [ha, hp, ih, Function.comp_apply]
          · rw [Finset.filter_insert]
            simp [ha, hp, ih, Function.comp_apply]

/-- **Finite rectangular residue formula for explicit principal parts.**
Every center lies strictly inside the rectangle; the boundary integral of
their finite principal-part sum is `2*pi*I` times the sum of the supplied
coefficients.  This is the strongest residue theorem needed after one has
factored an analytic function into its finite interior divisor and a
zero-free analytic factor.
@isnad1 id=eq.4h8v.s7.9fb0112ee192 from=translated src=- shape=0a1d1462 vocab=2896a4cc
-/
theorem rectangleBoundaryIntegral_finitePrincipalPart_eq
    {ι : Type*} (s : Finset ι) (rho : ι → Complex) (c : ι → Complex)
    {left right bottom top : Real}
    (hleft : ∀ i ∈ s, left < (rho i).re)
    (hright : ∀ i ∈ s, (rho i).re < right)
    (hbottom : ∀ i ∈ s, bottom < (rho i).im)
    (htop : ∀ i ∈ s, (rho i).im < top) :
    rectangleBoundaryIntegral (finitePrincipalPart s rho c)
      left right bottom top = twoPiI * ∑ i ∈ s, c i := by
  classical
  have hBottomInt : ∀ i ∈ s, IntervalIntegrable
      (fun x : Real =>
        c i * ((x : Complex) + (bottom : Complex) * Complex.I - rho i)⁻¹)
      MeasureTheory.volume left right := by
    intro i hi
    exact intervalIntegrable_const_mul_inv_horizontal
      (ne_of_lt (hbottom i hi))
  have hTopInt : ∀ i ∈ s, IntervalIntegrable
      (fun x : Real =>
        c i * ((x : Complex) + (top : Complex) * Complex.I - rho i)⁻¹)
      MeasureTheory.volume left right := by
    intro i hi
    exact intervalIntegrable_const_mul_inv_horizontal
      (ne_of_gt (htop i hi))
  have hRightInt : ∀ i ∈ s, IntervalIntegrable
      (fun y : Real =>
        c i * ((right : Complex) + (y : Complex) * Complex.I - rho i)⁻¹)
      MeasureTheory.volume bottom top := by
    intro i hi
    exact intervalIntegrable_const_mul_inv_vertical
      (ne_of_gt (hright i hi))
  have hLeftInt : ∀ i ∈ s, IntervalIntegrable
      (fun y : Real =>
        c i * ((left : Complex) + (y : Complex) * Complex.I - rho i)⁻¹)
      MeasureTheory.volume bottom top := by
    intro i hi
    exact intervalIntegrable_const_mul_inv_vertical
      (ne_of_lt (hleft i hi))
  unfold rectangleBoundaryIntegral finitePrincipalPart
  rw [intervalIntegral.integral_finsetSum hBottomInt,
    intervalIntegral.integral_finsetSum hTopInt,
    intervalIntegral.integral_finsetSum hRightInt,
    intervalIntegral.integral_finsetSum hLeftInt]
  calc
    (∑ i ∈ s, ∫ x in left..right,
          c i * ((x : Complex) + (bottom : Complex) * Complex.I - rho i)⁻¹) -
        (∑ i ∈ s, ∫ x in left..right,
          c i * ((x : Complex) + (top : Complex) * Complex.I - rho i)⁻¹) +
        Complex.I * (∑ i ∈ s, ∫ y in bottom..top,
          c i * ((right : Complex) + (y : Complex) * Complex.I - rho i)⁻¹) -
        Complex.I * (∑ i ∈ s, ∫ y in bottom..top,
          c i * ((left : Complex) + (y : Complex) * Complex.I - rho i)⁻¹) =
        ∑ i ∈ s,
          ((∫ x in left..right,
              c i * ((x : Complex) + (bottom : Complex) * Complex.I - rho i)⁻¹) -
            (∫ x in left..right,
              c i * ((x : Complex) + (top : Complex) * Complex.I - rho i)⁻¹) +
            Complex.I * (∫ y in bottom..top,
              c i * ((right : Complex) + (y : Complex) * Complex.I - rho i)⁻¹) -
            Complex.I * (∫ y in bottom..top,
              c i * ((left : Complex) + (y : Complex) * Complex.I - rho i)⁻¹)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = ∑ i ∈ s, twoPiI * c i := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa [rectangleBoundaryIntegral] using
        (rectangleBoundaryIntegral_const_mul_inv_sub_eq
          (hleft i hi) (hright i hi) (hbottom i hi) (htop i hi)
          (c := c i))
    _ = twoPiI * ∑ i ∈ s, c i := by
      rw [Finset.mul_sum]

end OverflowResidueRH
