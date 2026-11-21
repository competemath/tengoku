/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Seed.Analysis.Calculus.Deriv.MeanValue
import Tengoku.Seed.Analysis.InnerProductSpace.Calculus
import Tengoku.Randomsettheory.RandomSetTheory.StrongMonotonicity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Jacobian criterion for strong monotonicity

This file proves the differentiable sufficient condition used in
`eq:z_jacobian_monotonicity` of the report.  On a convex parameter set, a
pointwise lower bound on the quadratic form of the derivative implies strong
monotonicity with exactly the same constant.

The main theorem is stated using an explicit derivative field and
`HasFDerivWithinAt`.  It therefore remains meaningful at the boundary of the
parameter set and does not require the set to have nonempty interior.  A
second theorem gives the familiar formulation using the ambient `fderiv`.

The proof scalarizes the estimating map along the segment joining the two
parameters and applies the one-dimensional mean value theorem.  Continuity of
the derivative is not needed: differentiability along the segment suffices.
-/

open Set
open scoped InnerProductSpace

noncomputable section

namespace RandomSetTheory

variable {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strong monotonicity of an ambient map after restricting both arguments to
`Theta`.  This is the ambient-set counterpart of `UniformStrongMonotonicity`.-/
def StrongMonotonicityOn (Theta : Set E) (kappa : ℝ) (f : E → E) : Prop :=
  ∀ ⦃x⦄, x ∈ Theta → ∀ ⦃y⦄, y ∈ Theta →
    kappa * ‖x - y‖ ^ 2 ≤ ⟪f x - f y, x - y⟫_ℝ

/-- Uniform ambient strong monotonicity for a family of maps.-/
def UniformStrongMonotonicityOn (Theta : Set E) (kappa : ℝ)
    (g : P → E → E) : Prop :=
  ∀ p, StrongMonotonicityOn Theta kappa (g p)

/-- A lower bound on the quadratic form of every derivative in a family.

For a real map, this is equivalent to the same lower bound on the symmetric
part of the derivative, since the skew-symmetric part has zero quadratic
form.-/
def UniformDerivativeLowerBoundOn (Theta : Set E) (kappa : ℝ)
    (Dg : P → E → E →L[ℝ] E) : Prop :=
  ∀ p x, x ∈ Theta → ∀ v,
    kappa * ‖v‖ ^ 2 ≤ ⟪Dg p x v, v⟫_ℝ

/-- A derivative lower bound on a convex set implies strong monotonicity.

The derivative is allowed to be a derivative *within* `Theta`.  This makes
the statement valid on closed convex domains and even on convex sets with
empty ambient interior.-/
theorem strongMonotonicityOn_of_hasFDerivWithinAt
    (Theta : Set E) (kappa : ℝ) (f : E → E) (Df : E → E →L[ℝ] E)
    (hTheta : Convex ℝ Theta)
    (hderiv : ∀ x, x ∈ Theta → HasFDerivWithinAt f (Df x) Theta x)
    (hlower : ∀ x, x ∈ Theta → ∀ v,
      kappa * ‖v‖ ^ 2 ≤ ⟪Df x v, v⟫_ℝ) :
    StrongMonotonicityOn Theta kappa f := by
  intro x hx y hy
  let d : E := x - y
  let line : ℝ → E := AffineMap.lineMap y x
  let phi : ℝ → ℝ := fun t ↦ ⟪f (line t), d⟫_ℝ
  have hmaps : MapsTo line (Icc (0 : ℝ) 1) Theta := by
    intro t ht
    exact hTheta.lineMap_mem hy hx ht
  have hlineDeriv (t : ℝ) :
      HasDerivWithinAt line d (Icc (0 : ℝ) 1) t := by
    simpa [line, d] using
      (AffineMap.hasDerivWithinAt_lineMap
        (a := y) (b := x) (s := Icc (0 : ℝ) 1) (x := t))
  have hphiDeriv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt phi ⟪Df (line t) d, d⟫_ℝ
        (Icc (0 : ℝ) 1) t := by
    have hcomp :
        HasDerivWithinAt (f ∘ line) (Df (line t) d)
          (Icc (0 : ℝ) 1) t :=
      (hderiv (line t) (hmaps ht)).comp_hasDerivWithinAt t
        (hlineDeriv t) hmaps
    have hconst :
        HasDerivWithinAt (fun _ : ℝ ↦ d) 0 (Icc (0 : ℝ) 1) t :=
      hasDerivWithinAt_const t (Icc (0 : ℝ) 1) d
    simpa [phi, Function.comp_def] using hcomp.inner ℝ hconst
  have hcont : ContinuousOn phi (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hphiDeriv t ht).continuousWithinAt
  have hdiff : DifferentiableOn ℝ phi (interior (Icc (0 : ℝ) 1)) := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    exact ((hphiDeriv t htIcc).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)).differentiableAt.differentiableWithinAt
  have hlowerDeriv : ∀ t ∈ interior (Icc (0 : ℝ) 1),
      kappa * ‖d‖ ^ 2 ≤ deriv phi t := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    have hfull := (hphiDeriv t htIcc).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)
    rw [hfull.deriv]
    exact hlower (line t) (hmaps htIcc) d
  have hmvt :=
    (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
      hcont hdiff hlowerDeriv 0 (left_mem_Icc.mpr zero_le_one)
      1 (right_mem_Icc.mpr zero_le_one) zero_le_one
  simpa [phi, line, d, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, inner_sub_left] using hmvt

/-- Family version of
`strongMonotonicityOn_of_hasFDerivWithinAt`.-/
theorem uniformStrongMonotonicityOn_of_hasFDerivWithinAt
    (Theta : Set E) (kappa : ℝ) (g : P → E → E)
    (Dg : P → E → E →L[ℝ] E)
    (hTheta : Convex ℝ Theta)
    (hderiv : ∀ p x, x ∈ Theta →
      HasFDerivWithinAt (g p) (Dg p x) Theta x)
    (hlower : UniformDerivativeLowerBoundOn Theta kappa Dg) :
    UniformStrongMonotonicityOn Theta kappa g := by
  intro p
  exact strongMonotonicityOn_of_hasFDerivWithinAt Theta kappa (g p)
    (Dg p) hTheta (hderiv p) (hlower p)

/-- Version formulated solely with differentiability within `Theta` and
`fderivWithin`.  Unlike the ambient `fderiv` corollary below, this theorem
does not ask the map to be defined differentiably outside the parameter
domain.-/
theorem strongMonotonicityOn_of_fderivWithin_lowerBound
    (Theta : Set E) (kappa : ℝ) (f : E → E)
    (hTheta : Convex ℝ Theta)
    (hdiff : DifferentiableOn ℝ f Theta)
    (hlower : ∀ x, x ∈ Theta → ∀ v,
      kappa * ‖v‖ ^ 2 ≤ ⟪fderivWithin ℝ f Theta x v, v⟫_ℝ) :
    StrongMonotonicityOn Theta kappa f := by
  exact strongMonotonicityOn_of_hasFDerivWithinAt Theta kappa f
    (fun x ↦ fderivWithin ℝ f Theta x) hTheta
    (fun x hx ↦ (hdiff x hx).hasFDerivWithinAt) hlower

/-- Uniform family version of the `fderivWithin` criterion.-/
theorem uniformStrongMonotonicityOn_of_fderivWithin_lowerBound
    (Theta : Set E) (kappa : ℝ) (g : P → E → E)
    (hTheta : Convex ℝ Theta)
    (hdiff : ∀ p, DifferentiableOn ℝ (g p) Theta)
    (hlower : ∀ p x, x ∈ Theta → ∀ v,
      kappa * ‖v‖ ^ 2 ≤ ⟪fderivWithin ℝ (g p) Theta x v, v⟫_ℝ) :
    UniformStrongMonotonicityOn Theta kappa g := by
  intro p
  exact strongMonotonicityOn_of_fderivWithin_lowerBound Theta kappa (g p)
    hTheta (hdiff p) (hlower p)

/-- Familiar Jacobian formulation: ambient differentiability at every point
of a convex parameter set and a lower bound on the quadratic form of `fderiv`
imply strong monotonicity on that set.

No continuity of `fderiv`, openness of `Theta`, or finite-dimensionality is
required.-/
theorem strongMonotonicityOn_of_fderiv_lowerBound
    (Theta : Set E) (kappa : ℝ) (f : E → E)
    (hTheta : Convex ℝ Theta)
    (hdiff : ∀ x, x ∈ Theta → DifferentiableAt ℝ f x)
    (hlower : ∀ x, x ∈ Theta → ∀ v,
      kappa * ‖v‖ ^ 2 ≤ ⟪fderiv ℝ f x v, v⟫_ℝ) :
    StrongMonotonicityOn Theta kappa f := by
  exact strongMonotonicityOn_of_hasFDerivWithinAt Theta kappa f
    (fun x ↦ fderiv ℝ f x) hTheta
    (fun x hx ↦ (hdiff x hx).hasFDerivAt.hasFDerivWithinAt) hlower

/-- Family form of the ambient `fderiv` criterion.-/
theorem uniformStrongMonotonicityOn_of_fderiv_lowerBound
    (Theta : Set E) (kappa : ℝ) (g : P → E → E)
    (hTheta : Convex ℝ Theta)
    (hdiff : ∀ p x, x ∈ Theta → DifferentiableAt ℝ (g p) x)
    (hlower : ∀ p x, x ∈ Theta → ∀ v,
      kappa * ‖v‖ ^ 2 ≤ ⟪fderiv ℝ (g p) x v, v⟫_ℝ) :
    UniformStrongMonotonicityOn Theta kappa g := by
  intro p
  exact strongMonotonicityOn_of_fderiv_lowerBound Theta kappa (g p)
    hTheta (hdiff p) (hlower p)

/-- Restrict an ambient uniformly strongly monotone family to the subtype
`Theta`, obtaining exactly the predicate used by the zero-set stability
theorems.-/
theorem uniformStrongMonotonicity_restrict
    (Theta : Set E) (kappa : ℝ) (g : P → E → E)
    (hmono : UniformStrongMonotonicityOn Theta kappa g) :
    UniformStrongMonotonicity Theta kappa
      (fun p theta ↦ g p (theta : E)) := by
  intro p theta theta'
  exact hmono p theta.property theta'.property

/-- Direct bridge from relative derivatives on `Theta` to the subtype
predicate consumed by the zero-set results.-/
theorem uniformStrongMonotonicity_restrict_of_hasFDerivWithinAt
    (Theta : Set E) (kappa : ℝ) (g : P → E → E)
    (Dg : P → E → E →L[ℝ] E)
    (hTheta : Convex ℝ Theta)
    (hderiv : ∀ p x, x ∈ Theta →
      HasFDerivWithinAt (g p) (Dg p x) Theta x)
    (hlower : UniformDerivativeLowerBoundOn Theta kappa Dg) :
    UniformStrongMonotonicity Theta kappa
      (fun p theta ↦ g p (theta : E)) :=
  uniformStrongMonotonicity_restrict Theta kappa g
    (uniformStrongMonotonicityOn_of_hasFDerivWithinAt
      Theta kappa g Dg hTheta hderiv hlower)

/-- Direct bridge from the intrinsic `fderivWithin` criterion to the subtype
predicate consumed by the zero-set results.-/
theorem uniformStrongMonotonicity_restrict_of_fderivWithin_lowerBound
    (Theta : Set E) (kappa : ℝ) (g : P → E → E)
    (hTheta : Convex ℝ Theta)
    (hdiff : ∀ p, DifferentiableOn ℝ (g p) Theta)
    (hlower : ∀ p x, x ∈ Theta → ∀ v,
      kappa * ‖v‖ ^ 2 ≤ ⟪fderivWithin ℝ (g p) Theta x v, v⟫_ℝ) :
    UniformStrongMonotonicity Theta kappa
      (fun p theta ↦ g p (theta : E)) :=
  uniformStrongMonotonicity_restrict Theta kappa g
    (uniformStrongMonotonicityOn_of_fderivWithin_lowerBound
      Theta kappa g hTheta hdiff hlower)

/-- Direct bridge from the Jacobian criterion of the report to
`UniformStrongMonotonicity` on the parameter subtype.-/
theorem uniformStrongMonotonicity_restrict_of_fderiv_lowerBound
    (Theta : Set E) (kappa : ℝ) (g : P → E → E)
    (hTheta : Convex ℝ Theta)
    (hdiff : ∀ p x, x ∈ Theta → DifferentiableAt ℝ (g p) x)
    (hlower : ∀ p x, x ∈ Theta → ∀ v,
      kappa * ‖v‖ ^ 2 ≤ ⟪fderiv ℝ (g p) x v, v⟫_ℝ) :
    UniformStrongMonotonicity Theta kappa
      (fun p theta ↦ g p (theta : E)) :=
  uniformStrongMonotonicity_restrict Theta kappa g
    (uniformStrongMonotonicityOn_of_fderiv_lowerBound
      Theta kappa g hTheta hdiff hlower)

end RandomSetTheory
