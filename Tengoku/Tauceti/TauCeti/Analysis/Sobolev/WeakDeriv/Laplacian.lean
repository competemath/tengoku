/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Tengoku
import Tengoku.Tauceti.TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The Laplacian against test functions

For a `C²` function `u` on an open set `Ω` of a finite-dimensional real inner product space and a
test function `φ ∈ 𝓓(Ω)`, integrating by parts twice in each coordinate direction gives Green's
second identity in the boundary-free form

`∫ Δφ • u ∂μ = ∫ φ • Δu ∂μ`,

for any additive Haar measure `μ`: the classical Laplacian of a `C²` function is its distributional
Laplacian on `Ω`. In particular a function harmonic on `Ω` is *weakly harmonic*: `∫ Δφ • u = 0` for
every test function `φ` on `Ω`. This is the form in which harmonicity enters integral arguments
such as the mean-value property, where the test functions are radial.

The two integrations by parts are the defining identities of the weak derivative
`TauCeti.HasWeakLineDerivOn`, applied to `u` and to its first directional derivative, both of
which are classical derivatives and hence weak ones
(`TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt`). No boundary term appears because the test
function is compactly supported in `Ω`, and no regularity of `∂Ω` is used.

## Main declarations

* `ContDiffOn.integral_fderiv_fderiv_smul_eq_integral_smul_fderiv_fderiv`: second-order
  integration by parts in one direction, `∫ ∂ᵥ∂ᵥφ • u = ∫ φ • ∂ᵥ∂ᵥu`.
* `ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian`: Green's second identity
  against a test function, `∫ Δφ • u = ∫ φ • Δu`.
* `InnerProductSpace.HarmonicOnNhd.integral_laplacian_smul_eq_zero`: a harmonic function is
  weakly harmonic.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory TopologicalSpace
open scoped Distributions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {u : E → F}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The directional derivative of a test function, as a test function, is its classical
directional derivative. -/
private lemma coe_lineDerivCLM (φ : 𝓓(Ω, ℝ)) (v : E) :
    ((TestFunction.lineDerivCLM ℝ v φ : 𝓓(Ω, ℝ)) : E → ℝ) =
      fun x ↦ lineDeriv ℝ (φ : E → ℝ) x v :=
  funext fun _ ↦ TestFunction.lineDerivCLM_apply_of_le le_top

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The iterated line derivative of a smooth test function in a fixed direction is the iterated
Fréchet derivative applied to that direction. -/
private lemma lineDeriv_lineDeriv_testFunction (φ : 𝓓(Ω, ℝ)) (v x : E) :
    lineDeriv ℝ (fun y ↦ lineDeriv ℝ (φ : E → ℝ) y v) x v =
      fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → ℝ) y v) x v := by
  have hφ1 : ∀ y, lineDeriv ℝ (φ : E → ℝ) y v = fderiv ℝ (φ : E → ℝ) y v := fun y ↦
    (φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv
  simp_rw [hφ1]
  exact (((φ.contDiff.fderiv_right (by simp)).clm_apply contDiff_const).differentiable
    one_ne_zero x).lineDeriv_eq_fderiv

/-- **Second-order integration by parts against a test function**, in one direction `v`. For
`u` of class `C²` on the open set `Ω` and a test function `φ` on `Ω`,
`∫ ∂ᵥ∂ᵥφ • u = ∫ φ • ∂ᵥ∂ᵥu`. -/
theorem _root_.ContDiffOn.integral_fderiv_fderiv_smul_eq_integral_smul_fderiv_fderiv
    (hu : ContDiffOn ℝ 2 u Ω) (φ : 𝓓(Ω, ℝ)) (v : E) :
    ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → ℝ) y v) x v • u x ∂μ =
      ∫ x, (φ : E → ℝ) x • fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v ∂μ := by
  have hΩ : IsOpen (Ω : Set E) := Ω.isOpen
  set g : E → F := fun y ↦ fderiv ℝ u y v with hg_def
  have hu1 : ContDiffOn ℝ 1 (fderiv ℝ u) Ω := hu.fderiv_of_isOpen hΩ (by norm_num)
  have hg : ContDiffOn ℝ 1 g Ω := hu1.clm_apply contDiffOn_const
  have hu_loc : LocallyIntegrableOn u Ω μ := hu.continuousOn.locallyIntegrableOn hΩ.measurableSet
  have hg_loc : LocallyIntegrableOn g Ω μ := hg.continuousOn.locallyIntegrableOn hΩ.measurableSet
  have hg'_loc : LocallyIntegrableOn (fun x ↦ fderiv ℝ g x v) Ω μ :=
    (hu.continuousOn_fderiv_fderiv_apply hΩ v).locallyIntegrableOn hΩ.measurableSet
  -- Both `u` and `∂ᵥu` are classically, hence weakly, differentiable on `Ω`.
  have h1 : HasWeakLineDerivOn μ Ω u g v :=
    hasWeakLineDerivOn_of_hasLineDerivAt hu_loc hg_loc fun x hx ↦
      ((hu.differentiableOn (by norm_num)).differentiableAt
        (hΩ.mem_nhds hx)).hasFDerivAt.hasLineDerivAt v
  have h2 : HasWeakLineDerivOn μ Ω g (fun x ↦ fderiv ℝ g x v) v :=
    hasWeakLineDerivOn_of_hasLineDerivAt hg_loc hg'_loc fun x hx ↦
      ((hg.differentiableOn one_ne_zero).differentiableAt
        (hΩ.mem_nhds hx)).hasFDerivAt.hasLineDerivAt v
  have e1 := h1.integral_lineDeriv_smul_eq_neg_integral_smul (TestFunction.lineDerivCLM ℝ v φ)
  have e2 := h2.integral_lineDeriv_smul_eq_neg_integral_smul φ
  rw [coe_lineDerivCLM] at e1
  simp_rw [lineDeriv_lineDeriv_testFunction] at e1
  have hφ1 : ∀ y, lineDeriv ℝ (φ : E → ℝ) y v = fderiv ℝ (φ : E → ℝ) y v := fun y ↦
    (φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv
  simp_rw [hφ1] at e1 e2
  rw [e1, e2, neg_neg]

end TauCeti
