/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.Goursat
import Tengoku.Seed.Analysis.Complex.CauchyIntegral
import Tengoku.Seed.MeasureTheory.Integral.CurveIntegral.Poincare

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Smooth homotopy invariance of holomorphic path integrals

This file proves homotopy invariance without assuming a primitive.  The analytic input is a
two-times continuously differentiable path homotopy whose image remains in the holomorphy domain.
The remaining bridge from an arbitrary topological path homotopy to such a smooth representative is
not currently supplied by Mathlib, so this module deliberately uses a foundation Entry id.

Current entry:

* `complex-analysis.cauchy.smooth-homotopy-foundation`.
-/

open Set Metric MeasureTheory AffineMap Filter Function
open scoped Interval unitInterval Topology

namespace SandronesLibrary.ComplexAnalysis

noncomputable section

/-- Two paths with the same endpoints are `C²`-homotopic within `U` if there is a relative-endpoint
homotopy whose image lies in `U` and whose standard extension to the real unit square is `C²`.
This records precisely the regularity required by the curve-integral Poincare theorem.

> **Entry**: complex-analysis.cauchy.smooth-homotopy-foundation-/
def C2HomotopicWithin {a b : ℂ} (U : Set ℂ) (gamma delta : Path a b) : Prop :=
  ∃ F : gamma.Homotopy delta,
    (∀ s t : I, F (s, t) ∈ U) ∧
      ContDiffOn ℝ 2
        (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (F.toHomotopy.extend xy.1) xy.2)
        (Icc 0 1)

private def smoothHomotopyOneForm (f : ℂ → ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)) ∘ f

private def scalarOneFormFDeriv (f : ℂ → ℂ) (z : ℂ) :
    ℂ →L[ℝ] ℂ →L[ℂ] ℂ :=
  ((ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).comp
    (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z))).restrictScalars ℝ

private theorem hasFDerivAt_smoothHomotopyOneForm {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    HasFDerivAt (smoothHomotopyOneForm f) (scalarOneFormFDeriv f z) z := by
  simpa [smoothHomotopyOneForm, scalarOneFormFDeriv] using
    ((ContinuousLinearMap.smulRightL ℂ ℂ ℂ
      (1 : ℂ →L[ℂ] ℂ)).hasFDerivAt.comp z hf.hasDerivAt.hasFDerivAt).restrictScalars ℝ

private theorem scalarOneFormFDeriv_symmetric (f : ℂ → ℂ) (z u v : ℂ) :
    scalarOneFormFDeriv f z u v = scalarOneFormFDeriv f z v u := by
  change v * (u * deriv f z) = u * (v * deriv f z)
  ring

/-- Path integrals of a textbook-holomorphic function are invariant under a `C²` path homotopy
inside the holomorphy domain.  No primitive is assumed: closedness of `f(z) dz` follows from complex
differentiability, and the two side paths of a relative-endpoint homotopy are constant.

> **Entry**: complex-analysis.cauchy.smooth-homotopy-foundation
@isnad1 id=eq.3h6v.s6.e6cb5e231f84 from=translated src=- shape=74e462c5 vocab=e295c73e
-/
theorem pathIntegral_eq_of_C2HomotopicWithin
    {f : ℂ → ℂ} {U : Set ℂ} {a b : ℂ} {gamma delta : Path a b}
    (hU : IsOpen U) (hf : HolomorphicOnTextbook f U)
    (hhom : C2HomotopicWithin U gamma delta) :
    pathIntegral f gamma = pathIntegral f delta := by
  obtain ⟨F, hFU, hF⟩ := hhom
  have hdiff : DifferentiableOn ℂ f U :=
    (holomorphicOnTextbook_iff_differentiableOn hU).mp hf
  let T : Set ℂ := range F
  have hTU : T ⊆ U := by
    rintro x ⟨⟨s, t⟩, rfl⟩
    exact hFU s t
  have hω : ∀ x ∈ T,
      HasFDerivWithinAt (smoothHomotopyOneForm f) (scalarOneFormFDeriv f x) T x :=
    fun x hx ↦ (hasFDerivAt_smoothHomotopyOneForm
      (hdiff.differentiableAt (hU.mem_nhds (hTU hx)))).hasFDerivWithinAt
  have hTclosed : IsClosed T := (isCompact_range F.continuous).isClosed
  have hωc : ContinuousOn (smoothHomotopyOneForm f) (closure T) := by
    rw [hTclosed.closure_eq]
    exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous.comp_continuousOn
      (hdiff.continuousOn.mono hTU)
  have hmain := F.toHomotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    (t := T) (dω := scalarOneFormFDeriv f)
    (fun s _ t _ ↦ mem_range_self (s, t)) hω hωc
    (fun x _ u _ v _ ↦ scalarOneFormFDeriv_symmetric f x u v) hF
  have hside0 : F.toHomotopy.evalAt 0 =
      (Path.refl a).cast gamma.source delta.source := by
    ext t
    exact F.source t
  have hside1 : F.toHomotopy.evalAt 1 =
      (Path.refl b).cast gamma.target delta.target := by
    ext t
    exact F.target t
  rw [hside0, hside1, curveIntegral_cast, curveIntegral_cast, curveIntegral_refl,
    curveIntegral_refl, add_zero] at hmain
  simpa [pathIntegral, scalarOneForm, smoothHomotopyOneForm] using hmain

/-- A smoothly null-homotopic loop has zero integral for every textbook-holomorphic integrand.

> **Entry**: complex-analysis.cauchy.smooth-homotopy-foundation
@isnad1 id=eq.3h4v.s6.302e140ef396 from=translated src=- shape=0ec51ba2 vocab=5308bcfd
-/
theorem pathIntegral_eq_zero_of_C2NullHomotopicWithin
    {f : ℂ → ℂ} {U : Set ℂ} {a : ℂ} {gamma : Path a a}
    (hU : IsOpen U) (hf : HolomorphicOnTextbook f U)
    (hhom : C2HomotopicWithin U gamma (.refl a)) :
    pathIntegral f gamma = 0 := by
  rw [pathIntegral_eq_of_C2HomotopicWithin hU hf hhom]
  simp [pathIntegral]

end

end SandronesLibrary.ComplexAnalysis
