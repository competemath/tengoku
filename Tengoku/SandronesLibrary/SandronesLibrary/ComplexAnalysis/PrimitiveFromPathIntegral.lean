/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.Holomorphic
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.PathIntegral
import Tengoku.Seed.Analysis.Calculus.AddTorsor.AffineMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Constructing a primitive from path-integral independence

This file isolates the analytic construction in the standard simply-connected-domain argument.
Once admissible path integrals depend only on their endpoints, integration from a fixed base point
produces a primitive.  Proving the required independence from topological simple connectedness is a
separate remaining bridge.

Current entry:

* `complex-analysis.cauchy.primitive-from-path-independence-foundation`.
-/

open Set Metric MeasureTheory AffineMap Filter Function
open scoped Interval unitInterval Topology

namespace SandronesLibrary.ComplexAnalysis

noncomputable section

/-- An admissible path is a finite concatenation of genuinely `C¹` paths which stay in `U` and
along which the scalar one-form `f(z) dz` is integrable.  Storing these facts on every piece makes
induction by concatenation available and excludes arbitrary continuous paths whose default
`derivWithin` would not support the fundamental theorem of calculus.

> **Entry**: complex-analysis.cauchy.primitive-from-path-independence-foundation-/
inductive AdmissiblePath (f : ℂ → ℂ) (U : Set ℂ) : {a b : ℂ} → Path a b → Prop
  | of_contDiffOn {a b : ℂ} (gamma : Path a b)
      (hrange : range gamma ⊆ U) (hintegrable : PathIntegrable f gamma)
      (hregular : ContDiffOn ℝ 1 gamma.extend (Icc 0 1)) : AdmissiblePath f U gamma
  | trans {a b c : ℂ} {gamma : Path a b} {delta : Path b c}
      (hgamma : AdmissiblePath f U gamma) (hdelta : AdmissiblePath f U delta) :
      AdmissiblePath f U (gamma.trans delta)

namespace AdmissiblePath

/--
@isnad1 id=le.1h5v.s6.fd50b895d7cf from=translated src=- shape=1f90139f vocab=2697920c
-/
theorem range_subset {f : ℂ → ℂ} {U : Set ℂ} {a b : ℂ} {gamma : Path a b}
    (hgamma : AdmissiblePath f U gamma) : range gamma ⊆ U := by
  induction hgamma with
  | of_contDiffOn _ hrange _ _ => exact hrange
  | trans hgamma hdelta ihgamma ihdelta =>
      rw [Path.trans_range]
      exact union_subset ihgamma ihdelta

/--
@isnad1 id=pathinte.1h5v.s5.2d905b051466 from=translated src=- shape=2a9f1f66 vocab=c6b5e7dd
-/
theorem pathIntegrable {f : ℂ → ℂ} {U : Set ℂ} {a b : ℂ} {gamma : Path a b}
    (hgamma : AdmissiblePath f U gamma) : PathIntegrable f gamma := by
  induction hgamma with
  | of_contDiffOn _ _ hintegrable _ => exact hintegrable
  | trans hgamma hdelta ihgamma ihdelta => exact ihgamma.trans ihdelta

end AdmissiblePath

/-- The integral of a function with a primitive along an admissible path is the difference of the
primitive at the endpoints.  The proof applies the fundamental theorem of calculus to each `C¹`
piece and then adds the resulting endpoint differences.

> **Entry**: complex-analysis.cauchy.primitive-from-path-independence-foundation
@isnad1 id=eq.2h6v.s6.ecf246108d7e from=translated src=- shape=e2116b05 vocab=1d991a39
-/
theorem pathIntegral_eq_sub_of_primitive_of_admissiblePath
    {f g : ℂ → ℂ} {U : Set ℂ} {a b : ℂ} {gamma : Path a b}
    (hgamma : AdmissiblePath f U gamma) (hg : ∀ z ∈ U, HasDerivAt g (f z) z) :
    pathIntegral f gamma = g b - g a := by
  induction hgamma with
  | of_contDiffOn gamma hrange hintegrable hregular =>
      rw [pathIntegral, curveIntegral_def]
      have hmaps : MapsTo gamma.extend (Icc (0 : ℝ) 1) U := by
        intro t ht
        exact hrange ⟨⟨t, ht⟩, by rw [Path.extend_apply _ ht]⟩
      have hcont : ContinuousOn (fun t : ℝ ↦ g (gamma.extend t)) (Icc 0 1) := by
        exact ContinuousOn.comp
          (fun z hz ↦ (hg z hz).continuousAt.continuousWithinAt)
          hregular.continuousOn hmaps
      have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
          HasDerivAt (fun t : ℝ ↦ g (gamma.extend t))
            (curveIntegralFun (scalarOneForm f) gamma t) t := by
        intro t ht
        have hinner : DifferentiableAt ℝ gamma.extend t :=
          ((hregular.differentiableOn one_ne_zero).mono Ioo_subset_Icc_self t ht).differentiableAt
            (Ioo_mem_nhds ht.1 ht.2)
        have houter := hg _ (hmaps ⟨ht.1.le, ht.2.le⟩)
        have hInhds : I ∈ nhds t := by
          exact mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self
        simpa [curveIntegralFun_def, derivWithin_of_mem_nhds hInhds,
          scalarOneForm, Function.comp_def, mul_comm] using
          (houter.comp_hasFDerivAt t hinner.hasFDerivAt).hasDerivAt
      simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        zero_le_one hcont hderiv hintegrable
  | trans hgamma hdelta ihgamma ihdelta =>
      rw [pathIntegral_trans f _ _ hgamma.pathIntegrable hdelta.pathIntegrable,
        ihgamma, ihdelta]
      abel

/-- Path integrals are endpoint-independent on `U` if any two admissible paths with the same
endpoints have equal integrals.

> **Entry**: complex-analysis.cauchy.primitive-from-path-independence-foundation-/
def PathIntegralIndependentOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ {a b : ℂ} (gamma delta : Path a b),
    AdmissiblePath f U gamma → AdmissiblePath f U delta →
      pathIntegral f gamma = pathIntegral f delta

/-- A primitive makes admissible path integrals depend only on their endpoints.

> **Entry**: complex-analysis.cauchy.primitive-from-path-independence-foundation
@isnad1 id=pathinte.1h3v.s6.90785d8c0d01 from=translated src=- shape=de03d0cd vocab=8e4df5b6
-/
theorem pathIntegralIndependentOn_of_primitive
    {f g : ℂ → ℂ} {U : Set ℂ} (hg : ∀ z ∈ U, HasDerivAt g (f z) z) :
    PathIntegralIndependentOn f U := by
  intro a b gamma delta hgamma hdelta
  rw [pathIntegral_eq_sub_of_primitive_of_admissiblePath hgamma hg,
    pathIntegral_eq_sub_of_primitive_of_admissiblePath hdelta hg]

/-- If every point can be reached from a fixed base point by an admissible path and admissible path
integrals depend only on endpoints, then integration from the base point defines a primitive of `f`
on `U`.

This is the analytic construction needed for the simply-connected-domain theorem.  The hypotheses
deliberately state the remaining global path problem instead of assuming a primitive in disguise.

> **Entry**: complex-analysis.cauchy.primitive-from-path-independence-foundation
@isnad1 id=ex.4h3v.s7.2eb9641bd55b from=translated src=- shape=1f10c54f vocab=8c8093f4
-/
theorem exists_primitive_of_pathIntegralIndependentOn
    {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ}
    (hU : IsOpen U) (hf : HolomorphicOnTextbook f U)
    (hpaths : ∀ z ∈ U, ∃ gamma : Path c z, AdmissiblePath f U gamma)
    (hind : PathIntegralIndependentOn f U) :
    ∃ g : ℂ → ℂ, ∀ z ∈ U, HasDerivAt g (f z) z := by
  classical
  let P : ∀ z : U, {gamma : Path c z.1 // AdmissiblePath f U gamma} := fun z ↦
    ⟨Classical.choose (hpaths z z.property), Classical.choose_spec (hpaths z z.property)⟩
  let g : ℂ → ℂ := fun z ↦ if hz : z ∈ U then pathIntegral f (P ⟨z, hz⟩).1 else 0
  refine ⟨g, fun z hz ↦ ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hz
  have hdiff : DifferentiableOn ℂ f U :=
    (holomorphicOnTextbook_iff_differentiableOn hU).mp hf
  have hωball : ContinuousOn (scalarOneForm f) (ball z r) := by
    exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ
      (1 : ℂ →L[ℂ] ℂ)).continuous.comp_continuousOn (hdiff.continuousOn.mono hball)
  have hsegDeriv : HasDerivAt (fun w ↦ pathIntegral f (.segment z w)) (f z) z := by
    have hF := HasFDerivWithinAt.curveIntegral_segment_source
      (𝕜 := ℂ) (convex_ball z r) hωball (mem_ball_self hr)
    have hFA := hF.hasFDerivAt (isOpen_ball.mem_nhds (mem_ball_self hr))
    simpa [pathIntegral, scalarOneForm] using hFA.hasDerivAt
  have heq : g =ᶠ[nhds z] fun w ↦ g z + pathIntegral f (.segment z w) := by
    filter_upwards [Metric.ball_mem_nhds z hr] with w hw
    have hwU : w ∈ U := hball hw
    have hsegRange : range (Path.segment z w) ⊆ U := by
      rintro q ⟨t, rfl⟩
      exact hball ((convex_ball z r).lineMap_mem (mem_ball_self hr) hw t.2)
    have hsegInt : PathIntegrable f (.segment z w) := by
      rw [PathIntegrable, curveIntegrable_segment]
      have hline : MapsTo (lineMap z w) (Icc (0 : ℝ) 1) (ball z r) :=
        fun _ ht ↦ (convex_ball z r).lineMap_mem (mem_ball_self hr) hw ht
      have hcont : ContinuousOn (fun t : ℝ ↦ (w - z) * f (lineMap z w t)) (Icc 0 1) := by
        simpa [Function.comp_def] using
          ((hdiff.continuousOn.mono hball).comp lineMap_continuous.continuousOn hline).const_mul
            (w - z)
      have hi : IntervalIntegrable (fun t : ℝ ↦ (w - z) * f (lineMap z w t)) volume 0 1 :=
        (show ContinuousOn (fun t : ℝ ↦ (w - z) * f (lineMap z w t)) [[0, 1]] by
          simpa [uIcc_of_le zero_le_one] using hcont).intervalIntegrable
      simpa [scalarOneForm] using hi
    have hsegRegular : ContDiffOn ℝ 1 (Path.segment z w).extend (Icc 0 1) := by
      apply (AffineMap.contDiff_lineMap z w).contDiffOn.congr
      intro t ht
      rw [Path.extend_apply _ ht]
      rfl
    have hPz := (P ⟨z, hz⟩).property
    have hPw := (P ⟨w, hwU⟩).property
    have hseg : AdmissiblePath f U (.segment z w) :=
      .of_contDiffOn _ hsegRange hsegInt hsegRegular
    have htrans : AdmissiblePath f U ((P ⟨z, hz⟩).1.trans (.segment z w)) :=
      .trans hPz hseg
    have hi := hind (P ⟨w, hwU⟩).1 ((P ⟨z, hz⟩).1.trans (.segment z w)) hPw htrans
    rw [pathIntegral_trans f _ _ hPz.pathIntegrable hsegInt] at hi
    simpa [g, hz, hwU] using hi
  exact (hsegDeriv.const_add (g z)).congr_of_eventuallyEq heq

end

end SandronesLibrary.ComplexAnalysis
