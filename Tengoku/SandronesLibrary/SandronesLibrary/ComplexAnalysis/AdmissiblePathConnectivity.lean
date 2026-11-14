/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.PrimitiveFromPathIntegral
import Tengoku.Seed.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Tengoku.Seed.Topology.Connected.Clopen

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Admissible paths in open connected domains

This file proves that every point of an open connected complex domain can be reached from a fixed
base point by a path along which a continuous integrand is curve-integrable.  The proof uses a
clopen reachable-set argument and constructs paths by adjoining short line segments in balls.

Current entry:

* `complex-analysis.cauchy.admissible-path-connectivity-foundation`.
-/

open Set Metric MeasureTheory AffineMap Filter Function
open scoped Interval unitInterval Topology

namespace SandronesLibrary.ComplexAnalysis

private theorem admissiblePath_segment_of_ball
    {f : ℂ → ℂ} {U : Set ℂ} {center z w : ℂ} {r : ℝ}
    (hf : ContinuousOn f U) (hball : ball center r ⊆ U)
    (hz : z ∈ ball center r) (hw : w ∈ ball center r) :
    AdmissiblePath f U (.segment z w) := by
  have hline : MapsTo (lineMap z w) (Icc (0 : ℝ) 1) (ball center r) :=
    fun _ ht ↦ (convex_ball center r).lineMap_mem hz hw ht
  apply AdmissiblePath.of_contDiffOn
  · rintro q ⟨t, rfl⟩
    exact hball (hline t.2)
  · rw [PathIntegrable, curveIntegrable_segment]
    have hcont : ContinuousOn (fun t : ℝ ↦ (w - z) * f (lineMap z w t)) (Icc 0 1) := by
      simpa [Function.comp_def] using
        ((hf.mono hball).comp lineMap_continuous.continuousOn hline).const_mul (w - z)
    have hi : IntervalIntegrable (fun t : ℝ ↦ (w - z) * f (lineMap z w t)) volume 0 1 :=
      (show ContinuousOn (fun t : ℝ ↦ (w - z) * f (lineMap z w t)) [[0, 1]] by
        simpa [uIcc_of_le zero_le_one] using hcont).intervalIntegrable
    simpa [scalarOneForm] using hi
  · apply (AffineMap.contDiff_lineMap z w).contDiffOn.congr
    intro t ht
    rw [Path.extend_apply _ ht]
    rfl

/-- In an open preconnected set, every point can be reached from a fixed member by an admissible
path for any continuous integrand.

> **Entry**: complex-analysis.cauchy.admissible-path-connectivity-foundation
@isnad1 id=ex.5h4v.s7.de5a38ecc85b from=translated src=- shape=76b759f0 vocab=7d1f0a5b
-/
theorem exists_admissiblePath_of_isPreconnected
    {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hc : c ∈ U)
    (hconn : IsPreconnected U) :
    ∀ z ∈ U, ∃ gamma : Path c z, AdmissiblePath f U gamma := by
  let R : Set ℂ := {z | ∃ gamma : Path c z, AdmissiblePath f U gamma}
  have hcR : c ∈ R := by
    refine ⟨.refl c, ?_⟩
    apply AdmissiblePath.of_contDiffOn
    · simpa using hc
    · simp [PathIntegrable]
    · apply (show ContDiffOn ℝ 1 (fun _ : ℝ ↦ c) (Icc 0 1) by fun_prop).congr
      intro t ht
      rw [Path.extend_apply _ ht]
      rfl
  have hRU : R ⊆ U := by
    rintro z ⟨gamma, hgamma⟩
    exact hgamma.range_subset ⟨1, gamma.target⟩
  have hRopen : IsOpen R := by
    rw [Metric.isOpen_iff]
    rintro z ⟨gamma, hgamma⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z (hRU ⟨gamma, hgamma⟩)
    refine ⟨r, hr, fun w hw ↦ ?_⟩
    have hseg := admissiblePath_segment_of_ball hf hball (mem_ball_self hr) hw
    refine ⟨gamma.trans (.segment z w), ?_⟩
    exact hgamma.trans hseg
  let V : Set ℂ := U \ R
  have hVopen : IsOpen V := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzU, hzR⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hzU
    refine ⟨r, hr, fun w hw ↦ ⟨hball hw, ?_⟩⟩
    intro hwR
    rcases hwR with ⟨gamma, hgamma⟩
    have hseg := admissiblePath_segment_of_ball hf hball hw (mem_ball_self hr)
    apply hzR
    refine ⟨gamma.trans (.segment w z), ?_⟩
    exact hgamma.trans hseg
  have hUR : U ⊆ R := by
    apply hconn.subset_left_of_subset_union hRopen hVopen
    · exact disjoint_sdiff_right
    · intro z hz
      by_cases hzR : z ∈ R
      · exact Or.inl hzR
      · exact Or.inr ⟨hz, hzR⟩
    · exact ⟨c, hc, hcR⟩
  intro z hz
  exact hUR hz

/-- On an open preconnected domain, endpoint-independence alone now suffices for a holomorphic
function to have a primitive: admissible paths from the base point are supplied automatically.

> **Entry**: complex-analysis.cauchy.admissible-path-connectivity-foundation
@isnad1 id=ex.5h3v.s6.918c45941e58 from=translated src=- shape=3134dff9 vocab=30e17a59
-/
theorem exists_primitive_of_isPreconnected_of_pathIntegralIndependentOn
    {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ}
    (hU : IsOpen U) (hf : HolomorphicOnTextbook f U) (hc : c ∈ U)
    (hconn : IsPreconnected U) (hind : PathIntegralIndependentOn f U) :
    ∃ g : ℂ → ℂ, ∀ z ∈ U, HasDerivAt g (f z) z := by
  have hdiff : DifferentiableOn ℂ f U :=
    (holomorphicOnTextbook_iff_differentiableOn hU).mp hf
  exact exists_primitive_of_pathIntegralIndependentOn hU hf
    (exists_admissiblePath_of_isPreconnected hU hdiff.continuousOn hc hconn) hind

/-- For a standard simply connected open set, the reachability hypothesis in the path-integral
construction is automatic.  Thus path-integral independence is the only remaining hypothesis.

> **Entry**: complex-analysis.cauchy.admissible-path-connectivity-foundation
@isnad1 id=ex.4h2v.s6.be1960126697 from=translated src=- shape=7406aa6c vocab=dd7a4c8d
-/
theorem exists_primitive_of_isSimplyConnected_of_pathIntegralIndependentOn
    {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : HolomorphicOnTextbook f U)
    (hconn : IsSimplyConnected U) (hind : PathIntegralIndependentOn f U) :
    ∃ g : ℂ → ℂ, ∀ z ∈ U, HasDerivAt g (f z) z := by
  obtain ⟨c, hc⟩ := hconn.nonempty
  exact exists_primitive_of_isPreconnected_of_pathIntegralIndependentOn
    hU hf hc hconn.isPathConnected.isConnected.isPreconnected hind

end SandronesLibrary.ComplexAnalysis
