/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.Holomorphic
import Tengoku.Seed.Analysis.Meromorphic.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Foundations for analytic Laurent expansions

This uses a bilateral analytic `HasSum`; Mathlib's formal, well-ordered-support `LaurentSeries` is
not an analytic Laurent expansion. No general existence theorem on an annulus is claimed. -/

open Filter Metric Set Topology
open scoped Topology

namespace SandronesLibrary.ComplexAnalysis

/-- The open annulus.

> **Entry**: complex-analysis.series.laurent-foundation-/
def ComplexAnnulus (center : ℂ) (inner outer : ℝ) : Set ℂ :=
  {z | inner < dist z center ∧ dist z center < outer}

/-- Pointwise convergence of a bilateral analytic Laurent series.

> **Entry**: complex-analysis.series.laurent-foundation-/
def HasLaurentExpansionOnAnnulus (f : ℂ → ℂ) (center : ℂ)
    (inner outer : ℝ) (coeff : ℤ → ℂ) : Prop :=
  ∀ z ∈ ComplexAnnulus center inner outer,
    HasSum (fun n : ℤ ↦ coeff n * (z - center) ^ n) (f z)

/-- The constant function has a Laurent expansion supported at exponent zero.

> **Entry**: complex-analysis.series.laurent-foundation
@isnad1 id=haslaure.0h4v.s5.0c1b7aa97cbb from=translated src=- shape=6fa7ba04 vocab=4f042d11
-/
theorem hasLaurentExpansionOnAnnulus_const (c center : ℂ) (inner outer : ℝ) :
    HasLaurentExpansionOnAnnulus (fun _ ↦ c) center inner outer
      (fun n ↦ if n = 0 then c else 0) := by
  intro z hz
  convert hasSum_ite_eq (0 : ℤ) c using 1
  ext n
  split_ifs with hn
  · subst n; simp
  · simp [hn]

/-- A simple pole has a Laurent expansion supported at exponent negative one.

> **Entry**: complex-analysis.series.laurent-foundation
@isnad1 id=haslaure.1h3v.s6.09f7c4e6f1a1 from=translated src=- shape=e4e81b5b vocab=6d02906e
-/
theorem hasLaurentExpansionOnAnnulus_inv_sub (center : ℂ) {inner outer : ℝ}
    (hinner : 0 ≤ inner) :
    HasLaurentExpansionOnAnnulus (fun z ↦ (z - center)⁻¹) center inner outer
      (fun n ↦ if n = -1 then 1 else 0) := by
  intro z hz
  have hne : z - center ≠ 0 := sub_ne_zero.mpr (by
    intro h
    subst z
    simpa [ComplexAnnulus] using lt_of_le_of_lt hinner hz.1)
  convert hasSum_ite_eq (-1 : ℤ) ((z - center)⁻¹) using 1
  ext n
  split_ifs with hn
  · subst n; simp
  · simp [hn]

end SandronesLibrary.ComplexAnalysis
