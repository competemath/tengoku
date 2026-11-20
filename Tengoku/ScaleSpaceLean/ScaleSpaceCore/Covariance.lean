/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.Transmittance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `lem:covariance-fourier`: (A8) as an identity of measures and of exponents

Home: line:lem:covariance-fourier

Blueprint: `blueprint/src/parts/06-covariance.tex`, `lem:covariance-fourier`.

The compatibility `D_λ(μ * f) = (D_λ μ) * (D_λ f)` turns (A8) into the statement that
`D_λ μ_{s,t}` and `μ_{S_λ s, S_λ t}` represent the same operator, and the uniqueness clause of
`lem:convolution-representation` makes that an identity of measures; the exponent form is
`(D_λ μ)^(ω) = μ̂(λω)` and `-log`.

twin: `Hemigroup.CascadeCore.covariance_laplace`.

## The two narrowings, recorded rather than silently taken

The blueprint states the three-way equivalence under (A1)–(A5), with clause (3) carrying
"whenever the exponents exist", because (A1)–(A5) alone do not give `lem:nonvanishing`. The Lean
statement takes `PreCascadeCore` — which carries (A6)–(A7) — plus a kernel family, and clause
(3) is unconditional; the (A1)–(A5)-only version is not stated because nothing consumes it
(finding **F5**). And the equivalence is stated on the `scale` field of `IsScaleCovariant` with
the three `S`-shape fields as hypotheses, since those are conditions on `S` alone and are shared
by all three clauses.

## Provenance

Moved by Q-0305 from Paper V's `SpatialLine/Covariance.lean` (the public cone export,
`cone-v0.1`, commit `f28c066e`) for the line classification (`MainAnalysis`,
`MainConstruction`): only the declarations those theorems reach, with statements and
proofs unchanged up to the namespace. Blueprint labels are Paper V's.
-/

namespace ScaleSpace

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology

/-! ## Dilation of a measure, against `mconv` -/

/-- **The compatibility of dilation with convolution**, at the level of functions:
`(D_λ ν) * f = D_λ (ν * D_{λ⁻¹} f)`. The measurable-embedding form of `integral_map` is used, so
no measurability of `f` is needed — which matters, because `f` is an `L¹` representative at
every use.
@isnad1 id=eq.1h4v.s5.f13ee79bb90e from=translated src=- shape=d62b2ae7 vocab=5f267356
-/
lemma mconv_map_mul (ν : Measure ℝ) {lam : ℝ} (hlam : 0 < lam) (f : ℝ → ℝ) (x : ℝ) :
    mconv (ν.map (fun y => lam * y)) f x = dilate lam (mconv ν (dilate lam⁻¹ f)) x := by
  rw [mconv_apply, (measurableEmbedding_mulLeft₀ hlam.ne').integral_map]
  simp only [dilate, mconv_apply, inv_inv]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  have hy : lam * (lam⁻¹ * x - y) = x - lam * y := by field_simp
  rw [hy, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]

/-- Dilations compose.
@isnad1 id=eq.0h3v.s4.9bc38abb8c52 from=translated src=- shape=0b16d896 vocab=fc3272dd
-/
lemma dilate_dilate (lam κ : ℝ) (f : ℝ → ℝ) :
    dilate lam (dilate κ f) = dilate (lam * κ) f := by
  funext x
  simp only [dilate]
  rw [mul_inv, ← mul_assoc]
  congr 2
  ring

/--
@isnad1 id=eq.0h1v.s4.f315fbb453b4 from=translated src=- shape=d11dff22 vocab=b0050396
-/
@[simp] lemma dilate_one (f : ℝ → ℝ) : dilate 1 f = f := by
  funext x
  simp [dilate]

/-- `D_{λ⁻¹}` undoes `D_λ`.
@isnad1 id=eq.1h2v.s4.90dcf193ac9b from=translated src=- shape=c67ef9ed vocab=ecdd4950
-/
lemma dilate_inv_dilate {lam : ℝ} (hlam : lam ≠ 0) (f : ℝ → ℝ) :
    dilate lam⁻¹ (dilate lam f) = f := by
  rw [dilate_dilate, inv_mul_cancel₀ hlam, dilate_one]

/-- `D_λ` undoes `D_{λ⁻¹}`.
@isnad1 id=eq.1h2v.s4.bb95a8ed0a96 from=translated src=- shape=313cb008 vocab=ecdd4950
-/
lemma dilate_dilate_inv {lam : ℝ} (hlam : lam ≠ 0) (f : ℝ → ℝ) :
    dilate lam (dilate lam⁻¹ f) = f := by
  rw [dilate_dilate, mul_inv_cancel₀ hlam, dilate_one]

/-- The transform of a dilated measure.
@isnad1 id=eq.1h3v.s5.56ee3540ae27 from=translated src=- shape=c28dc8ce vocab=45298e55
-/
lemma fourierCos_map_mul (ν : Measure ℝ) {lam : ℝ} (hlam : lam ≠ 0) (ω : ℝ) :
    fourierCos (ν.map (fun y => lam * y)) ω = fourierCos ν (lam * ω) := by
  rw [fourierCos_apply, fourierCos_apply, (measurableEmbedding_mulLeft₀ hlam).integral_map]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  congr 1
  ring

/-! ## `lem:covariance-fourier` -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

end ScaleSpace
