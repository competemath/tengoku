/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.Pairing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The kernels of a cascade family, and the positivity of their transforms

Home: line:lem:convolution-representation, lem:nonvanishing

Blueprint: `blueprint/src/parts/04-representation.tex` and `05-cascade.tex`.

What Chapters 5 and 6 actually consume from Chapter 4 is not the *existence* half of
`lem:convolution-representation` — that is supplied to every statement as the hypothesis
`IsKernelFamily` — but four consequences of its **uniqueness** half, together with
`lem:nonvanishing`:

* `kernel_symmetric` — the kernels are symmetric, which is (A3) read through uniqueness;
* `kernel_conv` — the cascade law at the level of measures, which is (A6) read through it;
* `kernel_diag` — `μ_{t,t} = δ₀`;
* `kernel_ne_dirac` — (ND) at the level of measures;
* `kernel_transform_pos` — the transform never vanishes.

## What the wave-1 merge did with this file

All five were proved twice: here for chapters 5 and 6, and in `Nonvanishing`
for `lem:nonvanishing`, whose own proof needs the same consequences of uniqueness. The merge of
2026-09-09 kept the copies in `Nonvanishing.lean` — the file that proves the node the facts
belong to — and left three one-line adapters here, because two of the surviving statements are
in a different but equivalent form and one node's statement fixes the form it needs:

* `kernel_symmetric` is `isSymmetric_kernel` with the `IsProbabilityMeasure` instance supplied
  from `IsKernelFamily.isProbability` instead of taken as an instance argument;
* `kernel_conv_comm` is `kernel_conv` with the factors commuted, because `lem:additivity`'s
  reviewed statement writes the cascade law as `μ_{r,t} = μ_{s,t} ∗ μ_{r,s}` and a node
  statement is not rewritten to suit a lemma;
* `fourierCos_kernel_mul_comm` likewise;
* `kernel_transform_pos` is `lem:nonvanishing`'s own declaration, `ScaleSpace.nonvanishing`,
  applied. Chapters 5 and 6 do **not** stand apart from chapter 4: `lem:additivity`,
  `cor:monotonicity`, `cor:smoothed-transmittance` and `lem:covariance-fourier` all consume the
  nonvanishing node and the uniqueness clause of the representation, and the import of
  `ScaleSpace.Nonvanishing` now records that. It corrects `SKELETON.md` F4.

The sixty-line proof this file carried for `kernel_transform_pos` — the least-zero argument on
`[s,t]` with joint continuity of `(s,t) ↦ μ̂_{s,t}(ω)` at the end — is therefore gone; the
surviving proof of the same statement is in `Nonvanishing.lean`, and it is the blueprint's.

## Provenance

Moved by Q-0305 from Paper V's `SpatialLine/Cascade.lean` (the public cone export,
`cone-v0.1`, commit `f28c066e`) for the line classification (`MainAnalysis`,
`MainConstruction`): only the declarations those theorems reach, with statements and
proofs unchanged up to the namespace. Blueprint labels are Paper V's.
-/

namespace ScaleSpace

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology

/-! ## The representation, at the level of the family -/

/-! ## What the representation's uniqueness clause gives -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

/-- **(ND) at the level of measures**: strictly below the diagonal the kernel is not `δ₀`.
@isnad1 id=ne.4h4v.s5.9a05f28fc7e3 from=translated src=- shape=f1b367e6 vocab=0e04b520
-/
theorem kernel_ne_dirac (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) : μ s t ≠ Measure.dirac 0 := by
  intro hcon
  refine hnd s t hs hst ?_
  refine ContinuousLinearMap.ext fun f => ?_
  refine Lp.ext_iff.mpr ?_
  refine (hker.conv s t hs hst.le f).trans ?_
  rw [hcon, mconv_dirac_zero]
  simp

/-! ## The transform along the cascade -/

/-- **The transform is multiplicative along the cascade**, with the factors in the order the
chapter-5 statements read them.
@isnad1 id=eq.4h6v.s6.0580afce6d43 from=translated src=- shape=ca477f2f vocab=62d7d705
-/
theorem fourierCos_kernel_mul_comm (hker : IsKernelFamily Fam.Φ μ) {r s t : ℝ} (hr : 0 ≤ r)
    (hrs : r ≤ s) (hst : s ≤ t) (ω : ℝ) :
    fourierCos (μ r t) ω = fourierCos (μ s t) ω * fourierCos (μ r s) ω := by
  rw [fourierCos_kernel_mul hker hr hrs hst ω, mul_comm]

/-! ## Joint continuity of the transform, from (A7) -/

/-! ## `lem:nonvanishing`, the nonvanishing clause -/

/-- **The transform of a kernel is strictly positive at every frequency** — `lem:nonvanishing`,
applied at the hypotheses chapters 5 and 6 carry. The node's own declaration is
`ScaleSpace.nonvanishing` in `Nonvanishing`; this is the name the later
chapters cite it by.
@isnad1 id=lt.3h5v.s5.6805070a38ec from=translated src=- shape=4714f211 vocab=93dc23e8
-/
theorem kernel_transform_pos (hker : IsKernelFamily Fam.Φ μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ω : ℝ) : 0 < fourierCos (μ s t) ω :=
  nonvanishing Fam μ hker hs hst ω

end ScaleSpace
