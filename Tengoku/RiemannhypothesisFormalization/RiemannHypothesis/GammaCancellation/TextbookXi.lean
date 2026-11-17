/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Tactic.Ring
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.Definitions
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.GammaCancellation.PoleSet
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.GammaCancellation.CompletedZeta

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# GammaCancellation.TextbookXi

The raw Γ-based completed-ξ function `completedXiFunction` and its behaviour at the
Γ-pole pullback. The textbook formula

  `ξ(s) = ½·s·(s−1)·π^(−s/2)·Γ(s/2)·ζ(s)`

carries the `Γ(s/2)` factor literally, so it *vanishes* at every Γ-pole pullback point,
and away from those points it agrees with Mathlib's entire `entireRiemannXi`.

## Main declarations

* `rawCompletedXiFormula`, `completedXiFunction_eq_rawFormula` — the formula, `rfl`.
* `completedXiVanishesOnGammaPolePullback` — raw ξ vanishes on the Γ-pole pullback.
* `completedXiNonzeroExcludesGammaPole` — contrapositive: nonzero raw ξ avoids Γ-poles.
* `completedXiRawEntireXiOffPolePointwiseFormula` — raw ξ `=` entire ξ off Γ-poles
  (away from `s = 1`), assembled from the `CompletedZeta` identities.
* `rawCompletedXiCorrectness` — the bundled unconditional correctness package.
-/

namespace OverflowResidueRH

open Complex

/-- **Raw completed-ξ formula** (matches `completedXiFunction` definition).-/
noncomputable def rawCompletedXiFormula (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1)
    * Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))
    * Complex.Gamma (s / 2)
    * riemannZeta s

/-- ⭐ **PROVED — `completedXiFunction = rawCompletedXiFormula` by `rfl`.**
@isnad1 id=eq.0h1v.s3.be09f6d86653 from=translated src=- shape=0fc427d2 vocab=d92dc9ab
-/
theorem completedXiFunction_eq_rawFormula (s : ℂ) :
    completedXiFunction s = rawCompletedXiFormula s := rfl

/-- ⭐ **PROVED — `completedXiFunction 1 = 0`.**
@isnad1 id=eq.0h0v.s3.280ccb0dea2f from=translated src=- shape=3c26ae4f vocab=4734eea1
-/
theorem completedXiFunction_one_eq_zero : completedXiFunction 1 = 0 := by
  unfold completedXiFunction
  ring

/-- 🌟🌟🌟 **PROVED — raw completed ξ vanishes when `s/2 = -n`.**
Direct application of `Complex.Gamma_neg_nat_eq_zero`.
@isnad1 id=eq.1h2v.s5.16efb8186e3f from=translated src=- shape=2cca160c vocab=6096d665
-/
theorem completedXiFunction_vanishes_of_half_eq_neg_nat
    {s : ℂ} {n : ℕ} (hs : s / 2 = -((n : ℂ))) :
    completedXiFunction s = 0 := by
  rw [completedXiFunction_eq_rawFormula]
  unfold rawCompletedXiFormula
  rw [hs, Complex.Gamma_neg_nat_eq_zero]
  ring

/-- 📦 **`CompletedXiVanishesOnGammaPolePullback`** — raw completed ξ
vanishes at Γ-pole-pullback points.-/
structure CompletedXiVanishesOnGammaPolePullback : Prop where
  vanishes :
    ∀ s : ℂ,
      s / 2 ∈ gammaPoleSet →
      completedXiFunction s = 0

/-- 🌟🌟🌟🌟 **PROVED unconditionally.**
@isnad1 id=complete.0h0v.s0.baa26094858f from=translated src=- shape=45709ebd vocab=baa26094
-/
theorem completedXiVanishesOnGammaPolePullback :
    CompletedXiVanishesOnGammaPolePullback := by
  refine ⟨?_⟩
  intro s hsPole
  obtain ⟨n, hn⟩ := hsPole
  exact completedXiFunction_vanishes_of_half_eq_neg_nat hn

/-- 📦 **`CompletedXiNonzeroExcludesGammaPole`** — at any nonzero
completed-ξ point, `s/2` is not a Γ pole.-/
structure CompletedXiNonzeroExcludesGammaPole : Prop where
  not_gamma_pole :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      s / 2 ∉ gammaPoleSet

/-- ⭐ **PROVED — nonzero exclusion from vanishing.**
@isnad1 id=complete.1h0v.s1.b8e3602a1977 from=translated src=- shape=1d48f1ac vocab=4572d0ca
-/
theorem CompletedXiNonzeroExcludesGammaPole.of_vanishes
    (H : CompletedXiVanishesOnGammaPolePullback) :
    CompletedXiNonzeroExcludesGammaPole := by
  refine ⟨?_⟩
  intro s hs hpole
  exact hs (H.vanishes s hpole)

/-- 🌟🌟 **PROVED — `CompletedXiNonzeroExcludesGammaPole`
unconditionally.**
@isnad1 id=complete.0h0v.s0.6f171ecf38e0 from=translated src=- shape=45709ebd vocab=6f171ecf
-/
theorem completedXiNonzeroExcludesGammaPole :
    CompletedXiNonzeroExcludesGammaPole :=
  CompletedXiNonzeroExcludesGammaPole.of_vanishes
    completedXiVanishesOnGammaPolePullback

/-- 📦 **`CompletedXiRawEntireXiOffPolePointwiseFormula`** — pointwise
off-pole identity. Requires `s ≠ 1` because `entireRiemannXi 1 = 1/2`
while `completedXiFunction 1 = 0` (the `+ 1/2` correction in
`entireRiemannXi`'s definition kicks in when the `s·(s-1)` factor
vanishes).-/
structure CompletedXiRawEntireXiOffPolePointwiseFormula : Prop where
  pointwise_eq :
    ∀ s : ℂ,
      s ≠ 1 →
      s / 2 ∉ gammaPoleSet →
      completedXiFunction s = entireRiemannXi s

/-- 🌟🌟 **PROVED — raw completed ξ formula in terms of
`completedRiemannZeta`** (off Γ poles).
@isnad1 id=eq.2h1v.s6.42db256ad074 from=translated src=- shape=f4d89ad0 vocab=0d3c2570
-/
theorem rawCompletedXiFormula_eq_completedZeta
    (HzetaRaw : CompletedRiemannZetaRawOffPoleFormula)
    {s : ℂ} (hsPole : s / 2 ∉ gammaPoleSet) :
    rawCompletedXiFormula s
      = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  unfold rawCompletedXiFormula
  rw [HzetaRaw.eq_raw s hsPole]
  ring

/-- 🌟🌟🌟 **PROVED — `CompletedXiRawEntireXiOffPolePointwiseFormula`
from zeta formula identities.**
@isnad1 id=complete.3h0v.s2.1c760a5f0eca from=translated src=- shape=b198369b vocab=56eceede
-/
theorem CompletedXiRawEntireXiOffPolePointwiseFormula.of_completedZetaIdentities
    (HzetaRaw : CompletedRiemannZetaRawOffPoleFormula)
    (Hzeta0 : CompletedRiemannZetaZeroCorrectionFormula)
    (Hxi : EntireRiemannXiFormulaSource) :
    CompletedXiRawEntireXiOffPolePointwiseFormula := by
  refine ⟨?_⟩
  intro s hs1 hsPole
  have hs0 : s ≠ 0 := by
    intro hs
    apply hsPole
    rw [hs]
    exact ⟨0, by simp⟩
  calc completedXiFunction s
      = rawCompletedXiFormula s := completedXiFunction_eq_rawFormula s
    _ = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s :=
        rawCompletedXiFormula_eq_completedZeta HzetaRaw hsPole
    _ = (1 / 2 : ℂ) * s * (s - 1)
          * (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) := by
        rw [Hzeta0.correction s]
    _ = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + 1 / 2 :=
        xi_completedZeta_correction_algebra hs0 hs1
    _ = entireRiemannXi s := (Hxi.formula s).symm

/-- 🌟🌟🌟🌟 **PROVED unconditionally** — the raw completed-ξ function
agrees pointwise with Mathlib's `entireRiemannXi` off Γ-poles and away
from `s = 1`.
@isnad1 id=complete.0h0v.s0.7970b2b34f1b from=translated src=- shape=45709ebd vocab=7970b2b3
-/
theorem completedXiRawEntireXiOffPolePointwiseFormula :
    CompletedXiRawEntireXiOffPolePointwiseFormula :=
  CompletedXiRawEntireXiOffPolePointwiseFormula.of_completedZetaIdentities
    completedRiemannZetaRawOffPoleFormula
    completedRiemannZetaZeroCorrectionFormula
    entireRiemannXiFormulaSource

/-- 📦 **`RawCompletedXiCorrectness`** — bundles the two Γ-cancellation
facts: nonzero raw ξ avoids Γ-poles, and the off-pole pointwise formula
identity (stated with the `s ≠ 1` exclusion inline).-/
structure RawCompletedXiCorrectness : Prop where
  nonzero_excludes_gammaPole : CompletedXiNonzeroExcludesGammaPole
  offPole_eq :
    ∀ s : ℂ,
      s ≠ 1 →
      s / 2 ∉ gammaPoleSet →
      completedXiFunction s = entireRiemannXi s

/-- 🌟🌟 **PROVED — `RawCompletedXiCorrectness` from the two
pointwise formula targets.**
@isnad1 id=rawcompl.2h0v.s2.89e84b87bf97 from=translated src=- shape=f443e7c7 vocab=ef4fb233
-/
theorem RawCompletedXiCorrectness.of_pointwise
    (Hvanish : CompletedXiVanishesOnGammaPolePullback)
    (Hformula : CompletedXiRawEntireXiOffPolePointwiseFormula) :
    RawCompletedXiCorrectness :=
  { nonzero_excludes_gammaPole :=
      CompletedXiNonzeroExcludesGammaPole.of_vanishes Hvanish
    offPole_eq := Hformula.pointwise_eq }

/-- 🌟🌟🌟🌟 **PROVED unconditionally** — the complete raw completed-ξ
correctness package.
@isnad1 id=rawcompl.0h0v.s0.d4aba89642da from=translated src=- shape=45709ebd vocab=d4aba896
-/
theorem rawCompletedXiCorrectness :
    RawCompletedXiCorrectness :=
  RawCompletedXiCorrectness.of_pointwise
    completedXiVanishesOnGammaPolePullback
    completedXiRawEntireXiOffPolePointwiseFormula

end OverflowResidueRH
