/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ComplexAnalysis.LogDerivative
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.Definitions
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.Pullback
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.LogDerivative
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.XiLimitData
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.EntireXi
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.GammaCancellation.EntireXiBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# HadamardProduct.CompletedXi

The Hadamard log-derivative *source* interfaces for the completed ξ and its critical-line
pullback `Λ[Ξ]`, and the chain-rule bridge between them. A "source" bundles a candidate
zero-contribution function together with the identity `logDerivativeResponse = zeroContribution`
(away from zeros, where the Hadamard sum converges); concrete inhabitants come from the
Hadamard product factorization. Identity content only.

## Main declarations (clean names; legacy `…AFZ` aliases in `Deprecated/LegacyNames`)

* `XiPullback.HadamardLogDerivSource` / `…AwayFromZeros` — z-plane source, unguarded /
  away-from-zeros (was `XiHadamardLogDerivativeSource` / `…AFZ`).
* `CompletedXi.LogDerivSourceAwayFromZeros` — ξ-side (s-plane) source
  (was `CompletedXiLogDerivativeSourceAFZ`).
* `pullbackZeroContribution` — pull the ξ-side contribution to the z-plane (`Λ[Ξ] = I·Λ[ξ]`).
* `XiPullback.HadamardLogDerivSourceAwayFromZeros.of_completedXi` — z-plane source from the
  ξ-side source via the chain rule.
* `CompletedXi.HadamardProductData` — the Hadamard-product identification data.
-/

namespace OverflowResidueRH

/-- 📦 **z-plane Hadamard log-derivative source.** `Λ[Ξ] z = zeroContribution z` on the
upper half-plane, where `zeroContribution` is the regularized zero sum. Abstract here to
keep the interface independent of the specific factorization.-/
structure XiPullback.HadamardLogDerivSource : Type where
  zeroContribution : ℂ → ℂ
  logDeriv_eq_zeroContribution :
    ∀ z : ℂ,
      0 < z.im →
      logDerivativeResponse XiPullback z = zeroContribution z

/-- 📦 **z-plane Hadamard log-derivative source, away from zeros.** As
`XiPullback.HadamardLogDerivSource`, but the identity is only required where
`XiPullback z ≠ 0` — the mathematically inhabitable guard (at zeros the Lean-totalized
`logDerivativeResponse` is `0` while the Hadamard sum diverges).-/
structure XiPullback.HadamardLogDerivSourceAwayFromZeros : Type where
  zeroContribution : ℂ → ℂ
  logDeriv_eq_zeroContribution :
    ∀ z : ℂ,
      0 < z.im →
      XiPullback z ≠ 0 →
      logDerivativeResponse XiPullback z = zeroContribution z

/-- ⭐ **PROVED — away-from-zeros source from the unguarded source.** The trivial
direction: drop the AFZ hypothesis.-/
def XiPullback.HadamardLogDerivSourceAwayFromZeros.of_unguarded
    (H : XiPullback.HadamardLogDerivSource) :
    XiPullback.HadamardLogDerivSourceAwayFromZeros :=
  { zeroContribution := H.zeroContribution
    logDeriv_eq_zeroContribution := by
      intro z hy _hne
      exact H.logDeriv_eq_zeroContribution z hy }

/-- 📦 **ξ-side (s-plane) Hadamard log-derivative source, away from zeros.** Carries the
zero contribution together with differentiability of `completedXiFunction` and the
log-derivative identity, both guarded by `completedXiFunction s ≠ 0`.-/
structure CompletedXi.LogDerivSourceAwayFromZeros : Type where
  xiZeroContribution : ℂ → ℂ
  xi_diff_at :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      DifferentiableAt ℂ completedXiFunction s
  xi_logDeriv_eq :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      logDerivativeResponse completedXiFunction s = xiZeroContribution s

/-- **Pullback of the ξ-side zero contribution to the z-plane.**
`Λ[Ξ] = I · Λ[ξ](½ + I·z)` from the chain rule.-/
noncomputable def pullbackZeroContribution
    (H : CompletedXi.LogDerivSourceAwayFromZeros) : ℂ → ℂ :=
  fun z => Complex.I * H.xiZeroContribution ((1 / 2 : ℂ) + Complex.I * z)

/-- 🌟🌟🌟 **PROVED — z-plane away-from-zeros source from the ξ-side source via the
chain rule.**-/
noncomputable def XiPullback.HadamardLogDerivSourceAwayFromZeros.of_completedXi
    (H : CompletedXi.LogDerivSourceAwayFromZeros) :
    XiPullback.HadamardLogDerivSourceAwayFromZeros :=
  { zeroContribution := pullbackZeroContribution H
    logDeriv_eq_zeroContribution := by
      intro z _hy hne
      have hs_ne :
          completedXiFunction ((1 / 2 : ℂ) + Complex.I * z) ≠ 0 := by
        unfold XiPullback at hne
        exact hne
      have hxi_diff := H.xi_diff_at _ hs_ne
      have hchain := XiPullback_logDeriv_chain_rule hxi_diff
      have h_logderiv := H.xi_logDeriv_eq _ hs_ne
      unfold logDerivativeResponse at h_logderiv
      rw [hchain]
      unfold pullbackZeroContribution
      rw [h_logderiv] }

/-- 📦 **Completed-ξ Hadamard product data.** The Hadamard-product identification of
`logDerivativeResponse completedXiFunction` on the non-zero set:

```
ξ(s) = ξ(0) · ∏_ρ E₁(s/ρ)  ⟹  ξ'(s)/ξ(s) = Σ_ρ (1/(s−ρ) + 1/ρ)   (away from zeros)
```-/
structure CompletedXi.HadamardProductData : Type where
  xiZeroContribution : ℂ → ℂ
  xi_diff_at :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      DifferentiableAt ℂ completedXiFunction s
  logDeriv_eq :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      logDerivativeResponse completedXiFunction s = xiZeroContribution s

/-- ⭐ **PROVED — ξ-side away-from-zeros source from Hadamard product data.**-/
def CompletedXi.LogDerivSourceAwayFromZeros.of_hadamardProductData
    (H : CompletedXi.HadamardProductData) :
    CompletedXi.LogDerivSourceAwayFromZeros :=
  { xiZeroContribution := H.xiZeroContribution
    xi_diff_at := H.xi_diff_at
    xi_logDeriv_eq := H.logDeriv_eq }

/-- 📦 **`CompletedXiHadamardProductWithZeros`** — the classical
Hadamard product representation of `completedXiFunction` with a
possible analytic prefactor. Parameterized by the zero index type `ι`.-/
structure CompletedXiHadamardProductWithZeros (ι : Type) : Type where
  zeroLoc : ι → ℂ
  prefactor : ℂ → ℂ
  prefactor_differentiable_at :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      DifferentiableAt ℂ prefactor s
  prefactor_ne_zero :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      prefactor s ≠ 0
  xi_eq_product :
    ∀ s : ℂ,
      completedXiFunction s
        = prefactor s * infiniteHadamardProduct zeroLoc s
  product_data : HadamardLocallyUniformProductData zeroLoc

/-- 📦 **`ClassicalPathBAnalyticInputs`** — the Hadamard-side
classical-input bundle. The remaining xi-side analytic inputs
(aside from the Stieltjes equality) live in this single object.-/
structure ClassicalPathBAnalyticInputs (ι : Type) where
  zeroLoc : ι → ℂ
  prefactor : ℂ → ℂ
  Hinv : HadamardZeroInvSqSummability zeroLoc
  Hluc : HadamardProductLUCLogDerivData zeroLoc
  Hregion :
    ∀ s : ℂ, completedXiFunction s ≠ 0 → s ∈ Hluc.region
  HnonzeroRegion :
    ∀ s ∈ Hluc.region, ∀ i, s ≠ zeroLoc i
  Hfact :
    ∀ s : ℂ,
      completedXiFunction s = prefactor s * infiniteHadamardProduct zeroLoc s
  Hpref_diff :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 → DifferentiableAt ℂ prefactor s
  Hpref_ne :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 → prefactor s ≠ 0

/-- 📦 **`CompletedXiHadamardPrefactorData`** — away-from-zeros properties of the
Hadamard prefactor as a Prop.-/
structure CompletedXiHadamardPrefactorData (prefactor : ℂ → ℂ) : Prop where
  differentiable_at_nonzero :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      DifferentiableAt ℂ prefactor s
  nonzero_at_nonzero :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      prefactor s ≠ 0

/-- 📦 **`CompletedXiHadamardFactorizationData`** — the classical
factorization identity `ξ = prefactor · ∏ E₁(·/ρᵢ)`.-/
structure CompletedXiHadamardFactorizationData
    {ι : Type*} (zeroLoc : ι → ℂ) (prefactor : ℂ → ℂ) : Prop where
  factorization :
    ∀ s : ℂ,
      completedXiFunction s
        = prefactor s * infiniteHadamardProduct zeroLoc s

/-- 📦 **`ConcreteCompletedXiZeroSystem`** — analytic-agent handoff
for the zero index. Parameterized by `ι : Type`.-/
structure ConcreteCompletedXiZeroSystem (ι : Type) : Type where
  zeroLoc : ι → ℂ
  zeroLoc_ne_zero : ∀ i : ι, zeroLoc i ≠ 0
  zeroLoc_is_zero : ∀ i : ι, completedXiFunction (zeroLoc i) = 0
  all_completedXi_zeros :
    ∀ s : ℂ, completedXiFunction s = 0 → ∃ i : ι, zeroLoc i = s

/-- 📦 **`ConcreteCompletedXiHadamardPrefactor`** — prefactor away-from-zeros
properties as a Prop.-/
structure ConcreteCompletedXiHadamardPrefactor (prefactor : ℂ → ℂ) : Prop where
  differentiable_at_nonzero :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 → DifferentiableAt ℂ prefactor s
  nonzero_at_nonzero :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 → prefactor s ≠ 0

/-- 🌟🌟 **PROVED — `CompletedXi.LogDerivSourceAwayFromZeros` from
entire-ξ source + Γ-cancellation bridge.**-/
noncomputable def CompletedXi.LogDerivSourceAwayFromZeros.of_entireXi
    (Hbridge : EntireXiToCompletedXiLogDerivBridge)
    (Hsrc : EntireXiLogDerivativeSourceAwayFromZeros) :
    CompletedXi.LogDerivSourceAwayFromZeros := by
  refine
    { xiZeroContribution := Hsrc.xiZeroContribution
      xi_diff_at := ?_
      xi_logDeriv_eq := ?_ }
  · intro s hs
    exact Hbridge.completed_differentiable_at_nonzero s hs
  · intro s hs
    have hs_entire : entireRiemannXi s ≠ 0 :=
      Hbridge.entire_nonzero_of_completed_nonzero s hs
    calc logDerivativeResponse completedXiFunction s
        = logDerivativeResponse entireRiemannXi s :=
          Hbridge.logDeriv_completed_eq_entire s hs
      _ = Hsrc.xiZeroContribution s :=
          Hsrc.xi_logDeriv_eq s hs_entire

/-- **Zero contribution from a Hadamard-with-zeros bundle**:
`logDeriv prefactor + tsum regularized`.-/
noncomputable def xiZeroContributionFromHadamard
    {ι : Type} (H : CompletedXiHadamardProductWithZeros ι) : ℂ → ℂ :=
  fun s =>
    logDerivativeResponse H.prefactor s
      + hadamardRegularizedLogDerivSeries H.zeroLoc s

/-- 🌟🌟🌟🌟 **PROVED — final Hadamard assembly.**

```
HadamardZeroInvSqSummability (Σ 1/‖ρ‖² + escape)
+ HadamardProductLUCLogDerivData (LUC log-deriv interchange)
+ ξ Hadamard factorization (prefactor · ∏ E₁)
+ prefactor AFZ (differentiable + non-vanishing)
⟹ CompletedXiHadamardProductWithZeros ι
```-/
noncomputable def CompletedXiHadamardProductWithZeros.of_factorization_luc_invSq
    {ι : Type} {zeroLoc : ι → ℂ}
    {prefactor : ℂ → ℂ}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hluc : HadamardProductLUCLogDerivData zeroLoc)
    (Hregion : ∀ s : ℂ, completedXiFunction s ≠ 0 → s ∈ Hluc.region)
    (HnonzeroRegion : ∀ s ∈ Hluc.region, ∀ i, s ≠ zeroLoc i)
    (Hfact :
      ∀ s : ℂ,
        completedXiFunction s = prefactor s * infiniteHadamardProduct zeroLoc s)
    (Hpref_diff :
      ∀ s : ℂ,
        completedXiFunction s ≠ 0 → DifferentiableAt ℂ prefactor s)
    (Hpref_ne :
      ∀ s : ℂ,
        completedXiFunction s ≠ 0 → prefactor s ≠ 0) :
    CompletedXiHadamardProductWithZeros ι := by
  refine
    { zeroLoc := zeroLoc
      prefactor := prefactor
      prefactor_differentiable_at := Hpref_diff
      prefactor_ne_zero := Hpref_ne
      xi_eq_product := Hfact
      product_data := ?_ }
  exact
    HadamardLocallyUniformProductData.of_logDerivLimitData
      Hinv.product_multipliable
      (HadamardLogDerivLimitData.of_productLUC_and_invSq
        Hluc Hinv HnonzeroRegion)
      Hregion

/-- 🌟🌟🌟 **PROVED — `ClassicalPathBAnalyticInputs` from the
Hadamard packages.** Assembles the bundled inputs from the
separately-developed Hadamard components.-/
noncomputable def ClassicalPathBAnalyticInputs.of_hadamard_packages
    {ι : Type} {zeroLoc : ι → ℂ} {prefactor : ℂ → ℂ}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hluc : HadamardProductLUCLogDerivData zeroLoc)
    (Hregion : ∀ s : ℂ, completedXiFunction s ≠ 0 → s ∈ Hluc.region)
    (HnonzeroRegion : ∀ s ∈ Hluc.region, ∀ i, s ≠ zeroLoc i)
    (Hfact : CompletedXiHadamardFactorizationData zeroLoc prefactor)
    (Hpref : CompletedXiHadamardPrefactorData prefactor) :
    ClassicalPathBAnalyticInputs ι :=
  { zeroLoc := zeroLoc
    prefactor := prefactor
    Hinv := Hinv
    Hluc := Hluc
    Hregion := Hregion
    HnonzeroRegion := HnonzeroRegion
    Hfact := Hfact.factorization
    Hpref_diff := Hpref.differentiable_at_nonzero
    Hpref_ne := Hpref.nonzero_at_nonzero }

/-- 📦 **`ConcreteCompletedXiHadamardFactorization`** — Hadamard
product identity for the chosen zero system + prefactor.-/
structure ConcreteCompletedXiHadamardFactorization
    {ι : Type}
    (HZ : ConcreteCompletedXiZeroSystem ι)
    (prefactor : ℂ → ℂ) : Prop where
  factorization :
    ∀ s : ℂ,
      completedXiFunction s
        = prefactor s * infiniteHadamardProduct HZ.zeroLoc s

/-- 📦 **`CompletedXiZeroInvSqDistribution`** — RvM-style
zero-distribution input.-/
structure CompletedXiZeroInvSqDistribution
    {ι : Type} (HZ : ConcreteCompletedXiZeroSystem ι) : Prop where
  inv_sq_summable :
    Summable fun i : ι => (‖HZ.zeroLoc i‖ ^ 2)⁻¹
  eventually_large :
    ∀ s : ℂ,
      ∀ᶠ i in Filter.cofinite, 2 * ‖s‖ ≤ ‖HZ.zeroLoc i‖

/-- ⭐ **PROVED — convert to `CompletedXiHadamardPrefactorData`.**-/
theorem ConcreteCompletedXiHadamardPrefactor.toPrefactorData
    {prefactor : ℂ → ℂ}
    (H : ConcreteCompletedXiHadamardPrefactor prefactor) :
    CompletedXiHadamardPrefactorData prefactor :=
  { differentiable_at_nonzero := H.differentiable_at_nonzero
    nonzero_at_nonzero := H.nonzero_at_nonzero }

/-- **Canonical completed-ξ source obtained from the canonical entire-ξ
log-derivative source and the proved Γ-cancellation bridge.**-/
noncomputable def canonicalCompletedXiLogDerivativeSourceAwayFromZeros :
    CompletedXi.LogDerivSourceAwayFromZeros :=
  CompletedXi.LogDerivSourceAwayFromZeros.of_entireXi
    entireXiToCompletedXiLogDerivBridge
    canonicalEntireXiLogDerivativeSourceAwayFromZeros

/-- 🌟🌟 **PROVED — convert ξ-nonzero-region LUC data to the general
`HadamardProductLUCLogDerivData` interface.**-/
noncomputable def HadamardProductLUCOnXiNonzeroData.toLUCLogDerivData
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardProductLUCOnXiNonzeroData zeroLoc) :
    HadamardProductLUCLogDerivData zeroLoc :=
  { region := {s : ℂ | completedXiFunction s ≠ 0}
    locally_uniform_product := H.locally_uniform_product
    infinite_differentiable_at := by
      intro s hs
      exact H.infinite_differentiable_at s hs
    logDeriv_eq_tsum := by
      intro s hs
      exact H.logDeriv_eq_tsum s hs }

/-- ⭐ **PROVED — convert to `CompletedXiHadamardFactorizationData`.**-/
theorem ConcreteCompletedXiHadamardFactorization.toFactorizationData
    {ι : Type} {HZ : ConcreteCompletedXiZeroSystem ι}
    {prefactor : ℂ → ℂ}
    (H : ConcreteCompletedXiHadamardFactorization HZ prefactor) :
    CompletedXiHadamardFactorizationData HZ.zeroLoc prefactor :=
  { factorization := H.factorization }

/-- ⭐ **PROVED — convert to `HadamardZeroInvSqSummability`.**-/
theorem CompletedXiZeroInvSqDistribution.toHadamardZeroInvSqSummability
    {ι : Type} {HZ : ConcreteCompletedXiZeroSystem ι}
    (H : CompletedXiZeroInvSqDistribution HZ) :
    HadamardZeroInvSqSummability HZ.zeroLoc :=
  { zero_ne := HZ.zeroLoc_ne_zero
    inv_sq_summable := H.inv_sq_summable
    eventually_large := H.eventually_large }

/-- 📦 **`ConcreteCompletedXiHadamardInputs`** — full concrete
Hadamard-side input package for the analytic agent.-/
structure ConcreteCompletedXiHadamardInputs (ι : Type) : Type where
  zeroSystem : ConcreteCompletedXiZeroSystem ι
  prefactor : ℂ → ℂ
  zeroDistribution : CompletedXiZeroInvSqDistribution zeroSystem
  luc : HadamardProductLUCLogDerivData zeroSystem.zeroLoc
  region :
    ∀ s : ℂ, completedXiFunction s ≠ 0 → s ∈ luc.region
  nonzeroRegion :
    ∀ s ∈ luc.region, ∀ i, s ≠ zeroSystem.zeroLoc i
  factorization :
    ConcreteCompletedXiHadamardFactorization zeroSystem prefactor
  prefactorData :
    ConcreteCompletedXiHadamardPrefactor prefactor

/-- 🌟🌟🌟 **PROVED — concrete completed-ξ Hadamard inputs from LUC data
on the ξ-nonzero region.** This is the publication-friendly constructor:
the region and no-collision side conditions are no longer separate
Hadamard obligations.-/
noncomputable def ConcreteCompletedXiHadamardInputs.of_lucOnXiNonzero
    {ι : Type}
    (HZ : ConcreteCompletedXiZeroSystem ι)
    (prefactor : ℂ → ℂ)
    (Hdist : CompletedXiZeroInvSqDistribution HZ)
    (Hluc : HadamardProductLUCOnXiNonzeroData HZ.zeroLoc)
    (Hfact : ConcreteCompletedXiHadamardFactorization HZ prefactor)
    (Hpref : ConcreteCompletedXiHadamardPrefactor prefactor) :
    ConcreteCompletedXiHadamardInputs ι :=
  { zeroSystem := HZ
    prefactor := prefactor
    zeroDistribution := Hdist
    luc := Hluc.toLUCLogDerivData
    region := by
      intro s hs
      exact hs
    nonzeroRegion := by
      intro s hs i hsi
      apply hs
      rw [hsi]
      exact HZ.zeroLoc_is_zero i
    factorization := Hfact
    prefactorData := Hpref }

/-- 🌟🌟🌟 **PROVED — extract the classical analytic inputs from the
concrete completed-ξ Hadamard input package.**-/
noncomputable def ConcreteCompletedXiHadamardInputs.toClassicalAnalyticInputs
    {ι : Type} (H : ConcreteCompletedXiHadamardInputs ι) :
    ClassicalPathBAnalyticInputs ι := by
  refine
    { zeroLoc := H.zeroSystem.zeroLoc
      prefactor := H.prefactor
      Hinv := ?_
      Hluc := H.luc
      Hregion := H.region
      HnonzeroRegion := H.nonzeroRegion
      Hfact := ?_
      Hpref_diff := ?_
      Hpref_ne := ?_ }
  · exact H.zeroDistribution.toHadamardZeroInvSqSummability
  · exact H.factorization.factorization
  · exact H.prefactorData.differentiable_at_nonzero
  · exact H.prefactorData.nonzero_at_nonzero

/-- 🌟🌟🌟 **PROVED — `ClassicalPathBAnalyticInputs` from the Hadamard
packages, with the ξ-nonzero LUC data and the zero-system equation.** The
no-collision side condition is discharged from the zero-system equation
`completedXiFunction (zeroLoc i) = 0`.-/
noncomputable def ClassicalPathBAnalyticInputs.of_hadamard_packages_onXiNonzero
    {ι : Type} {zeroLoc : ι → ℂ} {prefactor : ℂ → ℂ}
    (Hzero : ∀ i : ι, completedXiFunction (zeroLoc i) = 0)
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hluc : HadamardProductLUCOnXiNonzeroData zeroLoc)
    (Hfact : CompletedXiHadamardFactorizationData zeroLoc prefactor)
    (Hpref : CompletedXiHadamardPrefactorData prefactor) :
    ClassicalPathBAnalyticInputs ι :=
  ClassicalPathBAnalyticInputs.of_hadamard_packages
    Hinv
    Hluc.toLUCLogDerivData
    (by
      intro s hs
      exact hs)
    (by
      intro s hs i hsi
      apply hs
      rw [hsi]
      exact Hzero i)
    Hfact
    Hpref

end OverflowResidueRH
