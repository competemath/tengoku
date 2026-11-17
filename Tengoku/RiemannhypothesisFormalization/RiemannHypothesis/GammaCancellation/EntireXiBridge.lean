/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Analysis.Calculus.Deriv.Basic
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ComplexAnalysis.LogDerivative
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.FunctionalEquation
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.GammaCancellation.TextbookXi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# GammaCancellation.EntireXiBridge

The log-derivative bridge between the raw Γ-based `completedXiFunction` and Mathlib's
entire `entireRiemannXi`, assembled from the pole-set topology (`PoleSet`), the
completed-zeta identities (`CompletedZeta`), and the off-pole pointwise formula
(`TextbookXi`).

The headline result is `entireXiToCompletedXiLogDerivBridge`: **unconditionally**, at
every point where the raw completed ξ is nonzero, the raw completed ξ is differentiable
and its logarithmic-derivative response equals that of the entire ξ. This is exactly the
Γ-cancellation step — it lets the downstream Hadamard/Stieltjes route work with the
genuinely-entire `entireRiemannXi` while phrasing zero-contributions through the textbook
`completedXiFunction`.

The intermediate `…Source` structures form a ladder of progressively weaker, more
elementary hypotheses (pointwise → open-neighborhood → eventually-equal → log-derivative
bridge); each `.of_…` lemma climbs one rung, and the unconditional inhabitants at the end
discharge the whole ladder.
-/

namespace OverflowResidueRH

open Complex Filter Topology

/-- 📦 **`EntireXiToCompletedXiLogDerivBridge`** — quarantines the
Γ-pole/zero cancellation in a single named Prop.-/
structure EntireXiToCompletedXiLogDerivBridge : Prop where
  entire_nonzero_of_completed_nonzero :
    ∀ s : ℂ, completedXiFunction s ≠ 0 → entireRiemannXi s ≠ 0
  completed_differentiable_at_nonzero :
    ∀ s : ℂ, completedXiFunction s ≠ 0 →
      DifferentiableAt ℂ completedXiFunction s
  logDeriv_completed_eq_entire :
    ∀ s : ℂ, completedXiFunction s ≠ 0 →
      logDerivativeResponse completedXiFunction s
        = logDerivativeResponse entireRiemannXi s

/-- 📦 **`CompletedXiEqualsEntireXiLocallyAFZSource`** — local AFZ
equality between raw `completedXiFunction` and `entireRiemannXi`.-/
structure CompletedXiEqualsEntireXiLocallyAFZSource : Prop where
  eventually_eq_of_completed_nonzero :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      completedXiFunction =ᶠ[𝓝 s] entireRiemannXi
  differentiable_completed :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      DifferentiableAt ℂ completedXiFunction s

/-- ⭐ **PROVED — entire ξ nonzero from raw nonzero + local equality.**-/
theorem entireXi_nonzero_of_completedXi_nonzero_of_localEquality
    (H : CompletedXiEqualsEntireXiLocallyAFZSource)
    {s : ℂ} (hs : completedXiFunction s ≠ 0) :
    entireRiemannXi s ≠ 0 := by
  have hev : completedXiFunction =ᶠ[𝓝 s] entireRiemannXi :=
    H.eventually_eq_of_completed_nonzero s hs
  have hval : completedXiFunction s = entireRiemannXi s :=
    hev.eq_of_nhds
  intro hent
  apply hs
  rw [hval, hent]

/-- ⭐ **PROVED — raw completed ξ differentiable at AFZ.**-/
theorem completedXi_differentiable_at_nonzero_of_localEquality
    (H : CompletedXiEqualsEntireXiLocallyAFZSource)
    {s : ℂ} (hs : completedXiFunction s ≠ 0) :
    DifferentiableAt ℂ completedXiFunction s :=
  H.differentiable_completed s hs

/-- ⭐ **PROVED — local equality ⟹ `logDerivativeResponse` agree.**-/
theorem logDerivativeResponse_eq_of_eventuallyEq
    {f g : ℂ → ℂ} {s : ℂ} (hfg : f =ᶠ[𝓝 s] g) :
    logDerivativeResponse f s = logDerivativeResponse g s := by
  have hval : f s = g s := hfg.eq_of_nhds
  have hderiv : deriv f s = deriv g s := hfg.deriv_eq
  unfold logDerivativeResponse
  rw [hderiv, hval]

/-- ⭐ **PROVED — log-derivs of completed ξ and entire ξ agree AFZ.**-/
theorem logDeriv_completed_eq_entire_of_localEquality
    (H : CompletedXiEqualsEntireXiLocallyAFZSource)
    {s : ℂ} (hs : completedXiFunction s ≠ 0) :
    logDerivativeResponse completedXiFunction s
      = logDerivativeResponse entireRiemannXi s :=
  logDerivativeResponse_eq_of_eventuallyEq
    (H.eventually_eq_of_completed_nonzero s hs)

/-- 🌟🌟🌟 **PROVED — `EntireXiToCompletedXiLogDerivBridge` from
local equality source.**-/
theorem EntireXiToCompletedXiLogDerivBridge.of_localEquality
    (H : CompletedXiEqualsEntireXiLocallyAFZSource) :
    EntireXiToCompletedXiLogDerivBridge := by
  refine
    { entire_nonzero_of_completed_nonzero := ?_
      completed_differentiable_at_nonzero := ?_
      logDeriv_completed_eq_entire := ?_ }
  · intro s hs
    exact entireXi_nonzero_of_completedXi_nonzero_of_localEquality H hs
  · intro s hs
    exact completedXi_differentiable_at_nonzero_of_localEquality H hs
  · intro s hs
    exact logDeriv_completed_eq_entire_of_localEquality H hs

/-- 📦 **`CompletedXiRawEqualsEntireXiOffGammaPoles`** — the
concrete local theorem target: raw Γ-based `completedXiFunction`
agrees locally with `entireRiemannXi` at every nonzero raw
completed-ξ point.-/
structure CompletedXiRawEqualsEntireXiOffGammaPoles : Prop where
  eventually_eq :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      completedXiFunction =ᶠ[𝓝 s] entireRiemannXi
  differentiable_at :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      DifferentiableAt ℂ completedXiFunction s

/-- ⭐ **PROVED — local equality source from raw off-pole theorem.**-/
theorem CompletedXiEqualsEntireXiLocallyAFZSource.of_rawOffGammaPoles
    (H : CompletedXiRawEqualsEntireXiOffGammaPoles) :
    CompletedXiEqualsEntireXiLocallyAFZSource :=
  { eventually_eq_of_completed_nonzero := H.eventually_eq
    differentiable_completed := H.differentiable_at }

/-- ⭐ **PROVED — full bridge from raw off-pole theorem.**-/
theorem EntireXiToCompletedXiLogDerivBridge.of_rawOffGammaPoles
    (H : CompletedXiRawEqualsEntireXiOffGammaPoles) :
    EntireXiToCompletedXiLogDerivBridge :=
  EntireXiToCompletedXiLogDerivBridge.of_localEquality
    (CompletedXiEqualsEntireXiLocallyAFZSource.of_rawOffGammaPoles H)

/-- ⭐ **PROVED — `completedXi` differentiable when locally equal to
`entireXi` (which is itself differentiable).**-/
theorem completedXi_differentiable_of_eventuallyEq_entireXi
    {s : ℂ}
    (hev : completedXiFunction =ᶠ[𝓝 s] entireRiemannXi)
    (hentire : DifferentiableAt ℂ entireRiemannXi s) :
    DifferentiableAt ℂ completedXiFunction s :=
  hentire.congr_of_eventuallyEq hev

/-- 📦 **`EntireRiemannXiDifferentiabilitySource`** — every-point
differentiability of `entireRiemannXi`.-/
structure EntireRiemannXiDifferentiabilitySource : Prop where
  differentiable_at :
    ∀ s : ℂ, DifferentiableAt ℂ entireRiemannXi s

/-- 🌟🌟 **PROVED — unconditional inhabitant via
`entireRiemannXi_differentiable`.**-/
theorem entireRiemannXi_differentiabilitySource :
    EntireRiemannXiDifferentiabilitySource :=
  ⟨fun _ => entireRiemannXi_differentiable.differentiableAt⟩

/-- 📦 **`CompletedXiRawEntireXiLocalEqualitySource`** — the genuine
Γ-cancellation local equality theorem target.-/
structure CompletedXiRawEntireXiLocalEqualitySource : Prop where
  eventually_eq_at_nonzero :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      completedXiFunction =ᶠ[𝓝 s] entireRiemannXi

/-- 🌟🌟🌟 **PROVED — `CompletedXiRawEqualsEntireXiOffGammaPoles`
from local equality + entire differentiability.**-/
theorem CompletedXiRawEqualsEntireXiOffGammaPoles.of_eventuallyEq
    (Hdiff : EntireRiemannXiDifferentiabilitySource)
    (Heq :
      ∀ s : ℂ,
        completedXiFunction s ≠ 0 →
        completedXiFunction =ᶠ[𝓝 s] entireRiemannXi) :
    CompletedXiRawEqualsEntireXiOffGammaPoles := by
  refine
    { eventually_eq := Heq
      differentiable_at := ?_ }
  intro s hs
  exact completedXi_differentiable_of_eventuallyEq_entireXi
    (Heq s hs) (Hdiff.differentiable_at s)

/-- ⭐ **PROVED — bridge from `CompletedXiRawEntireXiLocalEqualitySource`
+ differentiability source.**-/
theorem CompletedXiRawEqualsEntireXiOffGammaPoles.of_localEqualitySource
    (Hdiff : EntireRiemannXiDifferentiabilitySource)
    (Heq : CompletedXiRawEntireXiLocalEqualitySource) :
    CompletedXiRawEqualsEntireXiOffGammaPoles :=
  CompletedXiRawEqualsEntireXiOffGammaPoles.of_eventuallyEq
    Hdiff Heq.eventually_eq_at_nonzero

/-- **Raw completed-ξ regular region**: the AFZ set.-/
def completedXiRawRegularRegion : Set ℂ :=
  {s : ℂ | completedXiFunction s ≠ 0}

/-- 📦 **`CompletedXiRawEqualsEntireXiOnRegularRegion`** —
region-form variant of the local equality source.-/
structure CompletedXiRawEqualsEntireXiOnRegularRegion : Prop where
  eventually_eq :
    ∀ s : ℂ,
      s ∈ completedXiRawRegularRegion →
      completedXiFunction =ᶠ[𝓝 s] entireRiemannXi

/-- ⭐ **PROVED — bridge from regular-region variant.**-/
theorem CompletedXiRawEntireXiLocalEqualitySource.of_regularRegion
    (H : CompletedXiRawEqualsEntireXiOnRegularRegion) :
    CompletedXiRawEntireXiLocalEqualitySource := by
  refine ⟨?_⟩
  intro s hs
  exact H.eventually_eq s hs

/-- 📦 **`CompletedXiRawEntireXiPointwiseEqualitySource`** — pointwise
equality at AFZ points. **NOT** sufficient alone for the local
equality required; kept for diagnostic clarity.-/
structure CompletedXiRawEntireXiPointwiseEqualitySource : Prop where
  pointwise_eq :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      completedXiFunction s = entireRiemannXi s

/-- 📦 **`CompletedXiRawEntireXiOpenNeighborhoodEqualitySource`** —
existence of an open neighborhood on which the two functions agree.-/
structure CompletedXiRawEntireXiOpenNeighborhoodEqualitySource : Prop where
  exists_nhds_eq :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      ∃ U : Set ℂ,
        IsOpen U ∧ s ∈ U ∧ Set.EqOn completedXiFunction entireRiemannXi U

/-- 🌟🌟 **PROVED — local equality source from open-neighborhood
variant.**-/
theorem CompletedXiRawEntireXiLocalEqualitySource.of_openNeighborhood
    (H : CompletedXiRawEntireXiOpenNeighborhoodEqualitySource) :
    CompletedXiRawEntireXiLocalEqualitySource := by
  refine ⟨?_⟩
  intro s hs
  obtain ⟨U, hUopen, hsU, hEq⟩ := H.exists_nhds_eq s hs
  filter_upwards [hUopen.mem_nhds hsU] with w hw
  exact hEq hw

/-- 📦 **`CompletedXiGammaRegularNeighborhoodSource`** — every
nonzero-completed-ξ point has an open neighborhood where `Γ(w/2)`
has no pole.-/
structure CompletedXiGammaRegularNeighborhoodSource : Prop where
  exists_regular_nhds :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      ∃ U : Set ℂ,
        IsOpen U ∧ s ∈ U ∧
        (∀ w ∈ U, w / 2 ∉ {z : ℂ | ∃ n : ℕ, z = -n})

/-- 📦 **`CompletedXiRawEntireXiOffPoleFormulaEquality`** — the pure
formula identity: on any open set `U` avoiding `Γ(·/2)` poles, raw
completed ξ and entire ξ agree pointwise.-/
structure CompletedXiRawEntireXiOffPoleFormulaEquality : Prop where
  eq_on_regular :
    ∀ U : Set ℂ,
      IsOpen U →
      (∀ w ∈ U, w / 2 ∉ {z : ℂ | ∃ n : ℕ, z = -n}) →
      Set.EqOn completedXiFunction entireRiemannXi U

/-- 🌟🌟🌟 **PROVED — open-neighborhood equality from
Γ-regular + off-pole formula.**-/
theorem CompletedXiRawEntireXiOpenNeighborhoodEqualitySource.of_gammaRegular_offPoleFormula
    (Hreg : CompletedXiGammaRegularNeighborhoodSource)
    (Hformula : CompletedXiRawEntireXiOffPoleFormulaEquality) :
    CompletedXiRawEntireXiOpenNeighborhoodEqualitySource := by
  refine ⟨?_⟩
  intro s hs
  obtain ⟨U, hUopen, hsU, hreg⟩ := Hreg.exists_regular_nhds s hs
  exact ⟨U, hUopen, hsU, Hformula.eq_on_regular U hUopen hreg⟩

/-- 🌟🌟🌟 **PROVED — local equality source from Γ-regular +
off-pole formula.**-/
theorem CompletedXiRawEntireXiLocalEqualitySource.of_gammaRegular_offPoleFormula
    (Hreg : CompletedXiGammaRegularNeighborhoodSource)
    (Hformula : CompletedXiRawEntireXiOffPoleFormulaEquality) :
    CompletedXiRawEntireXiLocalEqualitySource :=
  CompletedXiRawEntireXiLocalEqualitySource.of_openNeighborhood
    (CompletedXiRawEntireXiOpenNeighborhoodEqualitySource.of_gammaRegular_offPoleFormula
      Hreg Hformula)

/-- 🌟🌟🌟 **PROVED — `CompletedXiGammaRegularNeighborhoodSource`
from no-pole + avoiding-neighborhood sources.**-/
theorem CompletedXiGammaRegularNeighborhoodSource.of_noPole_and_avoidingNhds
    (Hnopole : CompletedXiNonzeroExcludesGammaPole)
    (Hnhds : GammaPoleAvoidingNeighborhoodSource) :
    CompletedXiGammaRegularNeighborhoodSource := by
  refine ⟨?_⟩
  intro s hs
  exact Hnhds.exists_avoiding_nhds s (Hnopole.not_gamma_pole s hs)

/-- 🌟🌟🌟 **PROVED — local equality source from raw correctness via
direct pointwise → local bridge.** Bypasses the set-level open-region
chain (which has trouble with the `+ 1/2` correction at s = 1).-/
theorem CompletedXiRawEntireXiLocalEqualitySource.of_rawCorrectness
    (H : RawCompletedXiCorrectness) :
    CompletedXiRawEntireXiLocalEqualitySource := by
  refine ⟨?_⟩
  intro s hs
  have h_s_ne_one : s ≠ 1 :=
    fun h => hs (h ▸ completedXiFunction_one_eq_zero)
  have h_polePullback : s / 2 ∉ gammaPoleSet :=
    H.nonzero_excludes_gammaPole.not_gamma_pole s hs
  have hcont : Continuous (fun w : ℂ => w / 2) :=
    continuous_id.div_const _
  have hOpen1 : IsOpen ((fun w : ℂ => w / 2) ⁻¹' gammaPoleSet)ᶜ :=
    (isClosed_gammaPoleSet.preimage hcont).isOpen_compl
  have hOpen2 : IsOpen (({(1 : ℂ)} : Set ℂ))ᶜ := isOpen_compl_singleton
  have hU_open :
      IsOpen
        (((fun w : ℂ => w / 2) ⁻¹' gammaPoleSet)ᶜ ∩
          ({(1 : ℂ)} : Set ℂ)ᶜ) :=
    hOpen1.inter hOpen2
  have hsU :
      s ∈ ((fun w : ℂ => w / 2) ⁻¹' gammaPoleSet)ᶜ ∩
            ({(1 : ℂ)} : Set ℂ)ᶜ :=
    ⟨h_polePullback, h_s_ne_one⟩
  filter_upwards [hU_open.mem_nhds hsU] with w hwU
  exact H.offPole_eq w hwU.2 hwU.1

/-- 🌟🌟🌟 **PROVED — pointwise equality source from raw correctness.**-/
theorem CompletedXiRawEntireXiPointwiseEqualitySource.of_rawCorrectness
    (H : RawCompletedXiCorrectness) :
    CompletedXiRawEntireXiPointwiseEqualitySource := by
  refine ⟨?_⟩
  intro s hs
  have h_s_ne_one : s ≠ 1 :=
    fun h => hs (h ▸ completedXiFunction_one_eq_zero)
  have h_polePullback : s / 2 ∉ gammaPoleSet :=
    H.nonzero_excludes_gammaPole.not_gamma_pole s hs
  exact H.offPole_eq s h_s_ne_one h_polePullback

/-- 🌟🌟🌟 **PROVED — open-neighborhood equality source from raw
correctness.**-/
theorem CompletedXiRawEntireXiOpenNeighborhoodEqualitySource.of_rawCorrectness
    (H : RawCompletedXiCorrectness) :
    CompletedXiRawEntireXiOpenNeighborhoodEqualitySource := by
  refine ⟨?_⟩
  intro s hs
  have h_s_ne_one : s ≠ 1 :=
    fun h => hs (h ▸ completedXiFunction_one_eq_zero)
  have h_polePullback : s / 2 ∉ gammaPoleSet :=
    H.nonzero_excludes_gammaPole.not_gamma_pole s hs
  let U : Set ℂ :=
    ((fun w : ℂ => w / 2) ⁻¹' gammaPoleSet)ᶜ ∩
      ({(1 : ℂ)} : Set ℂ)ᶜ
  have hcont : Continuous (fun w : ℂ => w / 2) :=
    continuous_id.div_const _
  have hOpen1 : IsOpen ((fun w : ℂ => w / 2) ⁻¹' gammaPoleSet)ᶜ :=
    (isClosed_gammaPoleSet.preimage hcont).isOpen_compl
  have hOpen2 : IsOpen (({(1 : ℂ)} : Set ℂ))ᶜ := isOpen_compl_singleton
  have hU_open : IsOpen U :=
    hOpen1.inter hOpen2
  have hsU : s ∈ U :=
    ⟨h_polePullback, h_s_ne_one⟩
  refine ⟨U, hU_open, hsU, ?_⟩
  intro w hw
  exact H.offPole_eq w hw.2 hw.1

/-- 🌟🌟 **PROVED — full entire→completed bridge from raw correctness.**-/
theorem EntireXiToCompletedXiLogDerivBridge.of_rawCorrectness
    (H : RawCompletedXiCorrectness) :
    EntireXiToCompletedXiLogDerivBridge :=
  EntireXiToCompletedXiLogDerivBridge.of_rawOffGammaPoles
    (CompletedXiRawEqualsEntireXiOffGammaPoles.of_localEqualitySource
      entireRiemannXi_differentiabilitySource
      (CompletedXiRawEntireXiLocalEqualitySource.of_rawCorrectness H))

/-- 🌟🌟🌟🌟 **PROVED unconditionally** — pointwise equality between raw
completed ξ and Mathlib's entire ξ at all nonzero raw completed-ξ
points.-/
theorem completedXiRawEntireXiPointwiseEqualitySource :
    CompletedXiRawEntireXiPointwiseEqualitySource :=
  CompletedXiRawEntireXiPointwiseEqualitySource.of_rawCorrectness
    rawCompletedXiCorrectness

/-- 🌟🌟🌟🌟 **PROVED unconditionally** — open-neighborhood equality between
raw completed ξ and Mathlib's entire ξ at all nonzero raw completed-ξ
points.-/
theorem completedXiRawEntireXiOpenNeighborhoodEqualitySource :
    CompletedXiRawEntireXiOpenNeighborhoodEqualitySource :=
  CompletedXiRawEntireXiOpenNeighborhoodEqualitySource.of_rawCorrectness
    rawCompletedXiCorrectness

/-- 🌟🌟🌟🌟 **PROVED unconditionally** — local equality between raw
completed ξ and Mathlib's entire ξ at all nonzero raw completed-ξ
points.-/
theorem completedXiRawEntireXiLocalEqualitySource :
    CompletedXiRawEntireXiLocalEqualitySource :=
  CompletedXiRawEntireXiLocalEqualitySource.of_openNeighborhood
    completedXiRawEntireXiOpenNeighborhoodEqualitySource

/-- 🌟🌟🌟🌟 **PROVED unconditionally** — regular-region local equality
between raw completed ξ and Mathlib's entire ξ.-/
theorem completedXiRawEqualsEntireXiOnRegularRegion :
    CompletedXiRawEqualsEntireXiOnRegularRegion :=
  ⟨fun s hs =>
    completedXiRawEntireXiLocalEqualitySource.eventually_eq_at_nonzero s hs⟩

/-- 🌟🌟🌟🌟 **PROVED unconditionally** — raw completed ξ agrees locally
with entire ξ off Γ-poles, with differentiability included.-/
theorem completedXiRawEqualsEntireXiOffGammaPoles :
    CompletedXiRawEqualsEntireXiOffGammaPoles :=
  CompletedXiRawEqualsEntireXiOffGammaPoles.of_localEqualitySource
    entireRiemannXi_differentiabilitySource
    completedXiRawEntireXiLocalEqualitySource

/-- 🌟🌟🌟🌟 **PROVED unconditionally** — the older local AFZ equality
source, including differentiability of raw completed ξ at nonzero raw
completed-ξ points.-/
theorem completedXiEqualsEntireXiLocallyAFZSource :
    CompletedXiEqualsEntireXiLocallyAFZSource :=
  CompletedXiEqualsEntireXiLocallyAFZSource.of_rawOffGammaPoles
    completedXiRawEqualsEntireXiOffGammaPoles

/-- 🌟🌟🌟🌟🌟 **PROVED unconditionally** — the completed-to-entire ξ
log-derivative bridge. The Γ-cancellation hazard, fully discharged.-/
theorem entireXiToCompletedXiLogDerivBridge :
    EntireXiToCompletedXiLogDerivBridge :=
  EntireXiToCompletedXiLogDerivBridge.of_rawOffGammaPoles
    completedXiRawEqualsEntireXiOffGammaPoles

end OverflowResidueRH
