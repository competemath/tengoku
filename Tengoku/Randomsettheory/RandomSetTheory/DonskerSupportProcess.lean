/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FunctionalZeroSetTransfer
import Tengoku.Randomsettheory.RandomSetTheory.SupportProcessContinuousMapping
import Tengoku.Randomsettheory.RandomSetTheory.UniformSupportTransfer
import Tengoku.Seed.Topology.ContinuousMap.SecondCountableSpace
import Tengoku.Seed.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Donsker interfaces for parameterized support processes

The nonseparable space `ℓ∞(Θ × B)` is not a sound default state space for
ordinary Borel weak convergence.  This file instead uses continuous paths on
the compact metric index space

`Θ × closedBall (0 : E) 1`.

Under the hypotheses below this continuous-function space is a separable
Banach space.  `IsPDonskerSupportClass` records three substantive facts:

* an unscaled continuous path is exactly the difference of the empirical and
  population support functions;
* its root-`n` scaling converges in distribution as a random element of that
  separable function space;
* the supplied limit has centered Gaussian finite-dimensional distributions.

This is an interface, not a proof that a concrete support class is Donsker.
The latter remains an explicit hypothesis for each application.  The results
here prove the missing deterministic bridge: the path sup norm is exactly
the parameter-uniform Hausdorff error for compact nonempty convex fibres.
-/

open Set Metric MeasureTheory Filter ProbabilityTheory
open scoped InnerProductSpace Topology ProbabilityTheory

noncomputable section

namespace RandomSetTheory

/-- Compact index space of a parameterized support process.-/
abbrev SupportProcessIndex (Θ E : Type*) [Zero E] [PseudoMetricSpace E] :=
  Θ × Metric.closedBall (0 : E) 1

/-- Separable continuous-path replacement for a potentially nonseparable
`ℓ∞` process space.-/
abbrev ContinuousSupportProcess (Θ E : Type*) [TopologicalSpace Θ]
    [Zero E] [PseudoMetricSpace E] :=
  C(SupportProcessIndex Θ E, ℝ)

/-- The selected continuous-path process space is separable under the
standard compact-metric assumptions used for the parameter set and the
finite-dimensional support space.
@isnad1 id=separabl.0h2v.s7.8bae18404987 from=translated src=- shape=002b91be vocab=e7aecc4f
-/
theorem continuousSupportProcess_separable
    (Θ E : Type*) [MetricSpace Θ] [CompactSpace Θ]
    [SecondCountableTopology Θ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    TopologicalSpace.SeparableSpace (ContinuousSupportProcess Θ E) := by
  infer_instance

/-- The selected continuous-path process space is complete.
@isnad1 id=complete.0h2v.s7.1eb620c11398 from=translated src=- shape=7d0eb44f vocab=3469828c
-/
theorem continuousSupportProcess_complete
    (Θ E : Type*) [MetricSpace Θ] [CompactSpace Θ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    CompleteSpace (ContinuousSupportProcess Θ E) := by
  infer_instance

/-- Supremum, over the parameter, of the Hausdorff errors.  The value is
defined with `sSup`; below it is identified with a continuous-path norm, which
in particular proves boundedness of the range in the intended setting.-/
def parameterUniformHausdorffDist
    {Θ E : Type*} [PseudoMetricSpace E]
    (K L : Θ → Set E) : ℝ :=
  sSup (Set.range fun θ => hausdorffDist (K θ) (L θ))

/-- A continuous support-difference path dominates the Hausdorff error at
each parameter.  This is the first half of the deterministic uniform bridge.
@isnad1 id=le.7h6v.s9.7f9234924fa4 from=translated src=- shape=7d9cfb55 vocab=5ed23428
-/
theorem hausdorffDist_le_norm_continuousSupportProcess
    {Θ E : Type*} [TopologicalSpace Θ] [CompactSpace Θ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K L : Θ → Set E}
    (hKcompact : ∀ θ, IsCompact (K θ))
    (hLcompact : ∀ θ, IsCompact (L θ))
    (hKne : ∀ θ, (K θ).Nonempty)
    (hLne : ∀ θ, (L θ).Nonempty)
    (hKconv : ∀ θ, Convex ℝ (K θ))
    (hLconv : ∀ θ, Convex ℝ (L θ))
    (U : ContinuousSupportProcess Θ E)
    (hU : ∀ q : SupportProcessIndex Θ E,
      U q = supportFunction (K q.1) q.2 - supportFunction (L q.1) q.2)
    (θ : Θ) :
    hausdorffDist (K θ) (L θ) ≤ ‖U‖ := by
  apply hausdorffDist_le_of_unitBall_supportFunction_sub_le
    (hKcompact θ) (hLcompact θ) (hKne θ) (hLne θ)
    (hKconv θ) (hLconv θ) (norm_nonneg U)
  intro u hu
  let us : Metric.closedBall (0 : E) 1 :=
    ⟨u, by simpa [Metric.mem_closedBall, dist_zero_right] using hu⟩
  have hnorm := ContinuousMap.norm_coe_le_norm U (θ, us)
  rw [hU (θ, us)] at hnorm
  simpa only [Real.norm_eq_abs] using hnorm

/-- The norm of a continuous parameter-direction support-difference process
is exactly the supremum of the parameterwise Hausdorff distances.  Thus the
definition of `Δₙ` in the report is not replaced by an unrelated process
norm: the two quantities are proved equal.
@isnad1 id=eq.7h5v.s9.0af82856b3db from=translated src=- shape=ac67e751 vocab=fe2c0649
-/
theorem norm_continuousSupportProcess_eq_parameterUniformHausdorffDist
    {Θ E : Type*} [TopologicalSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K L : Θ → Set E}
    (hKcompact : ∀ θ, IsCompact (K θ))
    (hLcompact : ∀ θ, IsCompact (L θ))
    (hKne : ∀ θ, (K θ).Nonempty)
    (hLne : ∀ θ, (L θ).Nonempty)
    (hKconv : ∀ θ, Convex ℝ (K θ))
    (hLconv : ∀ θ, Convex ℝ (L θ))
    (U : ContinuousSupportProcess Θ E)
    (hU : ∀ q : SupportProcessIndex Θ E,
      U q = supportFunction (K q.1) q.2 - supportFunction (L q.1) q.2) :
    ‖U‖ = parameterUniformHausdorffDist K L := by
  have hupper : ∀ θ, hausdorffDist (K θ) (L θ) ≤ ‖U‖ :=
    hausdorffDist_le_norm_continuousSupportProcess
      hKcompact hLcompact hKne hLne hKconv hLconv U hU
  have hlub : IsLUB
      (Set.range fun θ => hausdorffDist (K θ) (L θ)) ‖U‖ := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨θ, rfl⟩
      exact hupper θ
    · intro b hb
      let θ₀ : Θ := Classical.choice inferInstance
      have hb0 : 0 ≤ b :=
        hausdorffDist_nonneg.trans (hb (Set.mem_range_self θ₀))
      rw [ContinuousMap.norm_le U hb0]
      rintro ⟨θ, u⟩
      have hu : ‖(u : E)‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using u.property
      have hs := abs_supportFunction_sub_le_hausdorffDist
        (hKcompact θ) (hLcompact θ) (hKne θ) (hLne θ) (u : E)
      rw [hU (θ, u), Real.norm_eq_abs]
      calc
        |supportFunction (K θ) u - supportFunction (L θ) u| ≤
            ‖(u : E)‖ * hausdorffDist (K θ) (L θ) := hs
        _ ≤ 1 * hausdorffDist (K θ) (L θ) :=
          mul_le_mul_of_nonneg_right hu hausdorffDist_nonneg
        _ ≤ b := by simpa using hb (Set.mem_range_self θ)
  exact (hlub.csSup_eq (Set.range_nonempty _)).symm

/-- Root-`n` scaling of an unscaled continuous support path.-/
def rootNScaledSupportProcess
    {Ω Θ E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Θ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : ℕ → Ω → ContinuousSupportProcess Θ E) :
    ℕ → Ω → ContinuousSupportProcess Θ E :=
  fun n ω => Real.sqrt (n : ℝ) • U n ω

/-- Honest continuous-path interface for a `P`-Donsker support class.

The verification that a concrete class satisfies this structure is not
provided here.  In particular, `weakConvergence` and the Gaussian/centering
properties of `Z` are substantive application hypotheses.-/
structure IsPDonskerSupportClass
    {Ω Ω' Θ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [TopologicalSpace Θ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace (ContinuousSupportProcess Θ E)]
    [BorelSpace (ContinuousSupportProcess Θ E)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (Ghat : ℕ → Ω → Θ → Set E) (G : Θ → Set E)
    (U : ℕ → Ω → ContinuousSupportProcess Θ E)
    (Z : Ω' → ContinuousSupportProcess Θ E) : Prop where
  supportDifference : ∀ n ω q,
    U n ω q = supportFunction (Ghat n ω q.1) q.2 -
      supportFunction (G q.1) q.2
  weakConvergence : TendstoInDistribution
    (rootNScaledSupportProcess U) atTop Z (fun _ => μ) μ'
  gaussianLimit : IsGaussianProcess (fun q ω => Z ω q) μ'
  centeredLimit : ∀ q, ∫ ω, Z ω q ∂μ' = 0

namespace IsPDonskerSupportClass

variable {Ω Ω' Θ E : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MetricSpace Θ] [CompactSpace Θ] [SecondCountableTopology Θ] [Nonempty Θ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace (ContinuousSupportProcess Θ E)]
  [BorelSpace (ContinuousSupportProcess Θ E)]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {Ghat : ℕ → Ω → Θ → Set E} {G : Θ → Set E}
  {U : ℕ → Ω → ContinuousSupportProcess Θ E}
  {Z : Ω' → ContinuousSupportProcess Θ E}

/-- Weak convergence in the separable Banach process space implies that the
root-`n` scaled process itself is bounded in probability.
@isnad1 id=isbounde.1h10v.s9.f617767964a7 from=translated src=- shape=a70f9aa8 vocab=0f4a1687
-/
theorem rootN_process_isBoundedInProbability
    (h : IsPDonskerSupportClass μ μ' Ghat G U Z) :
    IsBoundedInProbability μ atTop (rootNScaledSupportProcess U) :=
  h.weakConvergence.isBoundedInProbability

/-- Exact deterministic identification of the unscaled process norm with
the report's parameter-uniform Hausdorff error.
@isnad1 id=eq.7h12v.s9.a94c5fd3f37c from=translated src=- shape=e8c528ba vocab=87fd1ac3
-/
theorem norm_eq_parameterUniformHausdorffDist
    (h : IsPDonskerSupportClass μ μ' Ghat G U Z)
    (hGhatcompact : ∀ n ω θ, IsCompact (Ghat n ω θ))
    (hGcompact : ∀ θ, IsCompact (G θ))
    (hGhatne : ∀ n ω θ, (Ghat n ω θ).Nonempty)
    (hGne : ∀ θ, (G θ).Nonempty)
    (hGhatconv : ∀ n ω θ, Convex ℝ (Ghat n ω θ))
    (hGconv : ∀ θ, Convex ℝ (G θ))
    (n : ℕ) (ω : Ω) :
    ‖U n ω‖ = parameterUniformHausdorffDist (Ghat n ω) G :=
  norm_continuousSupportProcess_eq_parameterUniformHausdorffDist
    (hGhatcompact n ω) hGcompact (hGhatne n ω) hGne
    (hGhatconv n ω) hGconv (U n ω) (h.supportDifference n ω)

/-- Exact root-`n` support/Hausdorff link.
@isnad1 id=eq.7h12v.s9.0609f7a18d67 from=translated src=- shape=c6a9917d vocab=6e3f1a72
-/
theorem norm_rootNScaledSupportProcess_eq
    (h : IsPDonskerSupportClass μ μ' Ghat G U Z)
    (hGhatcompact : ∀ n ω θ, IsCompact (Ghat n ω θ))
    (hGcompact : ∀ θ, IsCompact (G θ))
    (hGhatne : ∀ n ω θ, (Ghat n ω θ).Nonempty)
    (hGne : ∀ θ, (G θ).Nonempty)
    (hGhatconv : ∀ n ω θ, Convex ℝ (Ghat n ω θ))
    (hGconv : ∀ θ, Convex ℝ (G θ))
    (n : ℕ) (ω : Ω) :
    ‖rootNScaledSupportProcess U n ω‖ =
      Real.sqrt (n : ℝ) *
        parameterUniformHausdorffDist (Ghat n ω) G := by
  rw [rootNScaledSupportProcess, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (n : ℝ)),
    h.norm_eq_parameterUniformHausdorffDist hGhatcompact hGcompact
      hGhatne hGne hGhatconv hGconv n ω]

/-- Continuous-mapping form of the functional random-set CLT: the actual
root-`n` parameter-uniform Hausdorff error converges in distribution to the
uniform norm of the continuous Gaussian limit.
@isnad1 id=tendstoi.7h10v.s9.af40820a71f6 from=translated src=- shape=e37408b0 vocab=fa95a14e
-/
theorem rootN_parameterUniformHausdorffDist_tendstoInDistribution
    (h : IsPDonskerSupportClass μ μ' Ghat G U Z)
    (hGhatcompact : ∀ n ω θ, IsCompact (Ghat n ω θ))
    (hGcompact : ∀ θ, IsCompact (G θ))
    (hGhatne : ∀ n ω θ, (Ghat n ω θ).Nonempty)
    (hGne : ∀ θ, (G θ).Nonempty)
    (hGhatconv : ∀ n ω θ, Convex ℝ (Ghat n ω θ))
    (hGconv : ∀ θ, Convex ℝ (G θ)) :
    TendstoInDistribution (fun (n : ℕ) ω =>
      Real.sqrt (n : ℝ) *
        parameterUniformHausdorffDist (Ghat n ω) G)
      atTop (fun ω => ‖Z ω‖) (fun _ => μ) μ' := by
  have hnorm := h.weakConvergence.continuousMap_supNorm
  apply hnorm.congr
  · intro n
    filter_upwards [] with ω
    exact h.norm_rootNScaledSupportProcess_eq
      hGhatcompact hGcompact hGhatne hGne hGhatconv hGconv n ω
  · exact Filter.Eventually.of_forall (fun _ => rfl)

/-- The functional Donsker hypothesis implies
`sqrt n * Δₙ = O_P(1)` for the actual parameter-uniform Hausdorff error.
@isnad1 id=isbounde.7h10v.s9.e2811c9f2984 from=translated src=- shape=3d74fa7c vocab=2c0a9d58
-/
theorem rootN_parameterUniformHausdorffDist_isBoundedInProbability
    (h : IsPDonskerSupportClass μ μ' Ghat G U Z)
    (hGhatcompact : ∀ n ω θ, IsCompact (Ghat n ω θ))
    (hGcompact : ∀ θ, IsCompact (G θ))
    (hGhatne : ∀ n ω θ, (Ghat n ω θ).Nonempty)
    (hGne : ∀ θ, (G θ).Nonempty)
    (hGhatconv : ∀ n ω θ, Convex ℝ (Ghat n ω θ))
    (hGconv : ∀ θ, Convex ℝ (G θ)) :
    IsBoundedInProbability μ atTop (fun (n : ℕ) ω =>
      Real.sqrt (n : ℝ) *
        parameterUniformHausdorffDist (Ghat n ω) G) := by
  let Δ : ℕ → Ω → ℝ := fun n ω =>
    parameterUniformHausdorffDist (Ghat n ω) G
  apply rootN_uniformError_isBoundedInProbability_of_processCLT
    μ μ' (rootNScaledSupportProcess U) Z Δ
  · intro n ω
    change 0 ≤ parameterUniformHausdorffDist (Ghat n ω) G
    rw [← h.norm_eq_parameterUniformHausdorffDist hGhatcompact hGcompact
      hGhatne hGne hGhatconv hGconv n ω]
    exact norm_nonneg _
  · exact h.weakConvergence
  · intro n ω
    exact le_of_eq (h.norm_rootNScaledSupportProcess_eq
      hGhatcompact hGcompact hGhatne hGne hGhatconv hGconv n ω).symm

/-- Full formal version of the oracle part of Corollary 5.5.  The concrete
Donsker verification remains in `h`; compactness/nonemptiness make all
Hausdorff distances finite, and the metric error bound is explicit.
@isnad1 id=isbounde.9h11v.s9.1763c45081b3 from=translated src=- shape=8b01b40a vocab=9f4064f6
-/
theorem rootN_oracleEnlargedZeroSet_isBoundedInProbability
    (h : IsPDonskerSupportClass μ μ' Ghat G U Z)
    (hGhatcompact : ∀ n ω θ, IsCompact (Ghat n ω θ))
    (hGcompact : ∀ θ, IsCompact (G θ))
    (hGhatne : ∀ n ω θ, (Ghat n ω θ).Nonempty)
    (hGne : ∀ θ, (G θ).Nonempty)
    (hGhatconv : ∀ n ω θ, Convex ℝ (Ghat n ω θ))
    (hGconv : ∀ θ, Convex ℝ (G θ))
    {κ : ℝ} (hκ : 0 < κ)
    (herror : ∀ θ,
      κ * infDist θ (setValuedZeroSet G) ≤ infDist 0 (G θ)) :
    IsBoundedInProbability μ atTop (fun (n : ℕ) ω =>
      Real.sqrt (n : ℝ) * hausdorffDist
        (enlargedSetValuedZeroSet (Ghat n ω)
          (parameterUniformHausdorffDist (Ghat n ω) G))
        (setValuedZeroSet G)) := by
  let Δ : ℕ → Ω → ℝ := fun n ω =>
    parameterUniformHausdorffDist (Ghat n ω) G
  have hΔ : ∀ n ω, 0 ≤ Δ n ω := by
    intro n ω
    change 0 ≤ parameterUniformHausdorffDist (Ghat n ω) G
    rw [← h.norm_eq_parameterUniformHausdorffDist hGhatcompact hGcompact
      hGhatne hGne hGhatconv hGconv n ω]
    exact norm_nonneg _
  have hhaus : ∀ n ω θ,
      hausdorffDist (Ghat n ω θ) (G θ) ≤ Δ n ω := by
    intro n ω θ
    calc
      hausdorffDist (Ghat n ω θ) (G θ) ≤ ‖U n ω‖ :=
        hausdorffDist_le_norm_continuousSupportProcess
          (hGhatcompact n ω) hGcompact (hGhatne n ω) hGne
          (hGhatconv n ω) hGconv (U n ω) (h.supportDifference n ω) θ
      _ = Δ n ω :=
        h.norm_eq_parameterUniformHausdorffDist hGhatcompact hGcompact
          hGhatne hGne hGhatconv hGconv n ω
  have hfin : ∀ n ω θ,
      hausdorffEDist (Ghat n ω θ) (G θ) ≠ ⊤ := by
    intro n ω θ
    exact hausdorffEDist_ne_top_of_nonempty_of_bounded
      (hGhatne n ω θ) (hGne θ)
      (hGhatcompact n ω θ).isBounded (hGcompact θ).isBounded
  apply rootN_enlargedZeroSet_of_processCLT
    μ μ' (rootNScaledSupportProcess U) Z Ghat G Δ
    hΔ h.weakConvergence
  · intro n ω
    exact le_of_eq (h.norm_rootNScaledSupportProcess_eq
      hGhatcompact hGcompact hGhatne hGne hGhatconv hGconv n ω).symm
  · exact hκ
  · exact hfin
  · exact hhaus
  · exact herror

end IsPDonskerSupportClass

end RandomSetTheory
