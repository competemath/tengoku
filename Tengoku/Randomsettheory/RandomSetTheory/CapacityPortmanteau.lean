/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.CapacityLawDetermination
import Tengoku.Seed.MeasureTheory.Function.ConvergenceInDistribution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Portmanteau inequalities for random compact sets

Let `mu_i` and `mu` be probability laws on the Hausdorff/Vietoris
hyperspace `TopologicalSpace.NonemptyCompacts X`.  Weak convergence
`mu_i -> mu`, expressed by Mathlib's topology on `ProbabilityMeasure`,
implies the classical capacity inequalities

* `mu(hit U) <= liminf_i mu_i(hit U)` for open `U`;
* `limsup_i mu_i(hit F) <= mu(hit F)` for closed `F`, hence for compact
  `F`;
* convergence of the hitting probabilities whenever the corresponding
  hyperspace hitting event has `mu`-null frontier.

The last section transports the same statements through Mathlib's
`TendstoInDistribution` structure.  In particular, it applies directly to
the measurable hyperspace-valued realizations of compact-valued Effros
correspondences constructed in `MeasurableHyperspace`.

These are only the forward Portmanteau implications.  No converse
criterion for convergence of random compact sets is claimed here.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

noncomputable section

namespace RandomSetTheory

variable {X : Type*}

/-! ## Portmanteau for probability laws on the hyperspace -/

/-- Under weak convergence of laws on nonempty compact sets, the limiting
probability of hitting an open test set is bounded above by the liminf of
the approximating hitting probabilities.
@isnad1 id=le.2h6v.s8.5ad7416b9ad0 from=translated src=- shape=03d2416a vocab=da7559b9
-/
theorem le_liminf_measure_hyperspaceHitEvent_open_of_tendsto
    {ι : Type*} {L : Filter ι}
    [MetricSpace X]
    [MeasurableSpace (NonemptyCompacts X)]
    [BorelSpace (NonemptyCompacts X)]
    {μ : ProbabilityMeasure (NonemptyCompacts X)}
    {μs : ι → ProbabilityMeasure (NonemptyCompacts X)}
    (hμ : Tendsto μs L (𝓝 μ)) {U : Set X} (hU : IsOpen U) :
    (μ : Measure (NonemptyCompacts X)) (hyperspaceHitEvent U) ≤
      L.liminf (fun i =>
        (μs i : Measure (NonemptyCompacts X)) (hyperspaceHitEvent U)) := by
  exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ
    (TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU)

/-- Under weak convergence of laws on nonempty compact sets, the limsup of
the probabilities of hitting a closed test set is bounded above by the
limiting hitting probability.
@isnad1 id=le.2h6v.s8.e43d9530701b from=translated src=- shape=65a8f54b vocab=818f80d1
-/
theorem limsup_measure_hyperspaceHitEvent_closed_le_of_tendsto
    {ι : Type*} {L : Filter ι}
    [MetricSpace X]
    [MeasurableSpace (NonemptyCompacts X)]
    [BorelSpace (NonemptyCompacts X)]
    {μ : ProbabilityMeasure (NonemptyCompacts X)}
    {μs : ι → ProbabilityMeasure (NonemptyCompacts X)}
    (hμ : Tendsto μs L (𝓝 μ)) {F : Set X} (hF : IsClosed F) :
    L.limsup (fun i =>
        (μs i : Measure (NonemptyCompacts X)) (hyperspaceHitEvent F)) ≤
      (μ : Measure (NonemptyCompacts X)) (hyperspaceHitEvent F) := by
  exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ
    (TopologicalSpace.NonemptyCompacts.isClosed_inter_nonempty_of_isClosed hF)

/-- Compact-test form of
`limsup_measure_hyperspaceHitEvent_closed_le_of_tendsto`.
@isnad1 id=le.2h6v.s8.4255f0b49ec3 from=translated src=- shape=65a8f54b vocab=9403e2e3
-/
theorem limsup_measure_hyperspaceHitEvent_compact_le_of_tendsto
    {ι : Type*} {L : Filter ι}
    [MetricSpace X]
    [MeasurableSpace (NonemptyCompacts X)]
    [BorelSpace (NonemptyCompacts X)]
    {μ : ProbabilityMeasure (NonemptyCompacts X)}
    {μs : ι → ProbabilityMeasure (NonemptyCompacts X)}
    (hμ : Tendsto μs L (𝓝 μ)) {K : Set X} (hK : IsCompact K) :
    L.limsup (fun i =>
        (μs i : Measure (NonemptyCompacts X)) (hyperspaceHitEvent K)) ≤
      (μ : Measure (NonemptyCompacts X)) (hyperspaceHitEvent K) :=
  limsup_measure_hyperspaceHitEvent_closed_le_of_tendsto hμ hK.isClosed

/-- Weakly convergent hyperspace laws give convergent hitting
probabilities at every hitting event whose frontier is null under the
limiting law.
@isnad1 id=tendsto.2h6v.s8.ab818957dc00 from=translated src=- shape=6a932886 vocab=00d60c2c
-/
theorem tendsto_measure_hyperspaceHitEvent_of_null_frontier_of_tendsto
    {ι : Type*} {L : Filter ι}
    [MetricSpace X]
    [MeasurableSpace (NonemptyCompacts X)]
    [BorelSpace (NonemptyCompacts X)]
    {μ : ProbabilityMeasure (NonemptyCompacts X)}
    {μs : ι → ProbabilityMeasure (NonemptyCompacts X)}
    (hμ : Tendsto μs L (𝓝 μ)) {A : Set X}
    (hA : (μ : Measure (NonemptyCompacts X))
      (frontier (hyperspaceHitEvent A)) = 0) :
    Tendsto
      (fun i =>
        (μs i : Measure (NonemptyCompacts X)) (hyperspaceHitEvent A)) L
      (𝓝 ((μ : Measure (NonemptyCompacts X))
        (hyperspaceHitEvent A))) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ hA

/-! ## Random variables with values in the hyperspace -/

section TendstoInDistribution

variable [MetricSpace X]
  [MeasurableSpace (NonemptyCompacts X)]
  [BorelSpace (NonemptyCompacts X)]
  {ι Ω' : Type*} {Ω : ι → Type*}
  {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {K : (i : ι) → Ω i → NonemptyCompacts X}
  {Klim : Ω' → NonemptyCompacts X} {L : Filter ι}

/-- Portmanteau's open-set inequality, written as an inequality between
capacity functionals of hyperspace-valued random variables.
@isnad1 id=le.2h12v.s7.d28282cef270 from=translated src=- shape=2c1b509b vocab=2c39dccf
-/
theorem le_liminf_capacityFunctional_open_of_tendstoInDistribution
    (hK : TendstoInDistribution K L Klim μ μ')
    {U : Set X} (hU : IsOpen U) :
    capacityFunctional μ' (fun ω => (Klim ω : Set X)) U ≤
      L.liminf (fun i =>
        capacityFunctional (μ i) (fun ω => (K i ω : Set X)) U) := by
  have hport := le_liminf_measure_hyperspaceHitEvent_open_of_tendsto
    hK.tendsto hU
  have hHit : MeasurableSet (hyperspaceHitEvent (X := X) U) :=
    (TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).measurableSet
  simp only [ProbabilityMeasure.coe_mk] at hport
  rw [Measure.map_apply_of_aemeasurable hK.aemeasurable_limit hHit] at hport
  simp_rw [Measure.map_apply_of_aemeasurable (hK.forall_aemeasurable _) hHit] at hport
  simpa only [capacityFunctional, hitEvent, hyperspaceHitEvent,
    Set.preimage_ofPred_eq] using hport

/-- Portmanteau's closed-set inequality, written as an inequality between
capacity functionals of hyperspace-valued random variables.
@isnad1 id=le.2h12v.s7.40efeb075901 from=translated src=- shape=7211c14a vocab=ccc8cb1b
-/
theorem limsup_capacityFunctional_closed_le_of_tendstoInDistribution
    (hK : TendstoInDistribution K L Klim μ μ')
    {F : Set X} (hF : IsClosed F) :
    L.limsup (fun i =>
        capacityFunctional (μ i) (fun ω => (K i ω : Set X)) F) ≤
      capacityFunctional μ' (fun ω => (Klim ω : Set X)) F := by
  have hport := limsup_measure_hyperspaceHitEvent_closed_le_of_tendsto
    hK.tendsto hF
  have hHit : MeasurableSet (hyperspaceHitEvent (X := X) F) :=
    (TopologicalSpace.NonemptyCompacts.isClosed_inter_nonempty_of_isClosed hF).measurableSet
  simp only [ProbabilityMeasure.coe_mk] at hport
  rw [Measure.map_apply_of_aemeasurable hK.aemeasurable_limit hHit] at hport
  simp_rw [Measure.map_apply_of_aemeasurable (hK.forall_aemeasurable _) hHit] at hport
  simpa only [capacityFunctional, hitEvent, hyperspaceHitEvent,
    Set.preimage_ofPred_eq] using hport

/-- Compact-test form of
`TendstoInDistribution.limsup_capacityFunctional_closed_le`.
@isnad1 id=le.2h12v.s7.8c4871a2dcc0 from=translated src=- shape=7211c14a vocab=1017991d
-/
theorem limsup_capacityFunctional_compact_le_of_tendstoInDistribution
    (hK : TendstoInDistribution K L Klim μ μ')
    {A : Set X} (hA : IsCompact A) :
    L.limsup (fun i =>
        capacityFunctional (μ i) (fun ω => (K i ω : Set X)) A) ≤
      capacityFunctional μ' (fun ω => (Klim ω : Set X)) A :=
  limsup_capacityFunctional_closed_le_of_tendstoInDistribution hK hA.isClosed

/-- At a hyperspace hitting event which is measurable and has null frontier
under the limiting law, convergence in distribution gives convergence of
the corresponding capacity functionals.
@isnad1 id=tendsto.3h12v.s8.5d438c98b99a from=translated src=- shape=4a3b457d vocab=98909b33
-/
theorem tendsto_capacityFunctional_of_null_frontier_of_tendstoInDistribution
    (hK : TendstoInDistribution K L Klim μ μ')
    {A : Set X}
    (hAmeas : MeasurableSet (hyperspaceHitEvent (X := X) A))
    (hAfrontier : μ'.map Klim
      (frontier (hyperspaceHitEvent A)) = 0) :
    Tendsto
      (fun i => capacityFunctional (μ i)
        (fun ω => (K i ω : Set X)) A) L
      (𝓝 (capacityFunctional μ'
        (fun ω => (Klim ω : Set X)) A)) := by
  have hport :=
    tendsto_measure_hyperspaceHitEvent_of_null_frontier_of_tendsto
      hK.tendsto hAfrontier
  simp only [ProbabilityMeasure.coe_mk] at hport
  rw [Measure.map_apply_of_aemeasurable hK.aemeasurable_limit hAmeas] at hport
  simp_rw [Measure.map_apply_of_aemeasurable (hK.forall_aemeasurable _) hAmeas] at hport
  simpa only [capacityFunctional, hitEvent, hyperspaceHitEvent,
    Set.preimage_ofPred_eq] using hport

/-- Open-test continuity-set form for hyperspace-valued convergence in
distribution.
@isnad1 id=tendsto.3h12v.s8.fab4c0425132 from=translated src=- shape=a7eb4c20 vocab=e211a864
-/
theorem tendsto_capacityFunctional_open_of_null_frontier_of_tendstoInDistribution
    (hK : TendstoInDistribution K L Klim μ μ')
    {U : Set X} (hU : IsOpen U)
    (hUfrontier : μ'.map Klim
      (frontier (hyperspaceHitEvent U)) = 0) :
    Tendsto
      (fun i => capacityFunctional (μ i)
        (fun ω => (K i ω : Set X)) U) L
      (𝓝 (capacityFunctional μ'
        (fun ω => (Klim ω : Set X)) U)) :=
  tendsto_capacityFunctional_of_null_frontier_of_tendstoInDistribution hK
    (TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).measurableSet
    hUfrontier

/-- Closed-test continuity-set form for hyperspace-valued convergence in
distribution.
@isnad1 id=tendsto.3h12v.s8.7e53bf1ea0d6 from=translated src=- shape=a7eb4c20 vocab=15c7300c
-/
theorem tendsto_capacityFunctional_closed_of_null_frontier_of_tendstoInDistribution
    (hK : TendstoInDistribution K L Klim μ μ')
    {F : Set X} (hF : IsClosed F)
    (hFfrontier : μ'.map Klim
      (frontier (hyperspaceHitEvent F)) = 0) :
    Tendsto
      (fun i => capacityFunctional (μ i)
        (fun ω => (K i ω : Set X)) F) L
      (𝓝 (capacityFunctional μ'
        (fun ω => (Klim ω : Set X)) F)) :=
  tendsto_capacityFunctional_of_null_frontier_of_tendstoInDistribution hK
    (TopologicalSpace.NonemptyCompacts.isClosed_inter_nonempty_of_isClosed hF).measurableSet
    hFfrontier

/-- Compact-test continuity-set form for hyperspace-valued convergence in
distribution.
@isnad1 id=tendsto.3h12v.s8.68060a28cd2d from=translated src=- shape=a7eb4c20 vocab=16a071d0
-/
theorem tendsto_capacityFunctional_compact_of_null_frontier_of_tendstoInDistribution
    (hK : TendstoInDistribution K L Klim μ μ')
    {A : Set X} (hA : IsCompact A)
    (hAfrontier : μ'.map Klim
      (frontier (hyperspaceHitEvent A)) = 0) :
    Tendsto
      (fun i => capacityFunctional (μ i)
        (fun ω => (K i ω : Set X)) A) L
      (𝓝 (capacityFunctional μ'
        (fun ω => (Klim ω : Set X)) A)) :=
  tendsto_capacityFunctional_closed_of_null_frontier_of_tendstoInDistribution
    hK hA.isClosed hAfrontier

end TendstoInDistribution

/-! ## Effros correspondences and their pushforward laws -/

section EffrosPushforward

variable {ι Ω Ω' : Type*} {L : Filter ι}
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace (NonemptyCompacts X)]
  [BorelSpace (NonemptyCompacts X)]

/-- Weak convergence of the explicit `ProbabilityMeasure.map` laws of
compact-valued Effros correspondences is exactly convergence in
distribution of their bundled hyperspace-valued realizations.

This is the bridge which lets all the capacity Portmanteau theorems above
be applied without introducing a separate notion of weak convergence for
random sets.
@isnad1 id=tendstoi.7h9v.s8.c8346c017998 from=translated src=- shape=b62a266f vocab=3d9889fb
-/
theorem tendstoInDistribution_bundleNonemptyCompacts_of_tendsto_map
    {νs : ι → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω'}
    {S : ι → Ω → Set X} {T : Ω' → Set X}
    (hS : ∀ i, RandomSet.IsEffrosMeasurable (S i))
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hTne : ∀ ω, (T ω).Nonempty)
    (hLaw : Tendsto
      (fun i => (νs i).map
        (measurable_bundleNonemptyCompacts
          (hS i) (hScompact i) (hSne i)).aemeasurable) L
      (𝓝 (ν.map
        (measurable_bundleNonemptyCompacts
          hT hTcompact hTne).aemeasurable))) :
    TendstoInDistribution
      (fun i => bundleNonemptyCompacts (S i) (hScompact i) (hSne i)) L
      (bundleNonemptyCompacts T hTcompact hTne)
      (fun i => (νs i : Measure Ω)) (ν : Measure Ω') := by
  refine
    { forall_aemeasurable := fun i =>
        (measurable_bundleNonemptyCompacts
          (hS i) (hScompact i) (hSne i)).aemeasurable
      aemeasurable_limit :=
        (measurable_bundleNonemptyCompacts
          hT hTcompact hTne).aemeasurable
      tendsto := ?_ }
  simpa only [ProbabilityMeasure.map] using hLaw

/-- Direct capacity form of Portmanteau for the pushforward laws of
compact-valued Effros correspondences.  It packages both the open-test
liminf inequality and the closed-test limsup inequality.
@isnad1 id=and.7h9v.s8.04ef1b66e2e4 from=translated src=- shape=cc1950d9 vocab=18ed6db2
-/
theorem capacity_portmanteau_effros_of_tendsto_map
    {νs : ι → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω'}
    {S : ι → Ω → Set X} {T : Ω' → Set X}
    (hS : ∀ i, RandomSet.IsEffrosMeasurable (S i))
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hTne : ∀ ω, (T ω).Nonempty)
    (hLaw : Tendsto
      (fun i => (νs i).map
        (measurable_bundleNonemptyCompacts
          (hS i) (hScompact i) (hSne i)).aemeasurable) L
      (𝓝 (ν.map
        (measurable_bundleNonemptyCompacts
          hT hTcompact hTne).aemeasurable))) :
    (∀ U : Set X, IsOpen U →
      capacityFunctional (ν : Measure Ω') T U ≤
        L.liminf (fun i =>
          capacityFunctional (νs i : Measure Ω) (S i) U)) ∧
    (∀ F : Set X, IsClosed F →
      L.limsup (fun i =>
          capacityFunctional (νs i : Measure Ω) (S i) F) ≤
        capacityFunctional (ν : Measure Ω') T F) := by
  have hDist :=
    tendstoInDistribution_bundleNonemptyCompacts_of_tendsto_map
      hS hT hScompact hTcompact hSne hTne hLaw
  constructor
  · intro U hU
    simpa only [coe_bundleNonemptyCompacts] using
      (le_liminf_capacityFunctional_open_of_tendstoInDistribution
        hDist hU)
  · intro F hF
    simpa only [coe_bundleNonemptyCompacts] using
      (limsup_capacityFunctional_closed_le_of_tendstoInDistribution
        hDist hF)

end EffrosPushforward

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
