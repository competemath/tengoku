/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableHyperspace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Determination of random-compact laws by hitting probabilities

Let `K` be a random nonempty compact subset of a second-countable metric
space.  This file proves the uniqueness half of the classical capacity
theorem: the probabilities that `K` hits deterministic open sets determine
the Borel law of `K` on `TopologicalSpace.NonemptyCompacts X`.

The proof is measure-theoretic and does not invoke an existence theorem for
capacities.  Its main ingredients are:

* the upper Vietoris events `{K | K ⊆ U}`, for `U` open, form a pi-system;
* their generated sigma-algebra is the full Borel sigma-algebra of the
  Vietoris/Hausdorff hyperspace;
* a closed hitting event is a decreasing intersection of open hitting
  events, because every value in the hyperspace is compact;
* finite-measure uniqueness on a generating pi-system.

Consequently equality of hitting probabilities on all open tests, or on all
closed tests, implies equality of the hyperspace laws.  On a compact ambient
space the closed-test formulation can of course be stated using only compact
tests.  No Choquet converse or capacity-existence result is claimed here.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory TopologicalSpace
open scoped ENNReal

noncomputable section

namespace RandomSetTheory

variable {Ω Ω' X : Type*}

/-! ## Vietoris events and their generated sigma-algebra -/

/-- The upper Vietoris event consisting of nonempty compact subsets of `U`.-/
def upperVietorisEvent [TopologicalSpace X] (U : Set X) :
    Set (NonemptyCompacts X) :=
  {K | (K : Set X) ⊆ U}

/-- The lower Vietoris, or hitting, event associated with `A`.-/
def hyperspaceHitEvent [TopologicalSpace X] (A : Set X) :
    Set (NonemptyCompacts X) :=
  {K | ((K : Set X) ∩ A).Nonempty}

/-- The collection of upper Vietoris events with open targets.-/
def upperVietorisOpenGenerator [TopologicalSpace X] :
    Set (Set (NonemptyCompacts X)) :=
  upperVietorisEvent '' {U : Set X | IsOpen U}

@[simp]
theorem upperVietorisEvent_univ [TopologicalSpace X] :
    upperVietorisEvent (X := X) Set.univ = Set.univ := by
  ext K
  simp [upperVietorisEvent]

theorem upperVietorisEvent_inter [TopologicalSpace X] (U V : Set X) :
    upperVietorisEvent (X := X) (U ∩ V) =
      upperVietorisEvent U ∩ upperVietorisEvent V := by
  ext K
  simp only [upperVietorisEvent, Set.mem_ofPred_eq, Set.mem_inter_iff]
  exact Set.subset_inter_iff

theorem hyperspaceHitEvent_mono [TopologicalSpace X] :
    Monotone (hyperspaceHitEvent (X := X)) := by
  intro A B hAB K
  rintro ⟨x, hxK, hxA⟩
  exact ⟨x, hxK, hAB hxA⟩

theorem hyperspaceHitEvent_iUnion [TopologicalSpace X]
    {ι : Sort*} (A : ι → Set X) :
    hyperspaceHitEvent (⋃ i, A i) =
      ⋃ i, hyperspaceHitEvent (A i) := by
  ext K
  constructor
  · rintro ⟨x, hxK, hxA⟩
    rcases Set.mem_iUnion.mp hxA with ⟨i, hxi⟩
    exact Set.mem_iUnion.mpr ⟨i, x, hxK, hxi⟩
  · intro hK
    rcases Set.mem_iUnion.mp hK with ⟨i, x, hxK, hxi⟩
    exact ⟨x, hxK, Set.mem_iUnion.mpr ⟨i, hxi⟩⟩

theorem hyperspaceHitEvent_eq_compl_upper_compl [TopologicalSpace X]
    (A : Set X) :
    hyperspaceHitEvent A = (upperVietorisEvent (X := X) Aᶜ)ᶜ := by
  ext K
  change ((K : Set X) ∩ A).Nonempty ↔ ¬(K : Set X) ⊆ Aᶜ
  constructor
  · rintro ⟨x, hxK, hxA⟩ hKA
    exact (hKA hxK) hxA
  · intro hnot
    by_contra hnone
    apply hnot
    intro x hxK hxA
    exact hnone ⟨x, hxK, hxA⟩

theorem upperVietorisEvent_eq_compl_hit_compl [TopologicalSpace X]
    (U : Set X) :
    upperVietorisEvent (X := X) U = (hyperspaceHitEvent Uᶜ)ᶜ := by
  rw [hyperspaceHitEvent_eq_compl_upper_compl]
  simp

/-- Closed inner approximations of an open set, used to recover lower
Vietoris events from the upper open generator.-/
private def metricInnerApprox [MetricSpace X] (U : Set X) (n : ℕ) : Set X :=
  (Metric.thickening (1 / (n + 1 : ℝ)) Uᶜ)ᶜ

private theorem iUnion_metricInnerApprox_eq [MetricSpace X]
    {U : Set X} (hU : IsOpen U) :
    ⋃ n : ℕ, metricInnerApprox U n = U := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
    by_contra hxU
    exact hxn (Metric.self_subset_thickening
      (by positivity : 0 < 1 / (n + 1 : ℝ)) Uᶜ hxU)
  · intro hxU
    obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hU) x hxU
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    intro hxthick
    rcases Metric.mem_thickening_iff.mp hxthick with ⟨z, hzUc, hxz⟩
    have hzball : z ∈ Metric.ball x ε := by
      simpa only [Metric.mem_ball, dist_comm] using lt_trans hxz hn
    exact hzUc (hball hzball)

private theorem measurableSet_upperVietorisEvent_generate
    [TopologicalSpace X] {U : Set X} (hU : IsOpen U) :
    @MeasurableSet (NonemptyCompacts X)
      (MeasurableSpace.generateFrom (upperVietorisOpenGenerator (X := X)))
      (upperVietorisEvent U) :=
  MeasurableSpace.measurableSet_generateFrom ⟨U, hU, rfl⟩

private theorem measurableSet_hyperspaceHitEvent_open_generate
    [MetricSpace X] {U : Set X} (hU : IsOpen U) :
    @MeasurableSet (NonemptyCompacts X)
      (MeasurableSpace.generateFrom (upperVietorisOpenGenerator (X := X)))
      (hyperspaceHitEvent U) := by
  rw [← iUnion_metricInnerApprox_eq hU, hyperspaceHitEvent_iUnion]
  apply MeasurableSet.iUnion
  intro n
  rw [hyperspaceHitEvent_eq_compl_upper_compl]
  apply MeasurableSet.compl
  apply measurableSet_upperVietorisEvent_generate
  simpa only [metricInnerApprox, compl_compl] using
    (Metric.isOpen_thickening :
      IsOpen (Metric.thickening (1 / (n + 1 : ℝ)) Uᶜ))

/-- The open upper Vietoris events form a pi-system.-/
theorem isPiSystem_upperVietorisOpenGenerator [TopologicalSpace X] :
    IsPiSystem (upperVietorisOpenGenerator (X := X)) := by
  intro A hA B hB _hne
  rcases hA with ⟨U, hU, rfl⟩
  rcases hB with ⟨V, hV, rfl⟩
  refine ⟨U ∩ V, hU.inter hV, ?_⟩
  exact upperVietorisEvent_inter U V

/-- In a second-countable metric space, upper Vietoris events alone generate
the Borel sigma-algebra on nonempty compact sets.

This is a statement about sigma-algebras, not topologies: lower Vietoris
opens are recovered as countable unions of complements of upper events by
using metric inner approximations.-/
theorem borel_nonemptyCompacts_eq_generateFrom_upperVietoris
    [MetricSpace X] [SecondCountableTopology X] :
    borel (NonemptyCompacts X) =
      MeasurableSpace.generateFrom (upperVietorisOpenGenerator (X := X)) := by
  let C : Set (Set (NonemptyCompacts X)) :=
    (fun u => {K : NonemptyCompacts X |
      (K : Set X) ⊆ ⋃₀ u ∧
        ∀ U ∈ u, ((K : Set X) ∩ U).Nonempty}) ''
      {u : Set (Set X) | u.Finite ∧ u.Nonempty ∧ ∀ U ∈ u, IsOpen U}
  have hCbasis : IsTopologicalBasis C := by
    simpa only [C] using
      (TopologicalSpace.NonemptyCompacts.isTopologicalBasis (α := X))
  apply le_antisymm
  · rw [hCbasis.borel_eq_generateFrom]
    apply MeasurableSpace.generateFrom_le
    intro W hW
    rcases hW with ⟨u, hu, rfl⟩
    have hUnionOpen : IsOpen (⋃₀ u) :=
      isOpen_sUnion fun U hU => hu.2.2 U hU
    have hUpper : @MeasurableSet (NonemptyCompacts X)
        (MeasurableSpace.generateFrom
          (upperVietorisOpenGenerator (X := X)))
        (upperVietorisEvent (⋃₀ u)) :=
      measurableSet_upperVietorisEvent_generate hUnionOpen
    letI := hu.1.to_subtype
    have hLower : @MeasurableSet (NonemptyCompacts X)
        (MeasurableSpace.generateFrom
          (upperVietorisOpenGenerator (X := X)))
        (⋂ U : u, hyperspaceHitEvent (U : Set X)) :=
      MeasurableSet.iInter fun U =>
        measurableSet_hyperspaceHitEvent_open_generate
          (hu.2.2 U U.property)
    have hEq :
        {K : NonemptyCompacts X |
          (K : Set X) ⊆ ⋃₀ u ∧
            ∀ U ∈ u, ((K : Set X) ∩ U).Nonempty} =
          upperVietorisEvent (⋃₀ u) ∩
            ⋂ U : u, hyperspaceHitEvent (U : Set X) := by
      ext K
      simp only [upperVietorisEvent, hyperspaceHitEvent, Set.mem_ofPred_eq,
        Set.mem_inter_iff, Set.mem_iInter]
      exact and_congr_right fun _ => by
        constructor
        · intro h U
          exact h U U.property
        · intro h U hU
          exact h ⟨U, hU⟩
    change @MeasurableSet (NonemptyCompacts X)
      (MeasurableSpace.generateFrom
        (upperVietorisOpenGenerator (X := X)))
      {K : NonemptyCompacts X |
        (K : Set X) ⊆ ⋃₀ u ∧
          ∀ U ∈ u, ((K : Set X) ∩ U).Nonempty}
    rw [hEq]
    exact hUpper.inter hLower
  · apply MeasurableSpace.generateFrom_le
    intro W hW
    rcases hW with ⟨U, hU, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom
      (TopologicalSpace.NonemptyCompacts.isOpen_subsets_of_isOpen hU)

/-! ## Uniqueness of finite hyperspace laws -/

/-- Equality on all closed hitting events determines a finite hyperspace
law, once the total masses agree.-/
theorem measure_nonemptyCompacts_eq_of_hit_closed_eq
    [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace (NonemptyCompacts X)]
    [BorelSpace (NonemptyCompacts X)]
    {μ ν : Measure (NonemptyCompacts X)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_univ : μ Set.univ = ν Set.univ)
    (h_hit : ∀ F : Set X, IsClosed F →
      μ (hyperspaceHitEvent F) = ν (hyperspaceHitEvent F)) :
    μ = ν := by
  apply MeasureTheory.ext_of_generate_finite
    (upperVietorisOpenGenerator (X := X))
    (BorelSpace.measurable_eq.trans
      borel_nonemptyCompacts_eq_generateFrom_upperVietoris)
    isPiSystem_upperVietorisOpenGenerator
  · intro A hA
    rcases hA with ⟨U, hU, rfl⟩
    have hFmeas : MeasurableSet (hyperspaceHitEvent (X := X) Uᶜ) :=
      (TopologicalSpace.NonemptyCompacts.isClosed_inter_nonempty_of_isClosed
        hU.isClosed_compl).measurableSet
    rw [upperVietorisEvent_eq_compl_hit_compl,
      measure_compl hFmeas (by finiteness),
      measure_compl hFmeas (by finiteness), h_univ,
      h_hit Uᶜ hU.isClosed_compl]
  · exact h_univ

/-- Equality on all open hitting events determines a finite hyperspace law.

Closed hitting probabilities are first recovered by continuity from above
along the open thickenings of the closed test.-/
theorem measure_nonemptyCompacts_eq_of_hit_open_eq
    [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace (NonemptyCompacts X)]
    [BorelSpace (NonemptyCompacts X)]
    {μ ν : Measure (NonemptyCompacts X)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_univ : μ Set.univ = ν Set.univ)
    (h_hit : ∀ U : Set X, IsOpen U →
      μ (hyperspaceHitEvent U) = ν (hyperspaceHitEvent U)) :
    μ = ν := by
  apply measure_nonemptyCompacts_eq_of_hit_closed_eq h_univ
  intro F hF
  let A : ℕ → Set (NonemptyCompacts X) := fun n =>
    hyperspaceHitEvent
      (Metric.thickening (1 / (n + 1 : ℝ)) F)
  have hAeq : hyperspaceHitEvent (X := X) F = ⋂ n, A n := by
    simpa only [A, hyperspaceHitEvent, hitEvent] using
      (hitEvent_closed_eq_iInter_thickening_of_compact_values
        (S := fun K : NonemptyCompacts X => (K : Set X))
        (fun K => K.isCompact) hF)
  have hAmeas : ∀ n, MeasurableSet (A n) := fun n =>
    (TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen
      Metric.isOpen_thickening).measurableSet
  have hAanti : Antitone A := by
    intro m n hmn
    exact hyperspaceHitEvent_mono
      (Metric.thickening_mono (Nat.one_div_le_one_div hmn) F)
  rw [hAeq,
    hAanti.measure_iInter (fun n => (hAmeas n).nullMeasurableSet)
      ⟨0, by finiteness⟩,
    hAanti.measure_iInter (fun n => (hAmeas n).nullMeasurableSet)
      ⟨0, by finiteness⟩]
  exact iInf_congr fun n =>
    h_hit _ Metric.isOpen_thickening

/-- On a compact ambient metric space, equality on compact hitting tests is
enough, since every closed test is compact.-/
theorem measure_nonemptyCompacts_eq_of_hit_compact_eq
    [MetricSpace X] [SecondCountableTopology X] [CompactSpace X]
    [MeasurableSpace (NonemptyCompacts X)]
    [BorelSpace (NonemptyCompacts X)]
    {μ ν : Measure (NonemptyCompacts X)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_univ : μ Set.univ = ν Set.univ)
    (h_hit : ∀ K : Set X, IsCompact K →
      μ (hyperspaceHitEvent K) = ν (hyperspaceHitEvent K)) :
    μ = ν :=
  measure_nonemptyCompacts_eq_of_hit_closed_eq h_univ fun F hF =>
    h_hit F hF.isCompact

/-! ## Random compact-valued correspondences -/

/-- Equality of open-set capacity functionals determines the pushforward
law of two nonempty compact-valued Effros correspondences.  The source
spaces and source measures may be different.-/
theorem map_bundleNonemptyCompacts_eq_of_capacity_open_eq
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace (NonemptyCompacts X)]
    [BorelSpace (NonemptyCompacts X)]
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Ω → Set X} {T : Ω' → Set X}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty)
    (hTne : ∀ ω, (T ω).Nonempty)
    (h_univ : μ Set.univ = ν Set.univ)
    (h_capacity : ∀ U : Set X, IsOpen U →
      capacityFunctional μ S U = capacityFunctional ν T U) :
    Measure.map (bundleNonemptyCompacts S hScompact hSne) μ =
      Measure.map (bundleNonemptyCompacts T hTcompact hTne) ν := by
  have hSmeas : Measurable (bundleNonemptyCompacts S hScompact hSne) :=
    measurable_bundleNonemptyCompacts hS hScompact hSne
  have hTmeas : Measurable (bundleNonemptyCompacts T hTcompact hTne) :=
    measurable_bundleNonemptyCompacts hT hTcompact hTne
  apply measure_nonemptyCompacts_eq_of_hit_open_eq
  · rw [Measure.map_apply hSmeas MeasurableSet.univ,
      Measure.map_apply hTmeas MeasurableSet.univ]
    simpa only [Set.preimage_univ] using h_univ
  · intro U hU
    have hHitMeas : MeasurableSet (hyperspaceHitEvent (X := X) U) :=
      (TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).measurableSet
    rw [Measure.map_apply hSmeas hHitMeas,
      Measure.map_apply hTmeas hHitMeas]
    simpa only [hyperspaceHitEvent, coe_bundleNonemptyCompacts,
      capacityFunctional, hitEvent, Set.preimage_ofPred_eq] using
      h_capacity U hU

/-- Closed-test version of law determination for random compact-valued
Effros correspondences.-/
theorem map_bundleNonemptyCompacts_eq_of_capacity_closed_eq
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace (NonemptyCompacts X)]
    [BorelSpace (NonemptyCompacts X)]
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Ω → Set X} {T : Ω' → Set X}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty)
    (hTne : ∀ ω, (T ω).Nonempty)
    (h_univ : μ Set.univ = ν Set.univ)
    (h_capacity : ∀ F : Set X, IsClosed F →
      capacityFunctional μ S F = capacityFunctional ν T F) :
    Measure.map (bundleNonemptyCompacts S hScompact hSne) μ =
      Measure.map (bundleNonemptyCompacts T hTcompact hTne) ν := by
  have hSmeas : Measurable (bundleNonemptyCompacts S hScompact hSne) :=
    measurable_bundleNonemptyCompacts hS hScompact hSne
  have hTmeas : Measurable (bundleNonemptyCompacts T hTcompact hTne) :=
    measurable_bundleNonemptyCompacts hT hTcompact hTne
  apply measure_nonemptyCompacts_eq_of_hit_closed_eq
  · rw [Measure.map_apply hSmeas MeasurableSet.univ,
      Measure.map_apply hTmeas MeasurableSet.univ]
    simpa only [Set.preimage_univ] using h_univ
  · intro F hF
    have hHitMeas : MeasurableSet (hyperspaceHitEvent (X := X) F) :=
      (TopologicalSpace.NonemptyCompacts.isClosed_inter_nonempty_of_isClosed hF).measurableSet
    rw [Measure.map_apply hSmeas hHitMeas,
      Measure.map_apply hTmeas hHitMeas]
    simpa only [hyperspaceHitEvent, coe_bundleNonemptyCompacts,
      capacityFunctional, hitEvent, Set.preimage_ofPred_eq] using
      h_capacity F hF

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
