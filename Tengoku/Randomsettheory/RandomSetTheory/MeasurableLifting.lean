/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.EffrosCaratheodory
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableMaximum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurable lifting through a Carathéodory map

Let `S(ω)` be a nonempty compact random set and let `φ(ω, x)` be measurable
in `(ω, x)` and continuous in `x`.  Given a measurable target `v(ω)`, this
file studies the exact inverse-image correspondence

`{x ∈ S(ω) | φ(ω, x) = v(ω)}`.

When these fibres are nonempty, they are compact and Effros measurable.
Kuratowski--Ryll-Nardzewski therefore gives a measurable latent lifting of
the target.  This is the measurable-lifting step used in sharp
observational/Aumann representations.

The Effros proof avoids projecting a measurable graph.  Instead it uses a
countable family of closed localizations of `S`: a constrained fibre hits an
open set exactly when one localized compact image of the nonnegative
residual `dist (φ(ω, x)) (v(ω))` has distance zero from zero.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory TopologicalSpace

noncomputable section

namespace RandomSetTheory

/-- The exact inverse-image correspondence of a measurable target through a
base-dependent map, restricted to the feasible correspondence `S`.-/
def measurableLiftingFiber
    {Ω X Y : Type*} (S : Ω → Set X) (φ : Ω × X → Y) (v : Ω → Y)
    (ω : Ω) : Set X :=
  S ω ∩ {x | φ (ω, x) = v ω}

@[simp]
theorem mem_measurableLiftingFiber
    {Ω X Y : Type*} {S : Ω → Set X} {φ : Ω × X → Y} {v : Ω → Y}
    {ω : Ω} {x : X} :
    x ∈ measurableLiftingFiber S φ v ω ↔
      x ∈ S ω ∧ φ (ω, x) = v ω :=
  Iff.rfl

theorem measurableLiftingFiber_subset
    {Ω X Y : Type*} (S : Ω → Set X) (φ : Ω × X → Y) (v : Ω → Y)
    (ω : Ω) :
    measurableLiftingFiber S φ v ω ⊆ S ω :=
  inter_subset_left

/-- Exact inverse-image fibres of a continuous map inside compact feasible
sets are compact.-/
theorem measurableLiftingFiber_isCompact
    {Ω X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {S : Ω → Set X} (hcompact : ∀ ω, IsCompact (S ω))
    {φ : Ω × X → Y} (hφcont : ∀ ω, Continuous fun x => φ (ω, x))
    (v : Ω → Y) (ω : Ω) :
    IsCompact (measurableLiftingFiber S φ v ω) := by
  exact (hcompact ω).inter_right
    (isClosed_eq (hφcont ω) continuous_const)

/-- Countable basis event witnessing that an exact lifting fibre hits an
open set through a compact localization.-/
def MeasurableLiftingBasisEvent
    {Ω X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    [SecondCountableTopology X] [Nonempty X]
    (S : Ω → Set X) (φ : Ω × X → Y) (v : Ω → Y)
    (U : Set X) (n m : ℕ) (ω : Ω) : Prop :=
  let q : X := denseSeq X n
  let r : ℝ := 1 / (m + 1 : ℝ)
  Metric.closedBall q r ⊆ U ∧
    (S ω ∩ Metric.ball q r).Nonempty ∧
      infDist 0
          ((fun x => dist (φ (ω, x)) (v ω)) ''
            castaingLocalization S q r ω) = 0

/-- The localized zero-residual basis events are measurable.-/
theorem measurableSet_measurableLiftingBasisEvent
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : Ω × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ ω, Continuous fun x => φ (ω, x))
    {v : Ω → Y} (hv : Measurable v)
    (U : Set X) (n m : ℕ) :
    MeasurableSet
      {ω | MeasurableLiftingBasisEvent S φ v U n m ω} := by
  let q : X := denseSeq X n
  let r : ℝ := 1 / (m + 1 : ℝ)
  let L : Ω → Set X := castaingLocalization S q r
  let ρ : Ω × X → ℝ := fun p => dist (φ p) (v p.1)
  have hLcompact : ∀ ω, IsCompact (L ω) :=
    castaingLocalization_isCompact hcompact q r
  have hLne : ∀ ω, (L ω).Nonempty :=
    castaingLocalization_nonempty hne q r
  have hLEffros : RandomSet.IsEffrosMeasurable L :=
    effros_castaingLocalization hS q r
  have hρmeas : Measurable ρ := by
    exact hφmeas.dist (hv.comp measurable_fst)
  have hρcont : ∀ ω, Continuous fun x => ρ (ω, x) := by
    intro ω
    simpa [ρ] using
      (hφcont ω).dist (continuous_const : Continuous fun _ : X => v ω)
  have himageEffros : RandomSet.IsEffrosMeasurable
      (fun ω => (fun x => ρ (ω, x)) '' L ω) :=
    effrosMeasurable_caratheodoryImage hLEffros
      (fun ω => (hLcompact ω).isClosed) hLne hρmeas hρcont
  have himageNe : ∀ ω, ((fun x => ρ (ω, x)) '' L ω).Nonempty :=
    fun ω => (hLne ω).image fun x => ρ (ω, x)
  have hlocalDist : Measurable
      (fun ω => infDist 0 ((fun x => ρ (ω, x)) '' L ω)) :=
    measurable_infDist_correspondence himageEffros himageNe 0
  have hhit : MeasurableSet {ω | (S ω ∩ Metric.ball q r).Nonempty} :=
    hS (Metric.ball q r) Metric.isOpen_ball
  by_cases hb : Metric.closedBall q r ⊆ U
  · have hEq :
        {ω | MeasurableLiftingBasisEvent S φ v U n m ω} =
          {ω | (S ω ∩ Metric.ball q r).Nonempty} ∩
            {ω | infDist 0 ((fun x => ρ (ω, x)) '' L ω) = 0} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨_, hhitω, hzero⟩
        exact ⟨by simpa [q, r] using hhitω,
          by simpa [L, ρ, q, r] using hzero⟩
      · rintro ⟨hhitω, hzero⟩
        exact ⟨by simpa [q, r] using hb,
          by simpa [q, r] using hhitω,
          by simpa [L, ρ, q, r] using hzero⟩
    rw [hEq]
    exact hhit.inter (measurableSet_eq_fun hlocalDist measurable_const)
  · have hempty :
        {ω | MeasurableLiftingBasisEvent S φ v U n m ω} =
          (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      constructor
      · intro hω
        exact (hb (by simpa [q, r] using hω.1)).elim
      · exact False.elim
    rw [hempty]
    exact MeasurableSet.empty

/-- **Effros measurability of exact Carathéodory inverse images.**  The zero
fibre of a jointly measurable, fibrewise continuous map inside a compact
random set is again an Effros-measurable correspondence.  The zero fibre is
allowed to be empty; nonemptiness is needed only for measurable selection.-/
theorem effrosMeasurable_measurableLiftingFiber
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : Ω × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ ω, Continuous fun x => φ (ω, x))
    {v : Ω → Y} (hv : Measurable v) :
    RandomSet.IsEffrosMeasurable (measurableLiftingFiber S φ v) := by
  intro U hU
  have hEq :
      {ω | (measurableLiftingFiber S φ v ω ∩ U).Nonempty} =
        ⋃ n : ℕ, ⋃ m : ℕ,
          {ω | MeasurableLiftingBasisEvent S φ v U n m ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hxFiber, hxU⟩
      obtain ⟨n, m, hxball, hclosedBall⟩ :=
        exists_denseSeq_ball_closedBall_subset hU hxU
      let q : X := denseSeq X n
      let r : ℝ := 1 / (m + 1 : ℝ)
      have hhit : (S ω ∩ Metric.ball q r).Nonempty :=
        ⟨x, hxFiber.1, by simpa [q, r] using hxball⟩
      have hxlocal : x ∈ castaingLocalization S q r ω := by
        rw [castaingLocalization, ite_eq_left hhit]
        exact subset_closure ⟨hxFiber.1, by simpa [q, r] using hxball⟩
      have hzeroMem : (0 : ℝ) ∈
          (fun z => dist (φ (ω, z)) (v ω)) ''
            castaingLocalization S q r ω := by
        refine ⟨x, hxlocal, ?_⟩
        change dist (φ (ω, x)) (v ω) = 0
        rw [hxFiber.2]
        exact dist_self _
      refine ⟨n, m, ?_⟩
      exact ⟨by simpa [q, r] using hclosedBall,
        by simpa [q, r] using hhit,
        by simpa [q, r] using Metric.infDist_zero_of_mem hzeroMem⟩
    · rintro ⟨n, m, hbasis, hhit, hzero⟩
      let q : X := denseSeq X n
      let r : ℝ := 1 / (m + 1 : ℝ)
      let L : Set X := castaingLocalization S q r ω
      let ρ : X → ℝ := fun x => dist (φ (ω, x)) (v ω)
      have hhit' : (S ω ∩ Metric.ball q r).Nonempty := by
        simpa [q, r] using hhit
      have hLcompact : IsCompact L := by
        simpa [L] using castaingLocalization_isCompact hcompact q r ω
      have hLne : L.Nonempty := by
        simpa [L] using castaingLocalization_nonempty hne q r ω
      have hρcont : Continuous ρ := by
        simpa [ρ] using
          (hφcont ω).dist (continuous_const : Continuous fun _ : X => v ω)
      have himageCompact : IsCompact (ρ '' L) := hLcompact.image hρcont
      have himageNe : (ρ '' L).Nonempty := hLne.image ρ
      have hzero' : infDist 0 (ρ '' L) = 0 := by
        simpa [L, ρ, q, r] using hzero
      have hzeroMem : (0 : ℝ) ∈ ρ '' L :=
        (himageCompact.isClosed.mem_iff_infDist_zero himageNe).2 hzero'
      rcases hzeroMem with ⟨x, hxL, hρx⟩
      have hxS : x ∈ S ω :=
        castaingLocalization_subset
          (fun ω => (hcompact ω).isClosed) q r ω (by simpa [L] using hxL)
      have hxclosure : x ∈ closure (S ω ∩ Metric.ball q r) := by
        have : x ∈ castaingLocalization S q r ω := by simpa [L] using hxL
        simpa [castaingLocalization, hhit'] using this
      have hxclosedBall : x ∈ Metric.closedBall q r :=
        closure_minimal
          (inter_subset_right.trans Metric.ball_subset_closedBall)
          Metric.isClosed_closedBall hxclosure
      have hφx : φ (ω, x) = v ω := by
        apply dist_eq_zero.mp
        simpa [ρ] using hρx
      refine ⟨x, ⟨hxS, hφx⟩, ?_⟩
      have hbasis' : Metric.closedBall q r ⊆ U := by
        simpa [q, r] using hbasis
      exact hbasis' hxclosedBall
  rw [hEq]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
    measurableSet_measurableLiftingBasisEvent
      hS hcompact hne hφmeas hφcont hv U n m

/-- Canonical measurable lifting selected from the exact inverse-image
correspondence.-/
def measurableLiftingSelection
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : Ω × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ ω, Continuous fun x => φ (ω, x))
    {v : Ω → Y} (hv : Measurable v)
    (hfiberNe : ∀ ω, (measurableLiftingFiber S φ v ω).Nonempty) : Ω → X :=
  krnSelection
    (effrosMeasurable_measurableLiftingFiber hS hcompact hne
      hφmeas hφcont hv)
    hfiberNe

/-- The canonical lifting is measurable.-/
theorem measurable_measurableLiftingSelection
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : Ω × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ ω, Continuous fun x => φ (ω, x))
    {v : Ω → Y} (hv : Measurable v)
    (hfiberNe : ∀ ω, (measurableLiftingFiber S φ v ω).Nonempty) :
    Measurable
      (measurableLiftingSelection hS hcompact hne hφmeas hφcont hv hfiberNe) :=
  (kuratowski_ryll_nardzewski
    (effrosMeasurable_measurableLiftingFiber hS hcompact hne
      hφmeas hφcont hv)
    (fun ω => (measurableLiftingFiber_isCompact hcompact hφcont v ω).isClosed)
    hfiberNe).1

/-- The canonical lifting belongs to `S` and maps exactly to the prescribed
target in every fibre.-/
theorem measurableLiftingSelection_mem_and_map_eq
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : Ω × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ ω, Continuous fun x => φ (ω, x))
    {v : Ω → Y} (hv : Measurable v)
    (hfiberNe : ∀ ω, (measurableLiftingFiber S φ v ω).Nonempty)
    (ω : Ω) :
    measurableLiftingSelection hS hcompact hne hφmeas hφcont hv hfiberNe ω ∈ S ω ∧
      φ (ω,
          measurableLiftingSelection hS hcompact hne hφmeas hφcont hv hfiberNe ω) =
        v ω :=
  (kuratowski_ryll_nardzewski
    (effrosMeasurable_measurableLiftingFiber hS hcompact hne
      hφmeas hφcont hv)
    (fun ω => (measurableLiftingFiber_isCompact hcompact hφcont v ω).isClosed)
    hfiberNe).2 ω

/-- Existential measurable-lifting theorem in the form most directly used
by sharp representation arguments.-/
theorem exists_measurable_lifting
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : Ω × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ ω, Continuous fun x => φ (ω, x))
    {v : Ω → Y} (hv : Measurable v)
    (hfiberNe : ∀ ω, (measurableLiftingFiber S φ v ω).Nonempty) :
    ∃ T : Ω → X, Measurable T ∧
      ∀ ω, T ω ∈ S ω ∧ φ (ω, T ω) = v ω := by
  refine ⟨measurableLiftingSelection hS hcompact hne
      hφmeas hφcont hv hfiberNe,
    measurable_measurableLiftingSelection hS hcompact hne
      hφmeas hφcont hv hfiberNe, ?_⟩
  exact measurableLiftingSelection_mem_and_map_eq hS hcompact hne
    hφmeas hφcont hv hfiberNe

/-- A directly usable lifting theorem for a measurable selection of the
Carathéodory image.  Pointwise membership in the image discharges the
nonemptiness of every exact inverse-image fibre.-/
theorem exists_measurable_lifting_of_mem_image
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : Ω × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ ω, Continuous fun x => φ (ω, x))
    {v : Ω → Y} (hv : Measurable v)
    (hvmem : ∀ ω, v ω ∈ (fun x => φ (ω, x)) '' S ω) :
    ∃ T : Ω → X, Measurable T ∧
      ∀ ω, T ω ∈ S ω ∧ φ (ω, T ω) = v ω := by
  apply exists_measurable_lifting hS hcompact hne hφmeas hφcont hv
  intro ω
  rcases hvmem ω with ⟨x, hxS, hxφ⟩
  exact ⟨x, hxS, hxφ⟩

/-- The feasibility event of the exact inverse-image problem is measurable.
This is the key fact allowing an almost-surely feasible target to be
totalized on a measurable null exceptional set.-/
theorem measurableSet_measurableLiftingFiber_nonempty
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : Ω × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ ω, Continuous fun x => φ (ω, x))
    {v : Ω → Y} (hv : Measurable v) :
    MeasurableSet
      {ω | (measurableLiftingFiber S φ v ω).Nonempty} := by
  have hFiber := effrosMeasurable_measurableLiftingFiber
    hS hcompact hne hφmeas hφcont hv
  simpa only [inter_univ] using hFiber (Set.univ : Set X) isOpen_univ

/-- **Almost-sure measurable lifting.**  If the measurable target belongs
to the Carathéodory image almost surely, there is a globally measurable
map which belongs to `S` everywhere and lifts the prescribed target almost
surely.

On the measurable exceptional set where the original inverse-image fibre
is empty, the proof first selects a measurable fallback point of `S` by KRN
and replaces the target by its image.  The modified exact fibre is therefore
nonempty everywhere, so the pointwise lifting theorem applies.-/
theorem exists_measurable_lifting_of_ae_mem_image
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {μ : Measure Ω}
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : Ω × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ ω, Continuous fun x => φ (ω, x))
    {v : Ω → Y} (hv : Measurable v)
    (hvmem : ∀ᵐ ω ∂μ, v ω ∈ (fun x => φ (ω, x)) '' S ω) :
    ∃ T : Ω → X, Measurable T ∧
      (∀ ω, T ω ∈ S ω) ∧
        ∀ᵐ ω ∂μ, φ (ω, T ω) = v ω := by
  classical
  let A : Set Ω :=
    {ω | (measurableLiftingFiber S φ v ω).Nonempty}
  have hAmeas : MeasurableSet A := by
    simpa only [A] using
      measurableSet_measurableLiftingFiber_nonempty
        hS hcompact hne hφmeas hφcont hv
  let f₀ : Ω → X := krnSelection hS hne
  have hf₀sel : IsMeasurableSelection S f₀ := by
    simpa only [f₀] using
      kuratowski_ryll_nardzewski hS
        (fun ω => (hcompact ω).isClosed) hne
  have hφf₀ : Measurable (fun ω => φ (ω, f₀ ω)) :=
    hφmeas.comp (measurable_id.prodMk hf₀sel.1)
  let v' : Ω → Y := A.piecewise v (fun ω => φ (ω, f₀ ω))
  have hv' : Measurable v' := by
    simpa only [v'] using
      Measurable.piecewise hAmeas hv hφf₀
  have hv'fiberNe : ∀ ω,
      (measurableLiftingFiber S φ v' ω).Nonempty := by
    intro ω
    by_cases hω : ω ∈ A
    · have hneω : (measurableLiftingFiber S φ v ω).Nonempty := by
        simpa only [A, Set.mem_ofPred_eq] using hω
      rcases hneω with ⟨x, hxS, hxφ⟩
      refine ⟨x, hxS, ?_⟩
      simpa [v', Set.piecewise, hω] using hxφ
    · refine ⟨f₀ ω, hf₀sel.2 ω, ?_⟩
      simp [v', hω]
  obtain ⟨T, hTmeas, hTprop⟩ :=
    exists_measurable_lifting hS hcompact hne
      hφmeas hφcont hv' hv'fiberNe
  have hAae : ∀ᵐ ω ∂μ, ω ∈ A := by
    filter_upwards [hvmem] with ω hω
    rcases hω with ⟨x, hxS, hxφ⟩
    change (measurableLiftingFiber S φ v ω).Nonempty
    exact ⟨x, hxS, hxφ⟩
  refine ⟨T, hTmeas, fun ω => (hTprop ω).1, ?_⟩
  filter_upwards [hAae] with ω hω
  calc
    φ (ω, T ω) = v' ω := (hTprop ω).2
    _ = v ω := by simp [v', hω]

/-!
## Parameter-dependent lifting

The following wrappers keep the feasible random set indexed only by `ω`,
while both the observation map and the target may additionally depend on a
measurable parameter `θ`.
-/

/-- Effros measurability of parameter-dependent exact inverse-image fibres.
This is the correspondence on `Ω × Θ` whose value at `(ω, θ)` consists of
the points `x ∈ S(ω)` satisfying `φ((ω, θ), x) = v(ω, θ)`.-/
theorem effrosMeasurable_measurableLiftingFiber_param
    {Ω Θ X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : (Ω × Θ) × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ p : Ω × Θ, Continuous fun x => φ (p, x))
    {v : Ω × Θ → Y} (hv : Measurable v) :
    RandomSet.IsEffrosMeasurable
      (measurableLiftingFiber (fun p : Ω × Θ => S p.1) φ v) := by
  have hSlift : RandomSet.IsEffrosMeasurable
      (fun p : Ω × Θ => S p.1) := by
    intro U hU
    have hEq :
        {p : Ω × Θ | (S p.1 ∩ U).Nonempty} =
          Prod.fst ⁻¹' {ω | (S ω ∩ U).Nonempty} := by
      ext p
      rfl
    rw [hEq]
    exact measurable_fst (hS U hU)
  exact effrosMeasurable_measurableLiftingFiber hSlift
    (fun p => hcompact p.1) (fun p => hne p.1) hφmeas hφcont hv

/-- Parameter-dependent measurable lifting.  If every observational fibre
is nonempty, one can choose its latent representative jointly measurably in
`(ω, θ)`.-/
theorem exists_measurable_lifting_param
    {Ω Θ X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : (Ω × Θ) × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ p : Ω × Θ, Continuous fun x => φ (p, x))
    {v : Ω × Θ → Y} (hv : Measurable v)
    (hfiberNe : ∀ p : Ω × Θ,
      (measurableLiftingFiber (fun q : Ω × Θ => S q.1) φ v p).Nonempty) :
    ∃ T : Ω × Θ → X, Measurable T ∧
      ∀ p : Ω × Θ, T p ∈ S p.1 ∧ φ (p, T p) = v p := by
  have hSlift : RandomSet.IsEffrosMeasurable
      (fun p : Ω × Θ => S p.1) := by
    intro U hU
    have hEq :
        {p : Ω × Θ | (S p.1 ∩ U).Nonempty} =
          Prod.fst ⁻¹' {ω | (S ω ∩ U).Nonempty} := by
      ext p
      rfl
    rw [hEq]
    exact measurable_fst (hS U hU)
  exact exists_measurable_lifting hSlift
    (fun p => hcompact p.1) (fun p => hne p.1)
    hφmeas hφcont hv hfiberNe

/-- Parameterized lifting stated for a jointly measurable selection of the
parameter-dependent Carathéodory image.-/
theorem exists_measurable_lifting_param_of_mem_image
    {Ω Θ X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : (Ω × Θ) × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ p : Ω × Θ, Continuous fun x => φ (p, x))
    {v : Ω × Θ → Y} (hv : Measurable v)
    (hvmem : ∀ p : Ω × Θ,
      v p ∈ (fun x => φ (p, x)) '' S p.1) :
    ∃ T : Ω × Θ → X, Measurable T ∧
      ∀ p : Ω × Θ, T p ∈ S p.1 ∧ φ (p, T p) = v p := by
  apply exists_measurable_lifting_param hS hcompact hne hφmeas hφcont hv
  intro p
  rcases hvmem p with ⟨x, hxS, hxφ⟩
  exact ⟨x, hxS, hxφ⟩

/-- Almost-sure parameter-dependent lifting for an arbitrary measure on the
joint base `Ω × Θ`.  The selected latent point belongs to `S(ω)` everywhere
and realizes the prescribed parameter-dependent target almost surely.-/
theorem exists_measurable_lifting_param_of_ae_mem_image
    {Ω Θ X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {μ : Measure (Ω × Θ)}
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : (Ω × Θ) × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ p : Ω × Θ, Continuous fun x => φ (p, x))
    {v : Ω × Θ → Y} (hv : Measurable v)
    (hvmem : ∀ᵐ p ∂μ,
      v p ∈ (fun x => φ (p, x)) '' S p.1) :
    ∃ T : Ω × Θ → X, Measurable T ∧
      (∀ p : Ω × Θ, T p ∈ S p.1) ∧
        ∀ᵐ p ∂μ, φ (p, T p) = v p := by
  have hSlift : RandomSet.IsEffrosMeasurable
      (fun p : Ω × Θ => S p.1) := by
    intro U hU
    have hEq :
        {p : Ω × Θ | (S p.1 ∩ U).Nonempty} =
          Prod.fst ⁻¹' {ω | (S ω ∩ U).Nonempty} := by
      ext p
      rfl
    rw [hEq]
    exact measurable_fst (hS U hU)
  exact exists_measurable_lifting_of_ae_mem_image
    (μ := μ) hSlift (fun p => hcompact p.1) (fun p => hne p.1)
    hφmeas hφcont hv hvmem

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
