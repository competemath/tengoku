/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableLifting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The measurable Berge--Aumann maximum theorem

Let `S(ω)` be a nonempty compact-valued Effros-measurable correspondence and
let `f(ω, x)` be jointly measurable and continuous in `x`.  This file proves
the measurable maximum theorem in its correspondence-valued form:

* the fibrewise maximum value is measurable;
* the argmax correspondence is nonempty, compact and Effros measurable;
* an exact measurable maximizer exists.

The maximum-value proof regards the maximum as the support function in
direction `1` of the scalar Carathéodory image `f(ω, ·) '' S(ω)`.  Once that
value is known to be measurable, the argmax is an exact Carathéodory lifting
fibre, so the measurable-lifting theorem and KRN apply without any projection
or additional axiom.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set MeasureTheory TopologicalSpace
open scoped InnerProductSpace

noncomputable section

namespace RandomSetTheory

/-- The maximum value of `f(ω, ·)` on the feasible fibre `S(ω)`.-/
def bergeMaxValue
    {Ω X : Type*} (S : Ω → Set X) (f : Ω × X → ℝ) (ω : Ω) : ℝ :=
  sSup ((fun x => f (ω, x)) '' S ω)

/-- The points of `S(ω)` at which the fibrewise maximum is attained.-/
def bergeArgmax
    {Ω X : Type*} (S : Ω → Set X) (f : Ω × X → ℝ) (ω : Ω) : Set X :=
  S ω ∩ {x | f (ω, x) = bergeMaxValue S f ω}

@[simp]
theorem mem_bergeArgmax
    {Ω X : Type*} {S : Ω → Set X} {f : Ω × X → ℝ} {ω : Ω} {x : X} :
    x ∈ bergeArgmax S f ω ↔
      x ∈ S ω ∧ f (ω, x) = bergeMaxValue S f ω :=
  Iff.rfl

theorem bergeArgmax_subset
    {Ω X : Type*} (S : Ω → Set X) (f : Ω × X → ℝ) (ω : Ω) :
    bergeArgmax S f ω ⊆ S ω :=
  inter_subset_left

/-- On a nonempty compact fibre, the Berge maximum is attained.-/
theorem bergeArgmax_nonempty
    {Ω X : Type*} [TopologicalSpace X]
    {S : Ω → Set X} (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty) {f : Ω × X → ℝ}
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) (ω : Ω) :
    (bergeArgmax S f ω).Nonempty := by
  obtain ⟨x, hxS, hmax, _⟩ :=
    (hcompact ω).exists_sSup_image_eq_and_ge (hne ω)
      (hfcont ω).continuousOn
  exact ⟨x, hxS, hmax.symm⟩

/-- The Berge argmax of a continuous criterion over a compact fibre is
compact (emptiness of the fibre is not needed for this statement).-/
theorem bergeArgmax_isCompact
    {Ω X : Type*} [TopologicalSpace X]
    {S : Ω → Set X} (hcompact : ∀ ω, IsCompact (S ω))
    {f : Ω × X → ℝ} (hfcont : ∀ ω, Continuous fun x => f (ω, x))
    (ω : Ω) : IsCompact (bergeArgmax S f ω) := by
  exact (hcompact ω).inter_right
    (isClosed_eq (hfcont ω) continuous_const)

/-- A scalar maximum is the support function, in direction `1`, of the
scalar image of the feasible set.-/
theorem bergeMaxValue_eq_supportFunction_image
    {Ω X : Type*} (S : Ω → Set X) (f : Ω × X → ℝ) (ω : Ω) :
    bergeMaxValue S f ω =
      supportFunction ((fun x => f (ω, x)) '' S ω) (1 : ℝ) := by
  simp [bergeMaxValue, supportFunction]

/-- **Measurable Berge maximum theorem (value form).**-/
theorem measurable_bergeMaxValue
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : Ω × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) :
    Measurable (bergeMaxValue S f) := by
  let T : Ω → Set ℝ := fun ω => (fun x => f (ω, x)) '' S ω
  have hT : RandomSet.IsEffrosMeasurable T :=
    effrosMeasurable_caratheodoryImage hS
      (fun ω => (hcompact ω).isClosed) hne hfmeas hfcont
  have hTcompact : ∀ ω, IsCompact (T ω) :=
    fun ω => (hcompact ω).image (hfcont ω)
  have hTne : ∀ ω, (T ω).Nonempty :=
    fun ω => (hne ω).image (fun x => f (ω, x))
  have hsupport : Measurable (fun ω => supportFunction (T ω) (1 : ℝ)) :=
    measurable_supportFunction hT hTcompact hTne 1
  have heq : bergeMaxValue S f =
      fun ω => supportFunction (T ω) (1 : ℝ) := by
    funext ω
    exact bergeMaxValue_eq_supportFunction_image S f ω
  rw [heq]
  exact hsupport

/-- The Berge argmax is definitionally the exact lifting fibre of the
measurable maximum value.-/
theorem bergeArgmax_eq_measurableLiftingFiber
    {Ω X : Type*} (S : Ω → Set X) (f : Ω × X → ℝ) :
    bergeArgmax S f = measurableLiftingFiber S f (bergeMaxValue S f) :=
  rfl

/-- **Measurable Berge maximum theorem (correspondence form).**  The argmax
correspondence is Effros measurable.-/
theorem effrosMeasurable_bergeArgmax
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : Ω × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) :
    RandomSet.IsEffrosMeasurable (bergeArgmax S f) := by
  rw [bergeArgmax_eq_measurableLiftingFiber]
  exact effrosMeasurable_measurableLiftingFiber hS hcompact hne
    hfmeas hfcont (measurable_bergeMaxValue hS hcompact hne hfmeas hfcont)

/-- Canonical exact measurable maximizer supplied by KRN.-/
def bergeMaximizingSelection
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : Ω × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) : Ω → X :=
  measurableLiftingSelection hS hcompact hne hfmeas hfcont
    (measurable_bergeMaxValue hS hcompact hne hfmeas hfcont)
    (bergeArgmax_nonempty hcompact hne hfcont)

/-- The canonical Berge maximizer is measurable.-/
theorem measurable_bergeMaximizingSelection
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : Ω × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) :
    Measurable
      (bergeMaximizingSelection hS hcompact hne hfmeas hfcont) :=
  measurable_measurableLiftingSelection hS hcompact hne hfmeas hfcont
    (measurable_bergeMaxValue hS hcompact hne hfmeas hfcont)
    (bergeArgmax_nonempty hcompact hne hfcont)

/-- The canonical selection is feasible and maximizes the criterion exactly
in every fibre.-/
theorem bergeMaximizingSelection_mem_and_eq
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : Ω × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) (ω : Ω) :
    bergeMaximizingSelection hS hcompact hne hfmeas hfcont ω ∈ S ω ∧
      f (ω, bergeMaximizingSelection hS hcompact hne hfmeas hfcont ω) =
        bergeMaxValue S f ω :=
  measurableLiftingSelection_mem_and_map_eq hS hcompact hne
    hfmeas hfcont
    (measurable_bergeMaxValue hS hcompact hne hfmeas hfcont)
    (bergeArgmax_nonempty hcompact hne hfcont) ω

/-- Existential form of the exact measurable Berge--Aumann maximum theorem.-/
theorem exists_measurable_bergeMaximizer
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : Ω × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) :
    ∃ s : Ω → X, Measurable s ∧
      ∀ ω, s ω ∈ S ω ∧ f (ω, s ω) = bergeMaxValue S f ω := by
  exact ⟨bergeMaximizingSelection hS hcompact hne hfmeas hfcont,
    measurable_bergeMaximizingSelection hS hcompact hne hfmeas hfcont,
    bergeMaximizingSelection_mem_and_eq hS hcompact hne hfmeas hfcont⟩

/-! ## Measurable minima -/

/-- The minimum value of `f(ω, ·)` on the feasible fibre `S(ω)`.-/
def bergeMinValue
    {Ω X : Type*} (S : Ω → Set X) (f : Ω × X → ℝ) (ω : Ω) : ℝ :=
  sInf ((fun x => f (ω, x)) '' S ω)

/-- The points of `S(ω)` at which the fibrewise minimum is attained.-/
def bergeArgmin
    {Ω X : Type*} (S : Ω → Set X) (f : Ω × X → ℝ) (ω : Ω) : Set X :=
  S ω ∩ {x | f (ω, x) = bergeMinValue S f ω}

@[simp]
theorem mem_bergeArgmin
    {Ω X : Type*} {S : Ω → Set X} {f : Ω × X → ℝ} {ω : Ω} {x : X} :
    x ∈ bergeArgmin S f ω ↔
      x ∈ S ω ∧ f (ω, x) = bergeMinValue S f ω :=
  Iff.rfl

theorem bergeArgmin_subset
    {Ω X : Type*} (S : Ω → Set X) (f : Ω × X → ℝ) (ω : Ω) :
    bergeArgmin S f ω ⊆ S ω :=
  inter_subset_left

/-- On a nonempty compact fibre, the Berge minimum is attained.-/
theorem bergeArgmin_nonempty
    {Ω X : Type*} [TopologicalSpace X]
    {S : Ω → Set X} (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty) {f : Ω × X → ℝ}
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) (ω : Ω) :
    (bergeArgmin S f ω).Nonempty := by
  obtain ⟨x, hxS, hmin, _⟩ :=
    (hcompact ω).exists_sInf_image_eq_and_le (hne ω)
      (hfcont ω).continuousOn
  exact ⟨x, hxS, hmin.symm⟩

/-- The Berge argmin of a continuous criterion over a compact fibre is
compact.-/
theorem bergeArgmin_isCompact
    {Ω X : Type*} [TopologicalSpace X]
    {S : Ω → Set X} (hcompact : ∀ ω, IsCompact (S ω))
    {f : Ω × X → ℝ} (hfcont : ∀ ω, Continuous fun x => f (ω, x))
    (ω : Ω) : IsCompact (bergeArgmin S f ω) := by
  exact (hcompact ω).inter_right
    (isClosed_eq (hfcont ω) continuous_const)

/-- A scalar minimum is the negative support function, in direction `-1`,
of the scalar image of the feasible set.-/
theorem bergeMinValue_eq_neg_supportFunction_image
    {Ω X : Type*} (S : Ω → Set X) (f : Ω × X → ℝ) (ω : Ω) :
    bergeMinValue S f ω =
      -supportFunction ((fun x => f (ω, x)) '' S ω) (-1 : ℝ) := by
  simp [bergeMinValue, supportFunction]

/-- **Measurable Berge minimum theorem (value form).**-/
theorem measurable_bergeMinValue
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : Ω × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) :
    Measurable (bergeMinValue S f) := by
  let T : Ω → Set ℝ := fun ω => (fun x => f (ω, x)) '' S ω
  have hT : RandomSet.IsEffrosMeasurable T :=
    effrosMeasurable_caratheodoryImage hS
      (fun ω => (hcompact ω).isClosed) hne hfmeas hfcont
  have hTcompact : ∀ ω, IsCompact (T ω) :=
    fun ω => (hcompact ω).image (hfcont ω)
  have hTne : ∀ ω, (T ω).Nonempty :=
    fun ω => (hne ω).image (fun x => f (ω, x))
  have hsupport : Measurable
      (fun ω => supportFunction (T ω) (-1 : ℝ)) :=
    measurable_supportFunction hT hTcompact hTne (-1)
  have heq : bergeMinValue S f =
      fun ω => -supportFunction (T ω) (-1 : ℝ) := by
    funext ω
    exact bergeMinValue_eq_neg_supportFunction_image S f ω
  rw [heq]
  exact hsupport.neg

/-- The Berge argmin is definitionally the exact lifting fibre of the
measurable minimum value.-/
theorem bergeArgmin_eq_measurableLiftingFiber
    {Ω X : Type*} (S : Ω → Set X) (f : Ω × X → ℝ) :
    bergeArgmin S f = measurableLiftingFiber S f (bergeMinValue S f) :=
  rfl

/-- **Measurable Berge minimum theorem (correspondence form).**  The argmin
correspondence is Effros measurable.-/
theorem effrosMeasurable_bergeArgmin
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : Ω × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) :
    RandomSet.IsEffrosMeasurable (bergeArgmin S f) := by
  rw [bergeArgmin_eq_measurableLiftingFiber]
  exact effrosMeasurable_measurableLiftingFiber hS hcompact hne
    hfmeas hfcont (measurable_bergeMinValue hS hcompact hne hfmeas hfcont)

/-- Canonical exact measurable minimizer supplied by KRN.-/
def bergeMinimizingSelection
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : Ω × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) : Ω → X :=
  measurableLiftingSelection hS hcompact hne hfmeas hfcont
    (measurable_bergeMinValue hS hcompact hne hfmeas hfcont)
    (bergeArgmin_nonempty hcompact hne hfcont)

/-- The canonical Berge minimizer is measurable.-/
theorem measurable_bergeMinimizingSelection
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : Ω × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) :
    Measurable
      (bergeMinimizingSelection hS hcompact hne hfmeas hfcont) :=
  measurable_measurableLiftingSelection hS hcompact hne hfmeas hfcont
    (measurable_bergeMinValue hS hcompact hne hfmeas hfcont)
    (bergeArgmin_nonempty hcompact hne hfcont)

/-- The canonical selection is feasible and minimizes the criterion exactly
in every fibre.-/
theorem bergeMinimizingSelection_mem_and_eq
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : Ω × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) (ω : Ω) :
    bergeMinimizingSelection hS hcompact hne hfmeas hfcont ω ∈ S ω ∧
      f (ω, bergeMinimizingSelection hS hcompact hne hfmeas hfcont ω) =
        bergeMinValue S f ω :=
  measurableLiftingSelection_mem_and_map_eq hS hcompact hne
    hfmeas hfcont
    (measurable_bergeMinValue hS hcompact hne hfmeas hfcont)
    (bergeArgmin_nonempty hcompact hne hfcont) ω

/-- Existential form of the exact measurable Berge--Aumann minimum theorem.-/
theorem exists_measurable_bergeMinimizer
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : Ω × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) :
    ∃ s : Ω → X, Measurable s ∧
      ∀ ω, s ω ∈ S ω ∧ f (ω, s ω) = bergeMinValue S f ω := by
  exact ⟨bergeMinimizingSelection hS hcompact hne hfmeas hfcont,
    measurable_bergeMinimizingSelection hS hcompact hne hfmeas hfcont,
    bergeMinimizingSelection_mem_and_eq hS hcompact hne hfmeas hfcont⟩

/-! ## Measurable metric projections -/

/-- The distance criterion whose minimizers are nearest points to `y(ω)`.-/
def metricProjectionCriterion
    {Ω X : Type*} [PseudoMetricSpace X] (y : Ω → X) (p : Ω × X) : ℝ :=
  dist (y p.1) p.2

/-- The correspondence of all nearest points to `y(ω)` in `S(ω)`.-/
def metricProjectionSet
    {Ω X : Type*} [PseudoMetricSpace X]
    (S : Ω → Set X) (y : Ω → X) (ω : Ω) : Set X :=
  S ω ∩ {x | dist (y ω) x = Metric.infDist (y ω) (S ω)}

@[simp]
theorem mem_metricProjectionSet
    {Ω X : Type*} [PseudoMetricSpace X]
    {S : Ω → Set X} {y : Ω → X} {ω : Ω} {x : X} :
    x ∈ metricProjectionSet S y ω ↔
      x ∈ S ω ∧ dist (y ω) x = Metric.infDist (y ω) (S ω) :=
  Iff.rfl

/-- The minimum of the distance criterion is the point-to-set distance.-/
theorem bergeMinValue_metricProjectionCriterion
    {Ω X : Type*} [PseudoMetricSpace X]
    (S : Ω → Set X) (y : Ω → X) (ω : Ω) :
    bergeMinValue S (metricProjectionCriterion y) ω =
      Metric.infDist (y ω) (S ω) := by
  rw [bergeMinValue, Metric.infDist_eq_iInf, sInf_image']
  rfl

/-- The nearest-point correspondence is exactly the Berge argmin of the
distance criterion.-/
theorem metricProjectionSet_eq_bergeArgmin
    {Ω X : Type*} [PseudoMetricSpace X]
    (S : Ω → Set X) (y : Ω → X) :
    metricProjectionSet S y =
      bergeArgmin S (metricProjectionCriterion y) := by
  funext ω
  ext x
  simp only [mem_metricProjectionSet, mem_bergeArgmin]
  rw [bergeMinValue_metricProjectionCriterion]
  rfl

/-- Joint measurability of the distance-to-target criterion.-/
theorem measurable_metricProjectionCriterion
    {Ω X : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    {y : Ω → X} (hy : Measurable y) :
    Measurable (metricProjectionCriterion y) :=
  (hy.comp measurable_fst).dist measurable_snd

/-- Fibrewise continuity of the distance-to-target criterion.-/
theorem continuous_metricProjectionCriterion
    {Ω X : Type*} [PseudoMetricSpace X] (y : Ω → X) (ω : Ω) :
    Continuous fun x => metricProjectionCriterion y (ω, x) :=
  by
    simpa [metricProjectionCriterion] using
      (continuous_const.dist continuous_id :
        Continuous fun x : X => dist (y ω) x)

/-- The nearest-point correspondence of a measurable target and a random
compact set is Effros measurable.-/
theorem effrosMeasurable_metricProjectionSet
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {y : Ω → X} (hy : Measurable y) :
    RandomSet.IsEffrosMeasurable (metricProjectionSet S y) := by
  rw [metricProjectionSet_eq_bergeArgmin]
  exact effrosMeasurable_bergeArgmin hS hcompact hne
    (measurable_metricProjectionCriterion hy)
    (continuous_metricProjectionCriterion y)

/-- The nearest-point correspondence has nonempty compact values.-/
theorem metricProjectionSet_nonempty_and_isCompact
    {Ω X : Type*} [MetricSpace X]
    {S : Ω → Set X} (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty) (y : Ω → X) (ω : Ω) :
    (metricProjectionSet S y ω).Nonempty ∧
      IsCompact (metricProjectionSet S y ω) := by
  rw [metricProjectionSet_eq_bergeArgmin]
  exact ⟨bergeArgmin_nonempty hcompact hne
      (continuous_metricProjectionCriterion y) ω,
    bergeArgmin_isCompact hcompact
      (continuous_metricProjectionCriterion y) ω⟩

/-- A canonical measurable choice of a nearest point to `y(ω)` in `S(ω)`.-/
def measurableMetricProjection
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {y : Ω → X} (hy : Measurable y) : Ω → X :=
  bergeMinimizingSelection hS hcompact hne
    (measurable_metricProjectionCriterion hy)
    (continuous_metricProjectionCriterion y)

/-- The canonical metric projection is measurable.-/
theorem measurable_measurableMetricProjection
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {y : Ω → X} (hy : Measurable y) :
    Measurable (measurableMetricProjection hS hcompact hne hy) :=
  measurable_bergeMinimizingSelection hS hcompact hne
    (measurable_metricProjectionCriterion hy)
    (continuous_metricProjectionCriterion y)

/-- The canonical metric projection belongs to `S(ω)` and realizes the
point-to-set distance exactly.-/
theorem measurableMetricProjection_mem_and_dist_eq
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {y : Ω → X} (hy : Measurable y) (ω : Ω) :
    measurableMetricProjection hS hcompact hne hy ω ∈ S ω ∧
      dist (y ω) (measurableMetricProjection hS hcompact hne hy ω) =
        Metric.infDist (y ω) (S ω) := by
  have h := bergeMinimizingSelection_mem_and_eq hS hcompact hne
    (measurable_metricProjectionCriterion hy)
    (continuous_metricProjectionCriterion y) ω
  refine ⟨h.1, ?_⟩
  exact h.2.trans (bergeMinValue_metricProjectionCriterion S y ω)

/-- Existential measurable nearest-point theorem.-/
theorem exists_measurable_metricProjection
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {y : Ω → X} (hy : Measurable y) :
    ∃ p : Ω → X, Measurable p ∧
      ∀ ω, p ω ∈ S ω ∧
        dist (y ω) (p ω) = Metric.infDist (y ω) (S ω) := by
  exact ⟨measurableMetricProjection hS hcompact hne hy,
    measurable_measurableMetricProjection hS hcompact hne hy,
    measurableMetricProjection_mem_and_dist_eq hS hcompact hne hy⟩

/-! ## Parameter-dependent measurable maxima -/

/-- Pulling an Effros correspondence back along the first projection
preserves Effros measurability.-/
private theorem effrosMeasurable_fst_pullback
    {Ω Θ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [TopologicalSpace X] {S : Ω → Set X}
    (hS : RandomSet.IsEffrosMeasurable S) :
    RandomSet.IsEffrosMeasurable (fun p : Ω × Θ => S p.1) := by
  intro U hU
  have hEq :
      {p : Ω × Θ | (S p.1 ∩ U).Nonempty} =
        Prod.fst ⁻¹' {ω | (S ω ∩ U).Nonempty} := by
    ext p
    rfl
  rw [hEq]
  exact measurable_fst (hS U hU)

/-- Joint measurability in `(ω, θ)` of a parameter-dependent maximum over
the fixed feasible fibre `S(ω)`.-/
theorem measurable_bergeMaxValue_param
    {Ω Θ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : (Ω × Θ) × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ p : Ω × Θ, Continuous fun x => f (p, x)) :
    Measurable (bergeMaxValue (fun p : Ω × Θ => S p.1) f) :=
  measurable_bergeMaxValue (effrosMeasurable_fst_pullback hS)
    (fun p => hcompact p.1) (fun p => hne p.1) hfmeas hfcont

/-- The parameter-dependent argmax correspondence is jointly Effros
measurable in `(ω, θ)`.-/
theorem effrosMeasurable_bergeArgmax_param
    {Ω Θ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : (Ω × Θ) × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ p : Ω × Θ, Continuous fun x => f (p, x)) :
    RandomSet.IsEffrosMeasurable
      (bergeArgmax (fun p : Ω × Θ => S p.1) f) :=
  effrosMeasurable_bergeArgmax (effrosMeasurable_fst_pullback hS)
    (fun p => hcompact p.1) (fun p => hne p.1) hfmeas hfcont

/-- The parameter-dependent argmax has nonempty compact values.-/
theorem bergeArgmax_param_nonempty_and_isCompact
    {Ω Θ X : Type*} [TopologicalSpace X]
    {S : Ω → Set X} (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty) {f : (Ω × Θ) × X → ℝ}
    (hfcont : ∀ p : Ω × Θ, Continuous fun x => f (p, x))
    (p : Ω × Θ) :
    (bergeArgmax (fun q : Ω × Θ => S q.1) f p).Nonempty ∧
      IsCompact (bergeArgmax (fun q : Ω × Θ => S q.1) f p) :=
  ⟨bergeArgmax_nonempty (fun q : Ω × Θ => hcompact q.1)
      (fun q : Ω × Θ => hne q.1) hfcont p,
    bergeArgmax_isCompact (fun q : Ω × Θ => hcompact q.1) hfcont p⟩

/-- Parameterized exact Berge--Aumann selection theorem.  A maximizer can be
chosen jointly measurably in the outcome and the external parameter.-/
theorem exists_measurable_bergeMaximizer_param
    {Ω Θ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : (Ω × Θ) × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ p : Ω × Θ, Continuous fun x => f (p, x)) :
    ∃ s : Ω × Θ → X, Measurable s ∧
      ∀ p : Ω × Θ,
        s p ∈ S p.1 ∧
          f (p, s p) =
            bergeMaxValue (fun q : Ω × Θ => S q.1) f p := by
  exact exists_measurable_bergeMaximizer
    (effrosMeasurable_fst_pullback hS)
    (fun p => hcompact p.1) (fun p => hne p.1) hfmeas hfcont

/-! ## Parameter-dependent measurable minima -/

/-- Joint measurability in `(ω, θ)` of a parameter-dependent minimum over
the fixed feasible fibre `S(ω)`.-/
theorem measurable_bergeMinValue_param
    {Ω Θ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : (Ω × Θ) × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ p : Ω × Θ, Continuous fun x => f (p, x)) :
    Measurable (bergeMinValue (fun p : Ω × Θ => S p.1) f) :=
  measurable_bergeMinValue (effrosMeasurable_fst_pullback hS)
    (fun p => hcompact p.1) (fun p => hne p.1) hfmeas hfcont

/-- The parameter-dependent argmin correspondence is jointly Effros
measurable in `(ω, θ)`.-/
theorem effrosMeasurable_bergeArgmin_param
    {Ω Θ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : (Ω × Θ) × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ p : Ω × Θ, Continuous fun x => f (p, x)) :
    RandomSet.IsEffrosMeasurable
      (bergeArgmin (fun p : Ω × Θ => S p.1) f) :=
  effrosMeasurable_bergeArgmin (effrosMeasurable_fst_pullback hS)
    (fun p => hcompact p.1) (fun p => hne p.1) hfmeas hfcont

/-- The parameter-dependent argmin has nonempty compact values.-/
theorem bergeArgmin_param_nonempty_and_isCompact
    {Ω Θ X : Type*} [TopologicalSpace X]
    {S : Ω → Set X} (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty) {f : (Ω × Θ) × X → ℝ}
    (hfcont : ∀ p : Ω × Θ, Continuous fun x => f (p, x))
    (p : Ω × Θ) :
    (bergeArgmin (fun q : Ω × Θ => S q.1) f p).Nonempty ∧
      IsCompact (bergeArgmin (fun q : Ω × Θ => S q.1) f p) :=
  ⟨bergeArgmin_nonempty (fun q : Ω × Θ => hcompact q.1)
      (fun q : Ω × Θ => hne q.1) hfcont p,
    bergeArgmin_isCompact (fun q : Ω × Θ => hcompact q.1) hfcont p⟩

/-- Parameterized exact Berge--Aumann minimization theorem.  A minimizer can
be chosen jointly measurably in the outcome and the external parameter.-/
theorem exists_measurable_bergeMinimizer_param
    {Ω Θ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {f : (Ω × Θ) × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ p : Ω × Θ, Continuous fun x => f (p, x)) :
    ∃ s : Ω × Θ → X, Measurable s ∧
      ∀ p : Ω × Θ,
        s p ∈ S p.1 ∧
          f (p, s p) =
            bergeMinValue (fun q : Ω × Θ => S q.1) f p := by
  exact exists_measurable_bergeMinimizer
    (effrosMeasurable_fst_pullback hS)
    (fun p => hcompact p.1) (fun p => hne p.1) hfmeas hfcont

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
