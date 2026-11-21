/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.CastaingRepresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurability of the graph

The Castaing representation turns membership in a random closed set into a
countable collection of metric inequalities.  This proves the classical
implication from Effros measurability to graph measurability in a Polish
range space.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory TopologicalSpace

noncomputable section

namespace RandomSetTheory

/-- In the Polish closed-valued setting, the distance to the moving fibre is
jointly measurable in the base point and the ambient point.-/
theorem measurable_infDist_correspondence_joint
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hclosed : ∀ ω, IsClosed (S ω)) (hne : ∀ ω, (S ω).Nonempty) :
    Measurable (fun p : Ω × E => infDist p.2 (S p.1)) := by
  let f : ℕ → Ω → E := castaingRepresentation hS hclosed hne
  have hf : ∀ n, Measurable (f n) :=
    castaingRepresentation_measurable hS hclosed hne
  have hclosure : ∀ ω, closure (Set.range fun n => f n ω) = S ω :=
    closure_range_castaingRepresentation hS hclosed hne
  have hEq : (fun p : Ω × E => infDist p.2 (S p.1)) =
      fun p => ⨅ n : ℕ, dist p.2 (f n p.1) := by
    funext p
    rw [← hclosure p.1, Metric.infDist_closure]
    rw [Metric.infDist_eq_iInf, iInf, iInf]
    apply congrArg sInf
    ext z
    simp only [Set.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨n, hn⟩ := y.property
      exact ⟨n, congrArg (dist p.2) hn⟩
    · rintro ⟨n, rfl⟩
      exact ⟨⟨f n p.1, ⟨n, rfl⟩⟩, rfl⟩
  rw [hEq]
  exact Measurable.iInf fun n =>
    measurable_snd.dist ((hf n).comp measurable_fst)

/-- The graph of a nonempty closed-valued Effros-measurable correspondence
into a Polish space is measurable in the product sigma-algebra.-/
theorem measurableSet_correspondenceGraph
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hclosed : ∀ ω, IsClosed (S ω)) (hne : ∀ ω, (S ω).Nonempty) :
    MeasurableSet (correspondenceGraph S) := by
  let f : ℕ → Ω → E := castaingRepresentation hS hclosed hne
  have hf : ∀ n, Measurable (f n) :=
    castaingRepresentation_measurable hS hclosed hne
  have hclosure : ∀ ω, closure (Set.range fun n => f n ω) = S ω :=
    closure_range_castaingRepresentation hS hclosed hne
  have hEq : correspondenceGraph S =
      ⋂ m : ℕ, ⋃ n : ℕ,
        {p : Ω × E | dist p.2 (f n p.1) < 1 / ((m : ℝ) + 1)} := by
    ext p
    simp only [correspondenceGraph, Set.mem_ofPred_eq, Set.mem_iInter,
      Set.mem_iUnion]
    rw [← hclosure p.1, Metric.mem_closure_range_iff_nat]
  rw [hEq]
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iUnion
  intro n
  exact (measurable_snd.dist ((hf n).comp measurable_fst)) measurableSet_Iio

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
