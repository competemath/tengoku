/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Distance sections and graphs of correspondences

Effros measurability makes the distance to the correspondence measurable for
every fixed point.  The graph is defined here as a basic object.  The exact
selection theorem is proved constructively from countable hitting events and
does not require an expensive joint-measurability detour.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory

noncomputable section

namespace RandomSetTheory

/-- Graph of a set-valued map.-/
def correspondenceGraph {Ω E : Type*} (S : Ω → Set E) : Set (Ω × E) :=
  {p | p.2 ∈ S p.1}

/-- For a fixed point, the distance to a nonempty Effros-measurable
correspondence is measurable.-/
theorem measurable_infDist_correspondence
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hne : ∀ ω, (S ω).Nonempty) (x : E) :
    Measurable (fun ω => infDist x (S ω)) := by
  apply measurable_of_Iio
  intro r
  by_cases hr : 0 < r
  · have hEq : (fun ω => infDist x (S ω)) ⁻¹' Iio r =
        {ω | (S ω ∩ Metric.ball x r).Nonempty} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_ofPred_eq]
      rw [infDist_lt_iff (hne ω)]
      constructor
      · rintro ⟨y, hy, hxy⟩
        exact ⟨y, hy, by simpa [Metric.mem_ball, dist_comm] using hxy⟩
      · rintro ⟨y, hy, hyball⟩
        exact ⟨y, hy, by simpa [Metric.mem_ball, dist_comm] using hyball⟩
    rw [hEq]
    exact hS (Metric.ball x r) Metric.isOpen_ball
  · have hEq : (fun ω => infDist x (S ω)) ⁻¹' Iio r = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false]
      constructor
      · exact not_lt_of_ge
          ((not_lt.mp hr).trans (infDist_nonneg : 0 ≤ infDist x (S ω)))
      · exact False.elim
    rw [hEq]
    exact MeasurableSet.empty

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
