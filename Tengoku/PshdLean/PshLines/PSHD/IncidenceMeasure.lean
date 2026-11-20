import Tengoku.Seed.MeasureTheory.Measure.Typeclasses.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The finite-measure step in incidence

The final measure-theoretic argument of `pshd-vibe`, Lemma 1.5.
-/

open MeasureTheory Set
open scoped ENNReal

namespace PshLines.PSHD

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- A uniform lower bound on event masses persists on their set-theoretic limsup.-/
theorem le_measure_recurrent {s : ℕ → Set X} (hs : ∀ j, MeasurableSet (s j))
    {δ : ℝ≥0∞} (hδ : ∀ j, δ ≤ μ (s j)) :
    δ ≤ μ {x | ∀ m : ℕ, ∃ j, m ≤ j ∧ x ∈ s j} := by
  let t : ℕ → Set X := fun m ↦ ⋃ j ≥ m, s j
  have ht : Antitone t := by
    intro m n hmn x hx
    rcases mem_iUnion.mp hx with ⟨j, hj⟩
    rcases mem_iUnion.mp hj with ⟨hnj, hxj⟩
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hmn.trans hnj, hxj⟩⟩
  have htm : ∀ m, MeasurableSet (t m) := fun m ↦
    MeasurableSet.iUnion fun j ↦ MeasurableSet.iUnion fun _ ↦ hs j
  have heq : {x | ∀ m : ℕ, ∃ j, m ≤ j ∧ x ∈ s j} = ⋂ m, t m := by
    ext x
    simp [t]
  rw [heq, ht.measure_iInter (fun m ↦ (htm m).nullMeasurableSet)
    ⟨0, measure_ne_top μ _⟩]
  refine le_iInf fun m ↦ (hδ m).trans (measure_mono ?_)
  intro x hx
  exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨le_rfl, hx⟩⟩

/-- Positive uniformly bounded event masses force one point to recur infinitely often.-/
theorem exists_recurrent_of_measure_lower_bound {s : ℕ → Set X}
    (hs : ∀ j, MeasurableSet (s j)) {δ : ℝ≥0∞} (hδpos : 0 < δ)
    (hδ : ∀ j, δ ≤ μ (s j)) :
    ∃ x, ∀ m : ℕ, ∃ j, m ≤ j ∧ x ∈ s j := by
  have hpos := hδpos.trans_le (le_measure_recurrent μ hs hδ)
  exact MeasureTheory.nonempty_of_measure_ne_zero (ne_of_gt hpos)

end PshLines.PSHD
