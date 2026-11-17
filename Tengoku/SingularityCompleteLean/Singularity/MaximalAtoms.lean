import Tengoku.Seed.MeasureTheory.Measure.Typeclasses.Finite
import Tengoku.Seed.MeasureTheory.Measure.Basic
import Tengoku.Seed.MeasureTheory.Measure.Real
import Tengoku.Seed.Topology.Algebra.InfiniteSum.ENNReal
import Tengoku.Seed.Data.Set.Finite.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Maximal atoms of a finite measure

The masses of measurable singletons have bounded total sum. Consequently only
finitely many can exceed a positive threshold, and any nonzero atom yields a
largest atom. These facts do not assume the underlying space is countable.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal

namespace Singularity

/-- A finite measure has finitely many singleton masses above every positive threshold.
@isnad1 id=finite.1h3v.s5.a9e7bd871d7c from=translated src=- shape=c3deef80 vocab=01fec4b6
-/
theorem finite_large_atoms {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsFiniteMeasure ν] {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    {x : X | ε ≤ ν {x}}.Finite := by
  have hs : ∑' x : X, ν {x} ≤ ν univ :=
    tsum_measure_le_measure_univ (fun x => (measurableSet_singleton x).nullMeasurableSet)
      (fun x y hxy => (Set.disjoint_singleton.mpr hxy).aedisjoint)
  exact ENNReal.finite_const_le_of_tsum_ne_top (ne_top_of_le_ne_top (measure_ne_top ν univ) hs) hε

/-- If a finite measure has a nonzero singleton, its largest singleton mass is attained.
@isnad1 id=ex.1h2v.s7.26c2be373d29 from=translated src=- shape=0d09977f vocab=aa93f83c
-/
theorem exists_maximal_atom {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsFiniteMeasure ν] (h : ∃ x : X, ν {x} ≠ 0) :
    ∃ x : X, 0 < ν {x} ∧ ∀ y : X, ν {y} ≤ ν {x} := by
  obtain ⟨x₀, hx₀⟩ := h
  let S := {x : X | ν {x₀} ≤ ν {x}}
  have hS : S.Finite := finite_large_atoms ν hx₀
  obtain ⟨x, hx, hmax⟩ := Set.exists_max_image S (fun y => ν {y}) hS ⟨x₀, show ν {x₀} ≤ ν {x₀} from le_rfl⟩
  refine ⟨x, lt_of_lt_of_le (pos_iff_ne_zero.mpr hx₀) hx, fun y => ?_⟩
  by_cases hy : y ∈ S
  · exact hmax y hy
  · exact (le_of_not_ge hy).trans hx

/-- The real singleton-mass function also attains a positive maximum when an atom is present.
@isnad1 id=ex.1h2v.s7.1f726301c4a8 from=translated src=- shape=b6e7f175 vocab=d4853953
-/
theorem exists_maximal_real_atom {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsFiniteMeasure ν] (h : ∃ x : X, ν {x} ≠ 0) :
    ∃ x : X, 0 < (ν {x}).toReal ∧ ∀ y : X, (ν {y}).toReal ≤ (ν {x}).toReal := by
  obtain ⟨x, hx, hmax⟩ := exists_maximal_atom ν h
  exact ⟨x, ENNReal.toReal_pos hx.ne' (measure_ne_top ν _),
    fun y => (ENNReal.toReal_le_toReal (measure_ne_top ν _) (measure_ne_top ν _)).mpr (hmax y)⟩

/-- The positive maximizers of the real singleton-mass function form a finite set.
@isnad1 id=finite.1h3v.s6.af003e16b0e0 from=translated src=- shape=cea29ec2 vocab=769a2005
-/
theorem finite_maximal_real_atoms {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsFiniteMeasure ν] (x : X) (hx : 0 < (ν {x}).toReal) :
    {y : X | (ν {y}).toReal = (ν {x}).toReal}.Finite := by
  apply (finite_large_atoms ν (ENNReal.toReal_pos_iff.mp hx).1.ne').subset
  intro y hy
  exact le_of_eq ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν _) (measure_ne_top ν _)).mp hy).symm

end Singularity
