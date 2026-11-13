import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Simultaneous avoidance of finitely many smooth low-dimensional ranges

The high-codimension orbit-unknotting argument chooses perturbation parameters
away from several bad loci (the two secant charts and the tangent chart).  Each
bad locus is contained in the range of a `C¹` map whose source has smaller
finite dimension than the parameter space.

Mathlib already proves that one such range has Hausdorff dimension at most the
dimension of its source.  This file records the finite-family form needed by
the general-position construction: a single parameter can avoid all bad
ranges simultaneously.  No transversality axiom or measure-theoretic choice is
introduced.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology ContDiff

namespace Submission

variable {D P ι : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- A finite union of ranges of `C¹` maps from a strictly lower-dimensional
space has dense complement.

This is the simultaneous-parameter version of
`ContDiff.dense_compl_range_of_finrank_lt_finrank`.-/
theorem dense_compl_iUnion_range_of_contDiff
    [Fintype ι] [Countable ι]
    (f : ι → D → P) (hf : ∀ i, ContDiff ℝ 1 (f i))
    (hDP : Module.finrank ℝ D < Module.finrank ℝ P) :
    Dense (⋃ i, Set.range (f i))ᶜ := by
  apply dense_compl_of_dimH_lt_finrank
  rw [dimH_iUnion]
  apply iSup_lt_iff.mpr
  refine ⟨Module.finrank ℝ D, Nat.cast_lt.2 hDP, ?_⟩
  intro i
  exact (hf i).dimH_range_le

/-- Binary specialization, convenient when a bad secant locus is covered by
the two coordinate charts in which respectively the first or second circle
difference coordinate is nonzero.-/
theorem dense_compl_union_range_of_contDiff
    (f g : D → P) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hDP : Module.finrank ℝ D < Module.finrank ℝ P) :
    Dense (Set.range f ∪ Set.range g)ᶜ := by
  let F : Fin 2 → D → P := fun i => if i = 0 then f else g
  have hF : ∀ i, ContDiff ℝ 1 (F i) := by
    intro i
    fin_cases i
    · simpa [F] using hf
    · simpa [F] using hg
  have hdense := dense_compl_iUnion_range_of_contDiff F hF hDP
  convert hdense using 1
  ext x
  simp [F]

/-- Inside every nonempty open set there is a parameter avoiding all ranges
in a finite smooth lower-dimensional family.-/
theorem exists_mem_open_avoid_iUnion_range
    [Fintype ι] [Countable ι]
    (f : ι → D → P) (hf : ∀ i, ContDiff ℝ 1 (f i))
    (hDP : Module.finrank ℝ D < Module.finrank ℝ P)
    {U : Set P} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ∃ p ∈ U, ∀ i, p ∉ Set.range (f i) := by
  obtain ⟨p, hpbad, hpU⟩ :=
    (dense_compl_iUnion_range_of_contDiff f hf hDP).exists_mem_open hUopen hUne
  refine ⟨p, hpU, ?_⟩
  intro i hpi
  exact hpbad (Set.mem_iUnion.mpr ⟨i, hpi⟩)

end Submission
