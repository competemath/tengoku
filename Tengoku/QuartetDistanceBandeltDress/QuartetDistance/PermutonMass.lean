import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.Permuton
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.TiedSampleCount

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact mass of the step-permuton event

This module exposes the completed bridge between the analytic four-point
event for the step permuton and the literal finite tied-sample density.  The
rank-chamber, atomic-strip, exact `ℝ≥0∞` mass, and real normalization
calculations are proved in `Permuton.lean`; here they are related to both
finite density presentations and used to specialize the one published
permuton inequality.
-/

namespace QuartetDistance.Permuton

open MeasureTheory

/-- Equivalent formulation using the single global tied-sample space used by
the finite collision reduction.
@isnad1 id=eq.1h2v.s4.388103f4797b from=translated src=- shape=38091827 vocab=8e496ad7
-/
theorem dihedralDensity_stepPermuton_eq_globalTiedDihedralDensity {n : ℕ}
    (hn : 0 < n) (π : Equiv.Perm (Fin n)) :
    dihedralDensity (stepPermuton hn π) =
      (Circular.globalTiedDihedralDensity π : ℝ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact dihedralDensity_stepPermuton hn π

/-- The published real-valued permuton inequality supplies exactly the
rational finite step-permuton hypothesis used by the counting proof.
@isnad1 id=stepperm.2h1v.s4.22fe6ed18bc9 from=translated src=- shape=9edaa0d7 vocab=6cfe1ce0
-/
theorem publishedPermutonInequality_implies_stepPermutonTheorem {n : ℕ}
    (hn : 4 ≤ n) (hpublished : PublishedPermutonInequality) :
    Circular.StepPermutonTheorem n := by
  intro π
  have hn0 : 0 < n := by omega
  have h := hpublished (stepPermuton hn0 π)
  rw [dihedralDensity_stepPermuton_eq_globalTiedDihedralDensity hn0 π] at h
  change (1 : ℚ) / 3 ≤ Circular.globalTiedDihedralDensity π
  rw [← Rat.cast_le (K := ℝ)]
  norm_num
  exact h

end QuartetDistance.Permuton
