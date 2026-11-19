import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedDensity.CliqueMatchingNumerics
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A compact numerical interface for the sharp woven theorem in the
chromatic-inseparability stage construction. -/

namespace HadwigerLean.Inseparability

open HadwigerLean.RootedDensity

/--
@isnad1 id=le.3h3v.s7.5a89858f34d4 from=translated src=- shape=694c7b8c vocab=2dd59577
-/
theorem cliqueMatchingScale_stage_le_nine
    (t p x : ℕ)
    (hroot :
      (((2 * x : ℕ) : ℝ) *
        Real.sqrt (Real.log (((2 * x : ℕ) : ℝ)))) ≤
          4 * (t : ℝ))
    (hpx : p * x ≤ 2 * t)
    (hx : x ≤ t) :
    cliqueMatchingScale (2 * x) ((4 * p + 1) * x) ≤
      9 * (t : ℝ) := by
  unfold cliqueMatchingScale
  apply max_le
  · exact hroot.trans (by
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
      nlinarith)
  · have hpR : ((p * x : ℕ) : ℝ) ≤ 2 * (t : ℝ) := by
      exact_mod_cast hpx
    have hxR : (x : ℝ) ≤ t := by exact_mod_cast hx
    push_cast at hpR ⊢
    nlinarith

/--
@isnad1 id=le.4h4v.s7.73a7eebb90dc from=translated src=- shape=8018c019 vocab=2dd59577
-/
theorem sharp_woven_stage_budget
    (t p x C : ℕ)
    (hroot :
      (((2 * x : ℕ) : ℝ) *
        Real.sqrt (Real.log (((2 * x : ℕ) : ℝ)))) ≤
          4 * (t : ℝ))
    (hpx : p * x ≤ 2 * t)
    (hx : x ≤ t)
    (hC : 9000000 ≤ C) :
    1000000 * cliqueMatchingScale (2 * x) ((4 * p + 1) * x) ≤
      ((C * t : ℕ) : ℝ) := by
  have hscale := cliqueMatchingScale_stage_le_nine t p x hroot hpx hx
  have hC' : (9000000 : ℝ) ≤ C := by exact_mod_cast hC
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  push_cast
  nlinarith

end HadwigerLean.Inseparability
