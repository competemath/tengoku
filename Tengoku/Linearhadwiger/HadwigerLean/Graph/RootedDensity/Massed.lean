import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedDensity.Definitions
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.Massed
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The density and connectivity entry point to Appendix F's massed-pair invariant. -/

namespace HadwigerLean.RootedDensity

universe u
variable {V : Type u} [Fintype V]

/-- The real root-edge reserve follows from a linear density coefficient
once there are at least two roots.
@isnad1 id=lt.2h2v.s5.c9aaef55a26b from=translated src=- shape=5cb0c1d3 vocab=17dff172
-/
theorem root_edge_reserve
    (h : ℕ) (hh : 2 ≤ h) (α : ℝ) (hα : (h : ℝ) ≤ α) :
    ((h + 1).choose 2 : ℝ) < α * (h : ℝ) := by
  have hchoose : (h + 1).choose 2 < h * h := by
    rw [Nat.choose_two_right]
    have hsub : h + 1 - 1 = h := by omega
    rw [hsub]
    have hdiv : 2 * (((h + 1) * h) / 2) ≤ (h + 1) * h := by omega
    have hmul : (h + 1) * h < 2 * (h * h) := by nlinarith
    omega
  have hchooseR : ((h + 1).choose 2 : ℝ) < (h : ℝ) * (h : ℝ) := by
    exact_mod_cast hchoose
  have hnonneg : (0 : ℝ) ≤ h := by positivity
  nlinarith

end HadwigerLean.RootedDensity
