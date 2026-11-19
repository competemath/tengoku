import Tengoku.Linearhadwiger.HadwigerLean.Graph.SmallConnected.PackedMaximality
import Tengoku.Linearhadwiger.HadwigerLean.Graph.SmallConnected.TBound
import Tengoku.Linearhadwiger.HadwigerLean.Graph.SmallConnected.KTBound
import Tengoku.Seed.Analysis.Complex.ExponentialBounds
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exceptional sets in the quotient graph
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def highCrossVertices
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (X : Finset V) (k : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∉ X ∧
    3 * 6400 * (k : ℝ) ≤ ((Q.neighborFinset v ∩ X).card : ℝ)

noncomputable def highDegreeVertices
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (X Y : Finset V) (d t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∉ X ∧ v ∉ Y ∧
    20 * (d : ℝ) * Real.log (t : ℝ) ≤ (Q.degree v : ℝ)

end HadwigerLean
