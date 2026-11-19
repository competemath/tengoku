import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Diagonal.DenseRegionEndgame
import Tengoku.OddcyclegoodmanLean.OddCycleBound.BasicBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The balanced complete `k`-partite graphon (Corollary 1.2, minimality)

The balanced complete `k`-partite graphon `W_k` is modelled on the finite probability space
`Fin k` with the uniform measure: `completePartite k i j = 1` if `i ≠ j` and `0` otherwise.
(The graphon `W_k` on `[0,1]` of the paper is its pullback along `x ↦ ⌈kx⌉`.)
We compute its kernel powers and cycle densities (equation `eq:intro-kpartite-value`), and deduce
from Theorem 1.1 that it minimises the `C_m`-density at edge density `1 - 1/k`.
-/

open MeasureTheory
open scoped ENNReal

namespace OddCycleBound

/-- The balanced complete `k`-partite graphon on the vertex set `Fin k`.-/
def completePartite (k : ℕ) : Fin k → Fin k → ℝ := fun i j => if i = j then 0 else 1

/-- The uniform probability measure on `Fin k`.-/
noncomputable def uniformFin (k : ℕ) : Measure (Fin k) := (k : ℝ≥0∞)⁻¹ • Measure.count

/--
@isnad1 id=isgrapho.0h1v.s3.2579eaec8c0c from=translated src=- shape=ca92e646 vocab=7dda4a9d
-/
lemma isGraphon_completePartite (k : ℕ) : IsGraphon (completePartite k) (uniformFin k) where
  meas := measurable_of_finite _
  nonneg i j := by unfold completePartite; split_ifs <;> norm_num
  le_one i j := by unfold completePartite; split_ifs <;> norm_num
  symm i j := by unfold completePartite; simp only [eq_comm]

end OddCycleBound
