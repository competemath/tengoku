import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedDensity.CliqueMatching
import Tengoku.Linearhadwiger.HadwigerLean.Woven.SparseTargetRoles

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Canonical root and matching role labels in the recursive target. -/

namespace HadwigerLean.RootedDensity

/-- The clique vertex with label `i` in `K_a + b K₂`.-/
def cliqueMatchingRootLabel (a : ℕ) :
    (b : ℕ) → Fin a → CliqueMatchingLabels a b
  | 0, i => i
  | b + 1, i => Sum.inl (cliqueMatchingRootLabel a b i)

/-- Endpoint `e` of matching edge `i` in `K_a + b K₂`. In the successor
step, edge zero is new and successor indices refer to old edges.-/
def cliqueMatchingPairLabel (a : ℕ) :
    (b : ℕ) → Fin b → Fin 2 → CliqueMatchingLabels a b
  | 0, i, _ => i.elim0
  | b + 1, i, e =>
      Fin.cases (Sum.inr e)
        (fun k => Sum.inl (cliqueMatchingPairLabel a b k e)) i

/-- The clique vertices are pairwise adjacent.-/
theorem cliqueMatching_root_adj (a b : ℕ) (i k : Fin a) (hik : i ≠ k) :
    (cliqueMatchingGraph a b).Adj
      (cliqueMatchingRootLabel a b i) (cliqueMatchingRootLabel a b k) := by
  induction b with
  | zero => simpa [cliqueMatchingGraph, cliqueMatchingRootLabel] using hik
  | succ b ih =>
      simpa [cliqueMatchingGraph, cliqueMatchingRootLabel] using ih

/-- Different clique labels remain distinct at every matching depth.-/
theorem cliqueMatching_root_injective (a b : ℕ) :
    Function.Injective (cliqueMatchingRootLabel a b) := by
  induction b with
  | zero => intro i k h; exact h
  | succ b ih =>
      intro i k h
      exact ih (Sum.inl_injective h)

/-- Map the clique roots and two endpoints of every requested pair to
exactly the corresponding roles of `K_a + b K₂`.-/
def cliqueMatchingRoleLabel (a b : ℕ) :
    Woven.DistinctRoleIndex a b → CliqueMatchingLabels a b
  | .inl i => cliqueMatchingRootLabel a b i
  | .inr (.inl i) => cliqueMatchingPairLabel a b i 0
  | .inr (.inr i) => cliqueMatchingPairLabel a b i 1

end HadwigerLean.RootedDensity
