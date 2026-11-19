import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedDensity.DisjointEdge
import Tengoku.Linearhadwiger.HadwigerLean.Graph.CliqueDensity.Theorem
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! An unrooted density threshold for a clique plus disjoint matching edges. -/

namespace HadwigerLean.RootedDensity

/-- Labels for a clique followed by `b` independent edge components.-/
def CliqueMatchingLabels (a : ℕ) : ℕ → Type
  | 0 => Fin a
  | b + 1 => CliqueMatchingLabels a b ⊕ Fin 2

instance cliqueMatchingLabelsFintype (a b : ℕ) :
    Fintype (CliqueMatchingLabels a b) := by
  induction b with
  | zero => exact inferInstanceAs (Fintype (Fin a))
  | succ b ih =>
      change Fintype (CliqueMatchingLabels a b ⊕ Fin 2)
      letI := ih
      infer_instance

/-- The target `K_a + b K₂`, with its matching edges added recursively.-/
def cliqueMatchingGraph (a : ℕ) :
    (b : ℕ) → SimpleGraph (CliqueMatchingLabels a b)
  | 0 => SimpleGraph.completeGraph (Fin a)
  | b + 1 => cliqueMatchingGraph a b ⊕g SimpleGraph.completeGraph (Fin 2)

/-- The density threshold used in Appendix F, Section 7.1.-/
noncomputable def cliqueMatchingThreshold (a b : ℕ) : ℝ :=
  30 * (a : ℝ) * Real.sqrt (Real.log (a : ℝ)) + 2 * (b : ℝ)

/-- The recursive target has exactly the expected number of labels.
@isnad1 id=eq.0h2v.s5.59e2a3039f4b from=translated src=- shape=ec571f25 vocab=35cfbeb8
-/
theorem cliqueMatchingLabels_card (a b : ℕ) :
    Fintype.card (CliqueMatchingLabels a b) = a + 2 * b := by
  induction b with
  | zero =>
      change Fintype.card (Fin a) = a
      exact Fintype.card_fin a
  | succ b ih =>
      change Fintype.card (CliqueMatchingLabels a b ⊕ Fin 2) = a + 2 * (b + 1)
      rw [Fintype.card_sum, ih]
      simp
      omega

/-- The base density threshold is nonnegative.
@isnad1 id=le.0h2v.s4.70020e264561 from=translated src=- shape=5ffe46ab vocab=1d8d2e27
-/
theorem cliqueMatchingThreshold_nonneg (a b : ℕ) :
    0 ≤ cliqueMatchingThreshold a b := by
  unfold cliqueMatchingThreshold
  positivity

/-- The target has at least three vertices outside the lone excluded case
`(a,b)=(2,0)` of the uniform woven argument.
@isnad1 id=le.2h2v.s5.f29dc592323b from=translated src=- shape=776b2a41 vocab=e151868d
-/
theorem cliqueMatchingLabels_card_ge_three
    (a b : ℕ) (ha : 2 ≤ a) (hcase : 3 ≤ a ∨ 1 ≤ b) :
    3 ≤ Fintype.card (CliqueMatchingLabels a b) := by
  rw [cliqueMatchingLabels_card]
  omega
end HadwigerLean.RootedDensity
