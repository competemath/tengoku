import Tengoku.EgzFormalProof.EGZ.Balanced.IntegerApproximation
import Tengoku.EgzFormalProof.EGZ.Balanced.RationalCoefficients

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The balanced-combination lemma

The positive rational barycenter is chosen at the largest centrality.
Bounded integer correction then supplies every sufficiently large weight,
with its lower fraction and threshold independent of centrality.
-/

namespace EGZ

/-- The balanced-combination lemma, with the uniform quantifier order in
the statement `BalancedCombinationLemma`.-/
theorem balanced_combination_lemma : BalancedCombinationLemma := by
  intro d D ε hε
  obtain ⟨β, hβ, hsum, hvec, hcap⟩ :=
    D.positive_rational_capped_barycenter_exists (η := ε / 2) (by positivity)
  exact D.exists_coefficients_of_rational ε hε β hβ hsum hvec hcap

end EGZ
