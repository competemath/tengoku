import Tengoku.FactorialHypergraphAuxiliaryErdos.FactorialHypergraph.Assembly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms FactorialHypergraph.Palomar.quantitative_auxiliary_erdos` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Proved Palomar solution

This module connects the small statement in `Challenge.lean` to the complete
proof development.  Comparator checks that this declaration has exactly the
same type as the Challenge declaration and uses only the permitted axioms.
-/

namespace FactorialHypergraph.Palomar

/--
@isnad1 id=ex.1h0v.s6.509b91bfebfc from=translated src=- shape=8f903af4 vocab=2f9e779e
-/
theorem quantitative_auxiliary_erdos (hs : UpperBoundSieveDimOne) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
      ((L + 1).factorial : ℝ) ^ eta / (100 * Real.log L)
        ≤ ((goodSet L).card : ℝ) := by
  exact main_quantitative_of_sieve_theorem hs

end FactorialHypergraph.Palomar

