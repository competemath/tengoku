import Tengoku.Rank3kum.Rank3KUM.TightFlatAutomatic
import Tengoku.Rank3kum.Rank3KUM.ContractInterleave

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_nonempty_proper_tight` (it only prints; the queue checks the axioms of every declaration). -/

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
Any nonempty proper tight set resolves the rank-three cyclic-order problem:
the rank-one case uses contraction, and the rank-two case uses restriction.
@isnad1 id=ex.8h4v.s7.0639d0f5ae1a from=translated src=- shape=3b1a85b6 vocab=608de93e
-/
theorem exists_cyclicBasisOrder3_of_nonempty_proper_tight
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  rcases
      (nonempty_proper_tight_flat_classification
        M k hE hRank hEcard hk hDense
        hX hXnonempty hXproper).2 with
    hOne | hTwo
  · exact
      exists_cyclicBasisOrder3_of_tight_rank_one
        M k hk hE hRank hEcard hDense hX hOne.1
  · exact
      exists_cyclicBasisOrder3_of_tight_rank_two
        M k hk hE hRank hEcard hDense hX hTwo.1

end

end Rank3KUM
