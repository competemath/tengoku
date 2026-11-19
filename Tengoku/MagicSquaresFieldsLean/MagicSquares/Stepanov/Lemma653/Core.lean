import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma653.Multiplicity
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-!
# LN97 Theorem 6.53: first abstract counting consequence of Lemma 6.52

Once Lemma 6.52 supplies a nonzero polynomial `h` with

* multiplicity at least `M` on a finite set `T`, and
* an explicit upper bound on `natDegree h`,

the first estimate in Theorem 6.53 is immediate.

This file packages that step independently of the explicit degree
estimate from Lemma 6.52.  `SetBound` and `Complete` connect the completed
auxiliary-polynomial theorem to the full point-count estimate.
-/

/-- The generic degree/multiplicity estimate used at the start of
LN97 Theorem 6.53.
@isnad1 id=le.3h5v.s6.120cd6c240f7 from=translated src=- shape=4224d815 vocab=e977e4fc
-/
theorem card_mul_le_of_multiplicity_and_degree
    (h : Polynomial F) (T : Finset F)
    (M D : ℕ)
    (hM : 0 < M)
    (hmult : ∀ c ∈ T, M ≤ rootMultiplicity c h)
    (hdeg : h.natDegree ≤ D) :
    M * T.card ≤ D := by
  exact le_trans
    (card_mul_le_natDegree_of_rootMultiplicity
      (F := F) h T M hM hmult)
    hdeg

/-- A division-form corollary: `|T| ≤ D / M` for `M > 0`.
@isnad1 id=le.3h5v.s6.d402de6f9c32 from=translated src=- shape=5b883228 vocab=d3f21e67
-/
theorem card_le_div_of_multiplicity_and_degree
    (h : Polynomial F) (T : Finset F)
    (M D : ℕ)
    (hM : 0 < M)
    (hmult : ∀ c ∈ T, M ≤ rootMultiplicity c h)
    (hdeg : h.natDegree ≤ D) :
    T.card ≤ D / M := by
  apply (Nat.le_div_iff_mul_le hM).2
  have hmul :
      M * T.card ≤ D :=
    card_mul_le_of_multiplicity_and_degree
      (F := F) h T M D hM hmult hdeg
  simpa [Nat.mul_comm] using hmul

end LN97
end MagicSquares
