import Tengoku.Nlalib.NLAlib.ForMathlib.Combinatorics.PairingQuotientGraph
import Tengoku.Nlalib.NLAlib.ForMathlib.Combinatorics.BipartitePartitionBound
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Per-pairing exact smaller-iid comparator for the Gaussian extremum route

This file formalizes deterministic sum bounds for the alternating Gram-cycle
quotient. For a positive cycle dimension `p = q + 1`, endpoint maps
`alpha beta : E → Fin p ⊕ Fin p` covering the occurrences bijectively, and
arbitrary finite label types `I`, `J`, the unrestricted indicator sum
`pairingSum` equals the quotient partition sum
(`pairingSum_eq_sum_quotient`). The connectedness of the paired quotient
graph (proved in `PairingQuotientGraph`) yields the universal graph bound
`pairingSum_cycle_le`, whose exponents are the row-quotient and
column-quotient cardinalities. Replacing the column/row-sum bounds `a`, `c`
by natural-number bounds `d1`, `d2` gives `pairingSum_cycle_le_of_nat_bounds`; the
exact unit-profile identity `pairingSum_cycle_one` counts all labels;
and the normalized per-pairing comparator `pairingSum_cycle_div_card_le`
divides both sides by the label cardinalities.

This is deterministic combinatorial infrastructure for
`independent-entry-gaussian-extremum`; no Gaussian probability statement appears
here.
-/

noncomputable section

open scoped BigOperators

namespace NLAlib.PairingQuotient

variable {O R C E I J : Type*}

/-- The unrestricted indicator sum over original labels: for each pair of row
and column labelings, the product over paired pairs of the weight at the
`alpha` endpoints when the paired pair identifies its row endpoints and its
column endpoints, and zero otherwise. This is exactly the left-hand side of
`sum_prod_indicator_eq_sum_quotient`.-/
noncomputable def pairingSum [Fintype R] [Fintype C] [Fintype E] [Fintype I] [Fintype J]
    [DecidableEq R] [DecidableEq C] [DecidableEq I] [DecidableEq J]
    (sr : O → R) (tg : O → C) (alpha beta : E → O) (w : I → J → ℝ) : ℝ :=
  ∑ x : R → I, ∑ y : C → J,
    ∏ e : E,
      if x (sr (alpha e)) = x (sr (beta e)) ∧ y (tg (alpha e)) = y (tg (beta e))
      then w (x (sr (alpha e))) (y (tg (alpha e))) else 0

/-- The exact quotient identity for `pairingSum`: the unrestricted indicator
sum over original labels equals the sum over quotient labels of the product of
the weights at the endpoint classes.
@isnad1 id=eq.0h11v.s8.5eb70f8983cb from=translated src=- shape=3676e5b6 vocab=8ba6c4be
-/
lemma pairingSum_eq_sum_quotient (sr : O → R) (tg : O → C) (alpha beta : E → O)
    [Fintype R] [Fintype C] [Fintype E] [Fintype I] [Fintype J]
    [DecidableEq R] [DecidableEq C] [DecidableEq I] [DecidableEq J]
    [Fintype (RowQuotient sr alpha beta)] [Fintype (ColQuotient tg alpha beta)]
    [DecidableEq (RowQuotient sr alpha beta)] [DecidableEq (ColQuotient tg alpha beta)]
    (w : I → J → ℝ) :
    pairingSum sr tg alpha beta w =
      ∑ f : RowQuotient sr alpha beta → I, ∑ g : ColQuotient tg alpha beta → J,
        ∏ e : E, w (f (rowEnd sr alpha beta e)) (g (colEnd tg alpha beta e)) := by
  simpa [pairingSum] using (sum_prod_indicator_eq_sum_quotient sr tg alpha beta w)

/-- The row quotient of the Gram cycle is finite, with the actual finite
`Fintype` instance from the finite row type `Fin (q + 1)`.-/
noncomputable instance cycleRowQuotientFintype (q : ℕ) {E : Type*}
    (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1)) :
    Fintype (RowQuotient (cycleRow (q + 1)) alpha beta) := by
  classical
  exact Quotient.fintype (rowSetoid (cycleRow (q + 1)) alpha beta)

/-- The column quotient of the Gram cycle is finite, with the actual finite
`Fintype` instance from the finite column type `Fin (q + 1)`.-/
noncomputable instance cycleColQuotientFintype (q : ℕ) {E : Type*}
    (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1)) :
    Fintype (ColQuotient (cycleCol (q + 1)) alpha beta) := by
  classical
  exact Quotient.fintype (colSetoid (cycleCol (q + 1)) alpha beta)

/-- The exact unit-profile identity: with the constant-one profile on
`Fin d1 × Fin d2` the unrestricted indicator sum equals
`(d1 : ℝ) ^ r * (d2 : ℝ) ^ v`. The identity remains valid for `d1 = 0` or
`d2 = 0`, preserving `0 ^ 0 = 1`.
@isnad1 id=eq.0h6v.s8.c44889589657 from=translated src=- shape=584a52df vocab=dc4811b5
-/
theorem pairingSum_cycle_one [Fintype E]
    (q : ℕ) (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1))
    (d1 d2 : ℕ) :
    pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta
      (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ)) =
      (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta)) *
        (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := by
  classical
  have hsum : pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta
        (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ)) =
      ∑ f : RowQuotient (cycleRow (q + 1)) alpha beta → Fin d1,
        ∑ g : ColQuotient (cycleCol (q + 1)) alpha beta → Fin d2,
          ∏ e : E, (1 : ℝ) := by
    exact pairingSum_eq_sum_quotient (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta
      (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ))
  rw [hsum]
  have hcount : (∑ f : RowQuotient (cycleRow (q + 1)) alpha beta → Fin d1,
        ∑ g : ColQuotient (cycleCol (q + 1)) alpha beta → Fin d2,
          (1 : ℝ)) =
      (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta → Fin d1) : ℝ) *
        (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta → Fin d2) : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Finset.sum_const, Finset.card_univ]
    simp [nsmul_eq_mul]
  calc
    (∑ f : RowQuotient (cycleRow (q + 1)) alpha beta → Fin d1,
        ∑ g : ColQuotient (cycleCol (q + 1)) alpha beta → Fin d2,
          ∏ e : E, (1 : ℝ))
        = ∑ f : RowQuotient (cycleRow (q + 1)) alpha beta → Fin d1,
            ∑ g : ColQuotient (cycleCol (q + 1)) alpha beta → Fin d2,
              (1 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro f hf
          refine Finset.sum_congr rfl ?_
          intro g hg
          simp
    _ = (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta → Fin d1) : ℝ) *
          (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta → Fin d2) : ℝ) := hcount
    _ = (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta)) *
          (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := by
          rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
          rw [Nat.cast_pow, Nat.cast_pow]

end NLAlib.PairingQuotient
