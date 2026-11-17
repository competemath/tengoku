import Tengoku.TunnellTwoToOneMap.TunnellMap.Parking

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The triangular proposal bound

This file sums the pointwise parking estimate and obtains the exact
`m(m+1)/2` bound from Theorem 7.1.
-/

namespace TunnellMap

/--
@isnad1 id=eq.0h1v.s5.695f0b9b8c32 from=translated src=- shape=4e8db965 vocab=d17cb838
-/
theorem sum_range_add_one_mul_two (m : ℕ) :
    (Finset.sum (Finset.range m) fun i => i + 1) * 2 = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Nat.add_mul, ih]
      ring

namespace GloballyRanked

variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

/-- The proposal-count sum in Theorem 7.1.
@isnad1 id=le.2h6v.s6.38909bf4cf42 from=translated src=- shape=074ea804 vocab=378f95bf
-/
theorem proposalCount_total_le (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M)
    (order : Fin (Fintype.card S) ≃ S) (horder : I.MatchedKeyOrder M order) :
    (∑ s : S, I.proposalCount M s) ≤
      Fintype.card S * (Fintype.card S + 1) / 2 := by
  let m := Fintype.card S
  have hreindex : (∑ i : Fin m, I.proposalCount M (order i)) =
      ∑ s : S, I.proposalCount M s := order.sum_comp _
  have hpoint : (∑ i : Fin m, I.proposalCount M (order i)) ≤
      ∑ i : Fin m, (i.1 + 1) := by
    exact Finset.sum_le_sum fun i _ => I.proposalCount_le_position M hM order horder i
  have htri : (∑ i : Fin m, (i.1 + 1)) * 2 = m * (m + 1) := by
    have hfinrange : (∑ i : Fin m, (i.1 + 1)) =
        Finset.sum (Finset.range m) (fun i => i + 1) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    rw [hfinrange]
    exact sum_range_add_one_mul_two m
  rw [← hreindex, Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  calc
    (∑ i : Fin m, I.proposalCount M (order i)) * 2 ≤
        (∑ i : Fin m, (i.1 + 1)) * 2 := Nat.mul_le_mul_right 2 hpoint
    _ = m * (m + 1) := htri

end GloballyRanked

end TunnellMap
