import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.Scalar.Coordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

theorem L_lt_q : P.L < P.q := by
  have hpq : P.p * P.q - P.alpha ^ 2 < P.q ^ 2 := by
    have halphaSq : P.q ^ 2 < P.alpha ^ 2 :=
      pow_lt_pow_left₀ P.alpha_gt_q P.q_nonneg (by norm_num)
    have hq3 : P.q < 3 * P.q ^ 2 := by
      have hthree : 0 < 3 * P.q - 1 := by linarith [P.q_gt_third]
      nlinarith [mul_pos P.q_pos hthree]
    dsimp [p]
    nlinarith
  have hsq : P.L ^ 2 < P.q ^ 2 := by
    rw [P.L_sq]
    exact hpq
  by_contra hnot
  have hqle : P.q <= P.L := le_of_not_gt hnot
  have hsquareLe : P.q ^ 2 <= P.L ^ 2 :=
    pow_le_pow_left₀ P.q_nonneg hqle 2
  exact (not_lt_of_ge hsquareLe) hsq

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
