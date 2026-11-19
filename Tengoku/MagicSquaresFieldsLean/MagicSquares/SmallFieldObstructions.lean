import Tengoku.MagicSquaresFieldsLean.MagicSquares.Characters.PowerTest
import Tengoku.Seed.Algebra.Polynomial.Roots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- Nine distinct entries require at least nine elements in the field.-/
theorem isNParker_of_card_lt_nine (n : ℕ) (hq : Fintype.card F < 9) : IsNParker F n := by
  rintro ⟨M, _, hdist, _⟩
  have hcard : 9 ≤ Fintype.card F := by
    simpa using Fintype.card_le_of_injective M.entries hdist
  exact (not_le_of_gt hq) hcard

/-- If the power subgroup has fewer than eight nonzero elements, a magic
square cannot have nine distinct power entries. The polynomial root bound
proves this without choosing a concrete model of the finite field.-/
theorem isNParker_of_power_index_bound {n : ℕ} (hn : 0 < n)
    (hsmall : (Fintype.card F - 1) / powerIndex n (Fintype.card F) < 8) :
    IsNParker F n := by
  classical
  let c := (Fintype.card F - 1) / powerIndex n (Fintype.card F)
  have hq : 0 < Fintype.card F - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  have hc : 0 < c := Nat.div_pos
    (Nat.le_of_dvd hq (Nat.gcd_dvd_right n (Fintype.card F - 1))) (powerIndex_pos hn)
  let p : Polynomial F := Polynomial.X ^ (c + 1) - Polynomial.X
  have hdeg : p.natDegree = c + 1 := by
    dsimp [p]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simp
      omega
  have hp : p ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  rintro ⟨M, _, hdist, hpowers⟩
  apply hp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hdist
  · intro i
    obtain hzero | hpow := (isNthPower_iff_zero_or_pow_eq_one hn _).mp (hpowers i)
    · simp [p, hzero]
    · have hpow' : M.entries i ^ c = 1 := hpow
      simp [p, pow_succ, hpow']
  · rw [hdeg, Fintype.card_fin]
    omega

/-- The small cube exceptions follow uniformly from the power-count obstruction.-/
theorem cubeParker_of_card_small
    (hq : Fintype.card F = 3 ∨ Fintype.card F = 5 ∨ Fintype.card F = 7 ∨
      Fintype.card F = 13 ∨ Fintype.card F = 19) : IsNParker F 3 := by
  rcases hq with hq | hq | hq | hq | hq
  all_goals apply isNParker_of_power_index_bound (by norm_num : 0 < 3)
  all_goals norm_num [hq, powerIndex, Nat.gcd]

/-- The first six odd square exceptions need no exhaustive search.-/
theorem squareParker_of_card_small
    (hq : Fintype.card F = 3 ∨ Fintype.card F = 5 ∨ Fintype.card F = 7 ∨
      Fintype.card F = 9 ∨ Fintype.card F = 11 ∨ Fintype.card F = 13) : IsParker F := by
  change IsNParker F 2
  rcases hq with hq | hq | hq | hq | hq | hq
  all_goals apply isNParker_of_power_index_bound (by norm_num : 0 < 2)
  all_goals norm_num [hq, powerIndex, Nat.gcd]

end MagicSquares
