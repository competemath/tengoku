import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterZero.PowerCount

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Center-zero existence for general powers (paper, Theorem 12.1)

The counting input lives in `CenterZero.PowerCount`. Here the total weight
is compared with the weight of the collision parameters. A strict excess
supplies a parameter outside the bad set with nonzero power weight.

The remaining algebra turns the three conditions on x-1, x, and x+1 into
powers at all nine entries; the hypothesis on -1 handles their negatives.
-/

namespace MagicSquares

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- Products of powers are powers.
@isnad1 id=isnthpow.2h4v.s6.ea8d2dac98e9 from=translated src=- shape=fb7bd740 vocab=01c8198d
-/
theorem IsNthPower.mul {n : ℕ} {a b : F}
    (ha : IsNthPower n a) (hb : IsNthPower n b) : IsNthPower n (a * b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x * y, mul_pow x y n⟩

omit [Fintype F] [DecidableEq F] in
/-- The sign condition makes every entry of the center-zero family a power.
@isnad1 id=isnthpow.5h4v.s7.a58401749c91 from=translated src=- shape=d9d2491b vocab=f6208dfb
-/
theorem centerZero_all_entries_are_powers {n : ℕ} (hn : 0 < n) (x : F)
    (hneg : IsNthPower n (-1 : F))
    (hxm : IsNthPower n (x - 1)) (hx : IsNthPower n x)
    (hxp : IsNthPower n (x + 1)) :
    ∀ k : Fin 9, IsNthPower n ((Square3.centerZero x).entries k) := by
  have hnegx : IsNthPower n (-x) := by simpa using hneg.mul hx
  have hnegxm : IsNthPower n (1 - x) := by simpa [neg_sub] using hneg.mul hxm
  have hnegxp : IsNthPower n (-x - 1) := by
    simpa [neg_add_rev, sub_eq_add_neg, add_comm] using hneg.mul hxp
  have hzero : IsNthPower n (0 : F) := ⟨0, zero_pow hn.ne'⟩
  have hone : IsNthPower n (1 : F) := ⟨1, one_pow n⟩
  intro k
  fin_cases k <;> simp [Square3.entries, hnegx, hnegxm, hnegxp, hneg, hxm, hx, hxp, hzero, hone]

omit [Fintype F] [DecidableEq F] in
/-- In particular the sign condition is automatic for odd exponents.
@isnad1 id=isnthpow.1h2v.s5.e0bd480378ea from=translated src=- shape=c4d7943c vocab=09f57355
-/
theorem isNthPower_neg_one_of_odd {n : ℕ} (hn : Odd n) :
    IsNthPower n (-1 : F) := ⟨-1, hn.neg_one_pow⟩

end MagicSquares
