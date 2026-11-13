import Tengoku.Seed.Data.Nat.Choose.Basic
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Ratios of adjacent binomial coefficients

The exact finite ratio used when a determinant minor loses one column.
-/

namespace Nat

/-- The ratio of consecutive binomial levels, after an admissible fixed-size
shift. The denominator is nonzero under the displayed size conditions.-/
theorem cast_choose_pred_div_choose {n d s : ℕ} (hd : 0 < d) (hds : d ≤ s) (hsn : s ≤ n) :
    (((n - (d - 1)).choose (s - (d - 1)) : ℕ) : ℝ) / ((n - d).choose (s - d) : ℝ) =
      ((n - d + 1 : ℕ) : ℝ) / ((s - d + 1 : ℕ) : ℝ) := by
  have hn : n - (d - 1) = n - d + 1 := by omega
  have hs : s - (d - 1) = s - d + 1 := by omega
  rw [hn, hs]
  have hc : (0 : ℝ) < ((n - d).choose (s - d) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (Nat.sub_le_sub_right hsn d))
  apply (div_eq_div_iff hc.ne' (by positivity)).mpr
  exact_mod_cast (Nat.add_one_mul_choose_eq (n - d) (s - d)).symm

end Nat
