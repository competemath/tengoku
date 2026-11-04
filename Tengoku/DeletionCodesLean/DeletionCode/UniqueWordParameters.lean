import Tengoku.Seed.Analysis.SpecialFunctions.Log.Base
import Tengoku.Seed.Data.Nat.Choose.Basic
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms uniquenessLength_eq_ceil` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eight_mul_choose_le_pow` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms collision_fraction_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms count_lower_bounds` (it only prints; the queue checks the axioms of every declaration). -/

/-!
The numerical choice in manuscript lemma `lem:family`.
The computable natural parameter is proved equal to the ordinary real-log
ceiling expression. Its collision allowance is at most one eighth, so any
corresponding union-bound estimate retains at least seven eighths of all
words and, for positive word length, at least 2^(n-1) words.
The counting and overlapping-window collision arguments are separate.
-/

namespace DeletionCode.UniqueWordParameters

/-- The manuscript's k = 2 ceil(log_2 n) + 2, computed with ceiling logarithms.-/
def uniquenessLength (n : ℕ) : ℕ := 2 * Nat.clog 2 n + 2

/--
@isnad1 id=le.0h1v.s3.289d4abd7da0 from=translated src=- shape=8a62b088 vocab=5d567900
-/
theorem uniquenessLength_ge_two (n : ℕ) : 2 ≤ uniquenessLength n := by
  unfold uniquenessLength
  omega

/-- Exact agreement with the natural ceiling of the real logarithm.
@isnad1 id=eq.0h1v.s5.95308c280fb3 from=translated src=- shape=b03aa3b7 vocab=1813fe67
-/
theorem uniquenessLength_eq_natCeil (n : ℕ) :
    uniquenessLength n = 2 * ⌈Real.logb 2 (n : ℝ)⌉₊ + 2 := by
  have hceil : ⌈Real.logb 2 (n : ℝ)⌉₊ = Nat.clog 2 n := by
    simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 n
  rw [hceil]
  rfl

/-- For positive n, the natural ceiling is the ordinary integer ceiling
appearing in the manuscript; the logarithm is nonnegative.
@isnad1 id=eq.1h1v.s5.5eba03d215cd from=translated src=- shape=e36d1574 vocab=a6de1186
-/
theorem uniquenessLength_eq_ceil (n : ℕ) (hn : 1 ≤ n) :
    (uniquenessLength n : ℤ) = 2 * ⌈Real.logb 2 (n : ℝ)⌉ + 2 := by
  rw [uniquenessLength_eq_natCeil]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [Int.natCast_ceil_eq_ceil
    (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hn))]

/--
@isnad1 id=le.0h1v.s5.e565db764ba6 from=translated src=- shape=d3b2da64 vocab=fe4bc797
-/
theorem two_mul_choose_le_square (n : ℕ) : 2 * n.choose 2 ≤ n ^ 2 := by
  rw [Nat.choose_two_right]
  have hdiv := Nat.div_mul_le_self (n * (n - 1)) 2
  have hmul := Nat.mul_le_mul_left n (Nat.sub_le n 1)
  nlinarith

/--
@isnad1 id=eq.0h1v.s6.3a886ec8d67c from=translated src=- shape=b5f9297f vocab=df3a195f
-/
theorem pow_uniquenessLength (n : ℕ) :
    2 ^ uniquenessLength n = 4 * (2 ^ Nat.clog 2 n) ^ 2 := by
  unfold uniquenessLength
  rw [show 2 * Nat.clog 2 n = Nat.clog 2 n * 2 by omega, pow_add, pow_mul]
  ring

/--
@isnad1 id=le.0h1v.s5.9993b5780cce from=translated src=- shape=3ea090b6 vocab=c41cbc2e
-/
theorem four_mul_square_le_pow (n : ℕ) : 4 * n ^ 2 ≤ 2 ^ uniquenessLength n := by
  have hn := Nat.le_pow_clog (by decide : 1 < 2) n
  have hsquare := Nat.mul_le_mul hn hn
  rw [pow_uniquenessLength]
  nlinarith

/-- An exact natural-number form of the paper's collision fraction bound.
@isnad1 id=le.0h1v.s5.66f8d868303a from=translated src=- shape=9be74d0b vocab=6efa364f
-/
theorem eight_mul_choose_le_pow (n : ℕ) : 8 * n.choose 2 ≤ 2 ^ uniquenessLength n := by
  have hchoose := two_mul_choose_le_square n
  have hpow := four_mul_square_le_pow n
  omega

/-- The total pairwise collision allowance is at most one eighth.
@isnad1 id=le.0h1v.s5.22647fd0300a from=translated src=- shape=1bc8a2fa vocab=9b142e6e
-/
theorem collision_fraction_le (n : ℕ) :
    (n.choose 2 : ℚ) / (2 : ℚ) ^ uniquenessLength n ≤ 1 / 8 := by
  have hpow : (0 : ℚ) < 2 ^ uniquenessLength n := pow_pos (by norm_num) _
  have hscaled : (8 : ℚ) * n.choose 2 ≤ (2 : ℚ) ^ uniquenessLength n := by
    exact_mod_cast eight_mul_choose_le_pow n
  apply (div_le_iff₀ hpow).mpr
  nlinarith

/--
@isnad1 id=le.0h1v.s6.6a57424d9090 from=translated src=- shape=1bc8a2fa vocab=81267769
-/
theorem collision_fraction_le_real (n : ℕ) :
    (n.choose 2 : ℝ) / (2 : ℝ) ^ uniquenessLength n ≤ 1 / 8 := by
  have hpow : (0 : ℝ) < 2 ^ uniquenessLength n := pow_pos (by norm_num) _
  have hscaled : (8 : ℝ) * n.choose 2 ≤ (2 : ℝ) ^ uniquenessLength n := by
    exact_mod_cast eight_mul_choose_le_pow n
  apply (div_le_iff₀ hpow).mpr
  nlinarith

/--
@isnad1 id=le.0h1v.s6.ecbfebc61966 from=translated src=- shape=01a5a73e vocab=f4a9e528
-/
theorem seven_eighths_le_retained (n : ℕ) :
    (7 / 8 : ℚ) * (2 : ℚ) ^ n ≤
      (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ uniquenessLength n) * (2 : ℚ) ^ n := by
  apply mul_le_mul_of_nonneg_right
  · have h := collision_fraction_le n
    linarith
  · exact le_of_lt (pow_pos (by norm_num : (0 : ℚ) < 2) n)

/--
@isnad1 id=le.0h1v.s7.f88b4ae30d4d from=translated src=- shape=01a5a73e vocab=e25f7b59
-/
theorem seven_eighths_le_retained_real (n : ℕ) :
    (7 / 8 : ℝ) * (2 : ℝ) ^ n ≤
      (1 - (n.choose 2 : ℝ) / (2 : ℝ) ^ uniquenessLength n) * (2 : ℝ) ^ n := by
  apply mul_le_mul_of_nonneg_right
  · have h := collision_fraction_le_real n
    linarith
  · exact le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) n)

/--
@isnad1 id=le.1h1v.s6.4c56f1f485c4 from=translated src=- shape=8e181187 vocab=37117d3e
-/
theorem half_words_le_seven_eighths (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℚ) ^ (n - 1) ≤ (7 / 8 : ℚ) * (2 : ℚ) ^ n := by
  have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  rw [hpow]
  have hnonneg := le_of_lt (pow_pos (by norm_num : (0 : ℚ) < 2) (n - 1))
  nlinarith

/--
@isnad1 id=le.1h1v.s6.0de50f3fa6ca from=translated src=- shape=8e181187 vocab=5ce83074
-/
theorem half_words_le_seven_eighths_real (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ (n - 1) ≤ (7 / 8 : ℝ) * (2 : ℝ) ^ n := by
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  rw [hpow]
  have hnonneg := le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) (n - 1))
  nlinarith

/-- A finite cardinality satisfying the collision union bound inherits
both of the manuscript's concluding lower bounds.
@isnad1 id=and.2h2v.s7.eeaf40275e94 from=translated src=- shape=5fceb930 vocab=f4a9e528
-/
theorem count_lower_bounds (n count : ℕ) (hn : 1 ≤ n)
    (hcount : (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ uniquenessLength n) * (2 : ℚ) ^ n ≤ count) :
    (7 / 8 : ℚ) * (2 : ℚ) ^ n ≤ count ∧ 2 ^ (n - 1) ≤ count := by
  have hlarge := (seven_eighths_le_retained n).trans hcount
  refine ⟨hlarge, ?_⟩
  exact_mod_cast (half_words_le_seven_eighths n hn).trans hlarge

end DeletionCode.UniqueWordParameters
