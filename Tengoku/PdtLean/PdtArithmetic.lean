import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace PDT

/-!
# Extended golden arithmetic bedrock (kernel-checked integer/ℚ identities)

Doc-comments give the field-theoretic meaning; the theorems are the integer/ℚ identities.
-/

theorem prime_23 : Nat.Prime 23 := by norm_num
theorem prime_283 : Nat.Prime 283 := by norm_num

end PDT
