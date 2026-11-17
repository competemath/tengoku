import Tengoku.Jsp000570Lean.Erdos700.Arithmetic
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Exact integer quotient expansions for the four rows of the digit table.
The cubic coefficients are explicitly `1,1,1,0` to match the digit-support
interface.  Legality of the lower digits is proved in `ParameterDigits`.
-/

namespace Erdos700.FourPrime.RowExpansions

/--
@isnad1 id=eq.1h4v.s7.1719a95760ae from=translated src=- shape=ae1f7e94 vocab=a4b73c6f
-/
theorem row_p (p a b c : ℤ) (hp : 0 < p) :
    (p * (p + a) * (p + b) * (p + c)) / p =
      1 * p ^ 3 + (a + b + c) * p ^ 2 +
        (a * b + a * c + b * c) * p + a * b * c := by
  apply Int.ediv_eq_of_eq_mul_right (ne_of_gt hp)
  ring

/--
@isnad1 id=eq.2h4v.s8.638c6f5b4ef2 from=translated src=- shape=a6d66d91 vocab=cb5d5132
-/
theorem row_a (p a b c : ℤ) (hp : 0 < p) (ha : 0 ≤ a) :
    (p * (p + a) * (p + b) * (p + c)) / (p + a) =
      1 * (p + a) ^ 3 + (b + c - 3 * a) * (p + a) ^ 2 +
        (b * c - 2 * a * (b + c) + 3 * a ^ 2 - 1) * (p + a) +
        (p + a - a * (b - a) * (c - a)) := by
  apply Int.ediv_eq_of_eq_mul_right (by omega : p + a ≠ 0)
  ring

/--
@isnad1 id=eq.2h4v.s8.5371a25c2be1 from=translated src=- shape=a4f01e47 vocab=cb5d5132
-/
theorem row_b (p a b c : ℤ) (hp : 0 < p) (hb : 0 ≤ b) :
    (p * (p + a) * (p + b) * (p + c)) / (p + b) =
      1 * (p + b) ^ 3 + (a + c - 3 * b - 1) * (p + b) ^ 2 +
        (p + b - ((2 * b - a) * c + 2 * a * b - 3 * b ^ 2)) * (p + b) +
        b * (b - a) * (c - b) := by
  apply Int.ediv_eq_of_eq_mul_right (by omega : p + b ≠ 0)
  ring

/--
@isnad1 id=eq.2h4v.s8.ad7513461e12 from=translated src=- shape=2555d057 vocab=cb5d5132
-/
theorem row_c (p a b c : ℤ) (hp : 0 < p) (hc : 0 ≤ c) :
    (p * (p + a) * (p + b) * (p + c)) / (p + c) =
      0 * (p + c) ^ 3 + (p + c - (3 * c - a - b)) * (p + c) ^ 2 +
        (3 * c ^ 2 - 2 * c * (a + b) + a * b - 1) * (p + c) +
        (p + c - c * (c - a) * (c - b)) := by
  apply Int.ediv_eq_of_eq_mul_right (by omega : p + c ≠ 0)
  ring

end Erdos700.FourPrime.RowExpansions
