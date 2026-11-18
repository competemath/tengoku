import Tengoku.CollatzGeneralizedNaturalDensity.GGMCollatz.General.Chain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Specification tests for the reduction (the example in the accompanying paper)

The example `(3, 4, [2, 4])` of the accompanying paper, divided by the common divisor `2`, becomes the worked
example `example34`, `(3, 4, [2, 1])`. We check the values of `reduce` and the conjugation `C(2N) = 2 C*(N)` for
small `N` with `decide` (`native_decide` is not used).
-/

namespace GGMCollatz

namespace Gen

/-- The example `(3, 4, [2, 4])` of the accompanying paper (it violates (d): `gcd(4, 2, 4) = 2`).-/
def example34d : FamilyGen where
  p := 3
  q := 4
  r := fun j => if j = 1 then 2 else 4
  two_le_p := by norm_num
  two_le_q := by norm_num
  coprime := by norm_num
  subcritical := example34.subcritical
  divisible := by
    intro j hj hjp
    interval_cases j <;> norm_num
  positive := by
    intro j hj hjp
    interval_cases j <;> norm_num

lemma example34d_commonDiv : CommonDiv example34d 2 where
  two_le := le_rfl
  dvd_q := by decide
  dvd_r := by
    intro j hj hjp
    change j < 3 at hjp
    interval_cases j <;> decide

lemma example34d_not_gcdOne : ¬ GcdOne example34d := fun h =>
  absurd (h 2 example34d_commonDiv.dvd_q example34d_commonDiv.dvd_r) (by norm_num)

end Gen

end GGMCollatz
