import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Analysis.SpecialFunctions.Sqrt
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Exact scalar threshold identities for the auxiliary nonstandard route -/

namespace QuadraticCarleson

set_option autoImplicit false

/--
@isnad1 id=eq.3h3v.s7.131a4072d9b5 from=translated src=- shape=b6ac650e vocab=e685659c
-/
theorem sqrt_mul_threshold_rpow {a w p : ℝ}
    (ha : 0 < a) (hw : 0 < w) (hp : 0 < p) :
    Real.sqrt w * (a * w ^ (-1 / p)) ^ (1 - p / 2) =
      a ^ (1 - p / 2) * w ^ ((p - 1) / p) := by
  rw [Real.sqrt_eq_rpow,
    Real.mul_rpow ha.le (Real.rpow_nonneg hw.le _), ← Real.rpow_mul hw.le,
    mul_left_comm, ← Real.rpow_add hw]
  have he : (1 / 2 : ℝ) + (-1 / p) * (1 - p / 2) = (p - 1) / p := by
    field_simp
    ring
  rw [he]

/--
@isnad1 id=eq.3h3v.s7.8c5b63e28b3e from=translated src=- shape=1d02caa7 vocab=f04be908
-/
theorem positive_threshold_rpow_one_sub {a w p : ℝ}
    (ha : 0 < a) (hw : 0 < w) (hp : 0 < p) :
    (a * w ^ (-1 / p)) ^ (1 - p) =
      a ^ (1 - p) * w ^ ((p - 1) / p) := by
  rw [Real.mul_rpow ha.le (Real.rpow_nonneg hw.le _), ← Real.rpow_mul hw.le]
  have he : (-1 / p) * (1 - p) = (p - 1) / p := by
    field_simp
    ring
  rw [he]

/--
@isnad1 id=eq.0h1v.s6.d49a416745eb from=translated src=- shape=39c7793b vocab=94a54071
-/
theorem reciprocal_holder_quotient (p : ℝ) :
    1 / (p / (p - 1)) = (p - 1) / p :=
  one_div_div (a := p) (b := p - 1)

end QuadraticCarleson
