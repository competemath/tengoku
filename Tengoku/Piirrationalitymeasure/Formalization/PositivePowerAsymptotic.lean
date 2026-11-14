import Tengoku.Piirrationalitymeasure.Formalization.PositivePowerLocalLimit
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientGrowth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Ordinary diagonal coefficient asymptotics and logarithmic rates for arbitrary powers. -/

namespace PiIrrationality.PositivePower

open Filter Asymptotics PowerSeries
open scoped Topology

variable (u v : ℕ) {d : ℕ} (hd : 0 < d)

include hd in
/--
@isnad1 id=eq.4h6v.s7.bf659cf158d3 from=translated src=- shape=f176c4ce vocab=8d0d7233
-/
theorem series_diagonal_log_formula {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (q : ℕ) {n : ℕ} (hn : 0 < n) :
    Real.log (↑(coeff (q * n) (series u v d ^ n)) : ℝ) / (n : ℝ) =
      Real.log (realValue u v d x) - q * Real.log x +
        Real.log (probability u v d x n (q * n)) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs := (realValue_pos u v d hx0.le hx1).ne'
  rw [probability_extraction u v hx0 hx1,
    Real.log_mul (div_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hx0.ne'))
      (probability_pos u v hd hx0 hx1 hn _).ne',
    Real.log_div (pow_ne_zero _ hs) (pow_ne_zero _ hx0.ne'),
    Real.log_pow, Real.log_pow, Nat.cast_mul]
  field_simp

end PiIrrationality.PositivePower
