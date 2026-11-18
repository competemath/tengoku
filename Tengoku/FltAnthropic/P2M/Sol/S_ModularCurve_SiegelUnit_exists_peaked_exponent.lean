import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_SiegelUnit_sum_levelBernoulliWeight_add_mul
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_SiegelUnit_exists_peaked_exponent.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_SiegelUnit_exists_peaked_exponent

set_option autoImplicit false

namespace Peak

def W (N v : ℕ) : ℤ := 6 * (v : ℤ) ^ 2 - 6 * (N : ℤ) * (v : ℤ) + (N : ℤ) ^ 2

section sums

variable {N : ℕ} [NeZero N]

end sums

end Peak

namespace Peak

section construction

variable {N : ℕ} [NeZero N]

def wt (N : ℕ) (r : ZMod N) : ℕ := (N / Nat.gcd r.val N) * Nat.totient (Nat.gcd r.val N)

end construction

end Peak
