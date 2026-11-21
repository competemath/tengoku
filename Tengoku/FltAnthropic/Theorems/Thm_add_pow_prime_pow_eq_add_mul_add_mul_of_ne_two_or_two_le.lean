import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_add_pow_prime_pow_eq_add_mul_add_mul_of_ne_two_or_two_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_add_pow_prime_pow_eq_add_mul_add_mul_of_ne_two_or_two_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
universe u

/--
@isnad1 id=ex.2h6v.s8.1569aa47556e from=translated src=- shape=5775e048 vocab=9f5f6576
-/
theorem _root_.Tengoku.FltAnthropic.add_pow_prime_pow_eq_add_mul_add_mul_of_ne_two_or_two_le
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (n r : ℕ) (hr : 1 ≤ r) (h2 : p ≠ 2 ∨ 2 ≤ r)
    (u v : A) :
    ∃ w : A, (u + (p : A) ^ r * v) ^ (p ^ n) =
      u ^ (p ^ n) + (p : A) ^ (n + r) * u ^ (p ^ n - 1) * v + (p : A) ^ (n + r + 1) * w := by exact @_root_.P2MW.S_add_pow_prime_pow_eq_add_mul_add_mul_of_ne_two_or_two_le.solution A _ p _ n r hr h2 u v
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
