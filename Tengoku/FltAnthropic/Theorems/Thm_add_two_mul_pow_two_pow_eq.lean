import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_add_two_mul_pow_two_pow_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_add_two_mul_pow_two_pow_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
universe u

/--
@isnad1 id=ex.1h4v.s8.3310651f377b from=translated src=- shape=397204ec vocab=dde3f2c6
-/
theorem _root_.Tengoku.FltAnthropic.add_two_mul_pow_two_pow_eq
    {A : Type u} [CommRing A] (n : ℕ) (hn : 1 ≤ n) (u v : A) :
    ∃ w : A, (u + 2 * v) ^ (2 ^ n) =
      u ^ (2 ^ n) + 2 ^ (n + 1) * (u ^ (2 ^ n - 1) * v + u ^ (2 ^ n - 2) * v ^ 2) + 2 ^ (n + 2) * w := by exact @_root_.P2MW.S_add_two_mul_pow_two_pow_eq.solution A _ n hn u v
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
