import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_EisensteinSeries_EisensteinG
import Tengoku.FltAnthropic.P2M.Sol.S_EisensteinSeries_qExpansion_eisensteinG_coeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_EisensteinSeries_qExpansion_eisensteinG_coeff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Real Complex
open scoped Nat

theorem EisensteinSeries.qExpansion_eisensteinG_coeff (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (a : Fin 2 → ZMod N) (n : ℕ) :
    (UpperHalfPlane.qExpansion N (EisensteinSeries.eisensteinG N k a)).coeff n =
      if n = 0 then
        (if a 0 = 0 then ∑' d : {d : ℤ // (d : ZMod N) = a 1}, ((d : ℂ) ^ k)⁻¹ else 0)
      else
        (-2 * π * I) ^ k / ((k - 1)! * (N : ℂ) ^ k) *
          ∑ m ∈ n.divisors,
            ((if ((n / m : ℕ) : ZMod N) = a 0 then ZMod.stdAddChar (a 1 * (m : ZMod N)) else 0) +
              (-1) ^ k *
                (if ((n / m : ℕ) : ZMod N) = -a 0 then ZMod.stdAddChar (-(a 1 * (m : ZMod N))) else 0)) *
            (m : ℂ) ^ (k - 1) := by exact @_root_.P2MW.S_EisensteinSeries_qExpansion_eisensteinG_coeff.solution N _ k hk a n
