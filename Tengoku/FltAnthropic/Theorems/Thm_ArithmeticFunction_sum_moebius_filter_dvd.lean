import Tengoku.Seed.NumberTheory.ArithmeticFunction.Moebius
import Tengoku.FltAnthropic.P2M.Sol.S_ArithmeticFunction_sum_moebius_filter_dvd

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ArithmeticFunction_sum_moebius_filter_dvd.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped ArithmeticFunction.Moebius
/--
@isnad1 id=eq.2h2v.s6.759ab6267157 from=translated src=- shape=e138ab1f vocab=74709ad2
-/
theorem ArithmeticFunction.sum_moebius_filter_dvd {n m : ℕ} (hn : n ≠ 0) (hm : m ∣ n) :
    ∑ f ∈ n.divisors, ArithmeticFunction.moebius (n / f) * (if m ∣ f then 1 else 0)
      = if m = n then 1 else 0 := by exact @_root_.P2MW.S_ArithmeticFunction_sum_moebius_filter_dvd.solution n m hn hm
