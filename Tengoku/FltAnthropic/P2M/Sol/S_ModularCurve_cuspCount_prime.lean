import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_GenusNumerics
import Tengoku.Seed.Data.Nat.Totient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_cuspCount_prime.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_cuspCount_prime

open ModularCurve

/--
@isnad1 id=eq.1h1v.s3.59006f46732c from=translated src=- shape=fdf4e94d vocab=707fdb51
-/
theorem solution {p : ℕ} (hp : p.Prime) : cuspCount p = 2 := by
  rw [cuspCount, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  rw [Nat.div_one, Nat.div_self hp.pos]
  simp
