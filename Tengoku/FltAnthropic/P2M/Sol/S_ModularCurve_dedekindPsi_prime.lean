import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_dedekindPsi_prime.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_dedekindPsi_prime

open ModularCurve IntermediateField

noncomputable section

/--
@isnad1 id=eq.1h1v.s4.af867e63232f from=translated src=- shape=b8d1d085 vocab=15ed365f
-/
theorem solution {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 :=by
  rw [dedekindPsi, Finset.sum_filter, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  simp [hp.squarefree, Nat.div_self hp.pos]

end
