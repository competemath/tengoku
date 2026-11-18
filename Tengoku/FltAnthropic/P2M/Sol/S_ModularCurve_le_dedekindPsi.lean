import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.Seed.NumberTheory.Divisors
import Tengoku.Seed.Data.Nat.Squarefree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_le_dedekindPsi.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_le_dedekindPsi

open ModularCurve Finset

theorem solution (N : ℕ) (hN : N ≠ 0) : N ≤ dedekindPsi N := by
  rw [dedekindPsi]
  have h1 : (1 : ℕ) ∈ {d ∈ N.divisors | Squarefree d} :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hN, squarefree_one⟩
  simpa using Finset.single_le_sum (f := fun d => N / d) (fun d _ => Nat.zero_le _) h1
