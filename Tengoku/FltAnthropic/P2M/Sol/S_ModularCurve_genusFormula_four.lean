import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_GenusNumerics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_genusFormula_four.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_genusFormula_four

set_option autoImplicit false

namespace Ws23
namespace GenusNumerics4
open ModularCurve

/--
@isnad1 id=eq.0h0v.s5.4ffcf73a4fbe from=translated src=- shape=36093055 vocab=89773dcd
-/
theorem divisors_eq : Nat.divisors 4 = {1, 2, 4} := by decide

/--
@isnad1 id=eq.0h0v.s3.e07bac76d0d6 from=translated src=- shape=3c26ae4f vocab=93177ece
-/
theorem dedekindPsi_eq : dedekindPsi 4 = 6 := by
  rw [dedekindPsi, divisors_eq]
  have h1 : Squarefree (1 : ℕ) := squarefree_one
  have h2 : Squarefree (2 : ℕ) := Nat.prime_two.prime.squarefree
  have h4 : ¬ Squarefree (4 : ℕ) := fun h => by
    have := h 2 ⟨1, by norm_num⟩
    rw [Nat.isUnit_iff] at this; omega
  rw [Finset.filter_insert, ite_eq_left h1, Finset.filter_insert, ite_eq_left h2, Finset.filter_singleton, ite_eq_right h4]
  decide

/--
@isnad1 id=eq.0h0v.s3.27515b89e8c3 from=translated src=- shape=3c26ae4f vocab=70004159
-/
theorem cuspCount_eq : cuspCount 4 = 3 := by decide

/--
@isnad1 id=eq.0h0v.s3.577b7d028368 from=translated src=- shape=3c26ae4f vocab=5e678d4a
-/
theorem nuTwo_eq : nuTwo 4 = 0 := by
  rw [nuTwo, Nat.card_eq_fintype_card]; decide

/--
@isnad1 id=eq.0h0v.s3.c4febc402bca from=translated src=- shape=3c26ae4f vocab=e3de17b5
-/
theorem nuThree_eq : nuThree 4 = 0 := by
  rw [nuThree, Nat.card_eq_fintype_card]; decide

/--
@isnad1 id=eq.0h0v.s3.ad3e1df28907 from=translated src=- shape=1ac31801 vocab=9c620cd2
-/
theorem main : genusFormula 4 = 0 := by
  rw [genusFormula, dedekindPsi_eq, cuspCount_eq, nuTwo_eq, nuThree_eq]
  norm_num

end Ws23.GenusNumerics4

/--
@isnad1 id=eq.0h0v.s3.ad3e1df28907 from=translated src=- shape=1ac31801 vocab=9c620cd2
-/
theorem solution : ModularCurve.genusFormula 4 = 0 :=
  Ws23.GenusNumerics4.main
