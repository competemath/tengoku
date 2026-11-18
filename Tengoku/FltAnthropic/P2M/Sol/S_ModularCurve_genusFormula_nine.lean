import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_GenusNumerics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_genusFormula_nine.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_genusFormula_nine

set_option autoImplicit false

namespace Ws23
namespace GenusNumerics9
open ModularCurve

/--
@isnad1 id=eq.0h0v.s5.3777e276408d from=translated src=- shape=36093055 vocab=89773dcd
-/
theorem divisors_eq : Nat.divisors 9 = {1, 3, 9} := by decide

/--
@isnad1 id=eq.0h0v.s3.04c9f1e081f1 from=translated src=- shape=3c26ae4f vocab=93177ece
-/
theorem dedekindPsi_eq : dedekindPsi 9 = 12 := by
  rw [dedekindPsi, divisors_eq]
  have h1 : Squarefree (1 : ℕ) := squarefree_one
  have h3 : Squarefree (3 : ℕ) := Nat.prime_three.prime.squarefree
  have h9 : ¬ Squarefree (9 : ℕ) := fun h => by
    have := h 3 ⟨1, by norm_num⟩
    rw [Nat.isUnit_iff] at this; omega
  rw [Finset.filter_insert, ite_eq_left h1, Finset.filter_insert, ite_eq_left h3, Finset.filter_singleton, ite_eq_right h9]
  decide

/--
@isnad1 id=eq.0h0v.s3.1501676af00f from=translated src=- shape=3c26ae4f vocab=70004159
-/
theorem cuspCount_eq : cuspCount 9 = 4 := by decide

/--
@isnad1 id=eq.0h0v.s3.9b435dfbd156 from=translated src=- shape=3c26ae4f vocab=5e678d4a
-/
theorem nuTwo_eq : nuTwo 9 = 0 := by
  rw [nuTwo, Nat.card_eq_fintype_card]; decide

/--
@isnad1 id=eq.0h0v.s3.cae1440eb377 from=translated src=- shape=3c26ae4f vocab=e3de17b5
-/
theorem nuThree_eq : nuThree 9 = 0 := by
  rw [nuThree, Nat.card_eq_fintype_card]; decide

/--
@isnad1 id=eq.0h0v.s3.29cc31898eed from=translated src=- shape=1ac31801 vocab=9c620cd2
-/
theorem main : genusFormula 9 = 0 := by
  rw [genusFormula, dedekindPsi_eq, cuspCount_eq, nuTwo_eq, nuThree_eq]
  norm_num

end Ws23.GenusNumerics9

/--
@isnad1 id=eq.0h0v.s3.29cc31898eed from=translated src=- shape=1ac31801 vocab=9c620cd2
-/
theorem solution : ModularCurve.genusFormula 9 = 0 :=
  Ws23.GenusNumerics9.main
