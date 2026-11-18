import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_SchurMultiplierTrivial
import Tengoku.FltAnthropic.Theorems.Thm_Ihara_hasTrivialSchurMultiplier_of_sylow
import Tengoku.FltAnthropic.Theorems.Thm_Ihara_hasTrivialSchurMultiplier_of_dicyclic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_of_prime.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_of_prime

open scoped MatrixGroups
open Matrix

namespace IharaSchurSL2

section MatrixFacts

variable {F : Type*} [Field F]

end MatrixFacts

section Card

variable {F : Type*} [Field F]

variable [Fintype F]

end Card

section SplitTorus

variable {F : Type*} [Field F]

end SplitTorus

section NonsplitTorus

open Polynomial

variable {F : Type*} [Field F] (f : F[X]) (R : Matrix (Fin 2) (Fin 2) F)
  (hR : Polynomial.aeval R f = 0)

theorem finite_adjoinRoot [Finite F] (hf0 : f ≠ 0) : Finite (AdjoinRoot f) := by
  haveI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  exact Module.finite_of_finite F

end NonsplitTorus

section Dicyclic

variable {G : Type*} [Group G]

end Dicyclic

section Arith

variable {q : ℕ} (hq : q.Prime)
include hq

end Arith

end IharaSchurSL2
open scoped _root_.P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_of_prime.IharaSchurSL2
