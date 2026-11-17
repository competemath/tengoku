import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology

import Tengoku.FltAnthropic.Theorems.Thm_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_coeffHeckeFun_mem_coeffParabolicCocycles.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_coeffHeckeFun_mem_coeffParabolicCocycles

set_option autoImplicit false

open scoped MatrixGroups

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (heckeConjMat heckeUpper coe_heckeConjSL heckeConj coe_heckeConj transferAux coe_transferAux coeffCocycles mem_coeffCocycles_iff IsParabolicCocycle coeffParabolicCocycles mem_coeffParabolicCocycles_iff coeffHeckeFun coeffHeckeFun_apply coeffHeckeFun_mem_coeffCocycles)
namespace ParabolicHeckeSol
open _root_.HeckeEis

open CongruenceSubgroup Function
open scoped MatrixGroups

theorem trace_heckeConjMat (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : (heckeConjMat ℓ g).trace = g.trace := by
  simp [heckeConjMat, Matrix.trace_fin_two]

section Orbit

variable {N ℓ : ℕ} [NeZero ℓ] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)

variable {ρ a}

variable (γ : Gamma0 N) (x : Gamma0 N ⧸ heckeUpper N ℓ)

variable {γ x}

end Orbit

section Main

variable {N ℓ : ℕ} [NeZero ℓ] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable {ρ : Representation K (Gamma0 N) V} {a : V →ₗ[K] V}

end Main

end HeckeEis.ParabolicHeckeSol

end
