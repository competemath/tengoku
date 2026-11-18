import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity
import Tengoku.FltAnthropic.P2M.Sol.S_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd
    (L : ℕ) [NeZero L] (χ : DirichletCharacter ℂ L) (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    ∃ E : ModularForm (Gamma1 L) 1,
      (∀ γ : SL(2, ℤ), γ ∈ Gamma0 L → ∀ τ : UpperHalfPlane,
        E (γ • τ) =
          χ ((γ 1 1 : ℤ) : ZMod L) *
            ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (1 : ℤ) * E τ)) ∧
      ModularFormClass.qCoeff E 0 =
        -(∑ a ∈ Finset.range L, (a : ℂ) * χ (a : ZMod L)) / (2 * L) ∧
      ∀ n : ℕ, 0 < n → ModularFormClass.qCoeff E n = ∑ d ∈ n.divisors, χ (d : ZMod L) := by exact @_root_.P2MW.S_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd.solution L _ χ hχ hodd
