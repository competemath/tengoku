import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_EisensteinSeries_WeierstrassZeta
import Tengoku.FltAnthropic.P2M.Sol.S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Real MatrixGroups Matrix

/--
@isnad1 id=and.0h2v.s10.582259ad036c from=translated src=- shape=ef764f85 vocab=fbc1e250
-/
theorem EisensteinSeries.eisensteinG1_apply_smul_and_eisensteinG1_add (N : ℕ) [NeZero N]
    (τ : UpperHalfPlane) :
    (∀ (γ : SL(2, ℤ)) (v : Fin 2 → ℤ),
        EisensteinSeries.eisensteinG1 N v (γ • τ) =
          UpperHalfPlane.denom γ τ *
            EisensteinSeries.eisensteinG1 N (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ) ∧
    (∀ v w : Fin 2 → ℤ, (¬ ∀ i, (N : ℤ) ∣ v i) →
        EisensteinSeries.eisensteinG1 N (v + (N : ℤ) • w) τ =
          EisensteinSeries.eisensteinG1 N v τ) := by exact @_root_.P2MW.S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.solution N _ τ
