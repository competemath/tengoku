import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology Real Matrix

/--
@isnad1 id=other.1h3v.s10.926d0626c82c from=translated src=- shape=9ada8e5b vocab=841951a1
-/
theorem PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty
    (L : UpperHalfPlane → PeriodPair) (hL : ∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (N : ℕ) [NeZero N] (a : Fin 2 → ZMod N) :
    let W : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ :=
      fun b τ => (L τ).weierstrassP ((((b 0).val : ℂ) * (τ : ℂ) + (b 1).val) / N)
    (∃ F : ModularForm (CongruenceSubgroup.Gamma N) 2, ⇑F = W a) ∧
    (∀ γ : SL(2, ℤ), W a ∣[(2 : ℤ)] γ = W (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) ∧
    (a ≠ 0 → Filter.Tendsto (W a) UpperHalfPlane.atImInfty
      (𝓝 (-((π : ℂ) ^ 2 / 3) + if a 0 = 0 then (π : ℂ) ^ 2 / Complex.sin (π * (a 1).val / N) ^ 2 else 0))) := by exact @_root_.P2MW.S_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty.solution L hL N _ a
