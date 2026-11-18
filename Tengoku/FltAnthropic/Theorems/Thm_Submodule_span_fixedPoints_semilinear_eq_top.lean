import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Submodule_span_fixedPoints_semilinear_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Submodule_span_fixedPoints_semilinear_eq_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Submodule.span_fixedPoints_semilinear_eq_top
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (V : Type*) [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (ρ : (L ≃ₐ[K] L) → V →+ V)
    (hρ_smul : ∀ (σ : L ≃ₐ[K] L) (a : L) (v : V), ρ σ (a • v) = σ a • ρ σ v)
    (hρ_one : ∀ v : V, ρ 1 v = v)
    (hρ_mul : ∀ (σ τ : L ≃ₐ[K] L) (v : V), ρ (σ * τ) v = ρ σ (ρ τ v)) :
    Submodule.span L {v : V | ∀ σ : L ≃ₐ[K] L, ρ σ v = v} = ⊤ := by exact @_root_.P2MW.S_Submodule_span_fixedPoints_semilinear_eq_top.solution K L _ _ _ _ _ V _ _ _ _ ρ hρ_smul hρ_one hρ_mul
