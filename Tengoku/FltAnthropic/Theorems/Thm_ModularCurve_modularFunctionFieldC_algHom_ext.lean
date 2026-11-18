import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_modularFunctionFieldC_algHom_ext

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_modularFunctionFieldC_algHom_ext.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open ModularCurve
theorem ModularCurve.modularFunctionFieldC_algHom_ext (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ] {A : Type*} [Semiring A] [Algebra K A]
    {f g : modularFunctionFieldC K ℓ →ₐ[K] A}
    (h1 : f ⟨jqModC K, jqModC_mem K ℓ⟩ = g ⟨jqModC K, jqModC_mem K ℓ⟩)
    (h2 : f ⟨jqNModC K ℓ, jqNModC_mem K ℓ⟩ = g ⟨jqNModC K ℓ, jqNModC_mem K ℓ⟩) : f = g := by exact @_root_.P2MW.S_ModularCurve_modularFunctionFieldC_algHom_ext.solution K _ ℓ _ A _ _ f g h1 h2
