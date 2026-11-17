import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_FiniteField_exists_forall_affineMap_ne_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FiniteField_exists_forall_affineMap_ne_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.2h5v.s9.6ae303931e2a from=translated src=- shape=a1edf60b vocab=a6a23844
-/
theorem FiniteField.exists_forall_affineMap_ne_zero
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] {n : ℕ} {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module 𝔽 (V j)]
    (φ : ∀ j, (Fin n → 𝔽) →ᵃ[𝔽] V j) (hφ : ∀ j, ∃ x, φ j x ≠ 0)
    (hm : Fintype.card ι < Fintype.card 𝔽) :
    ∃ x, ∀ j, φ j x ≠ 0 := by exact @_root_.P2MW.S_FiniteField_exists_forall_affineMap_ne_zero.solution 𝔽 _ _ n ι _ V _ _ φ hφ hm
