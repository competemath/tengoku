import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.FltAnthropic.P2M.Sol.S_IharaLemma_IdempotentSplitting_eq_smul_of_smul_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IharaLemma_IdempotentSplitting_eq_smul_of_smul_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem IharaLemma.IdempotentSplitting.eq_smul_of_smul_eq_zero {B : Type} [CommRing B]
    (S : IharaLemma.IdempotentSplitting B) {M : Type} [AddCommGroup M] [Module B M]
    {u : B} {y : M} (huy : u • y = 0) (i₀ : Fin S.n) (hu : ∀ j, j ≠ i₀ → u ∉ S.𝔪 j) :
    y = S.e i₀ • y := by exact @_root_.P2MW.S_IharaLemma_IdempotentSplitting_eq_smul_of_smul_eq_zero.solution B _ S M _ _ u y huy i₀ hu
