import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Mumford_finite_setOf_exists_mem_darts_smul_mem_darts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Mumford_finite_setOf_exists_mem_darts_smul_mem_darts.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CerednikDrinfeld.Mumford MulAction

/--
@isnad1 id=finite.1h9v.s7.ed62bf21349b from=translated src=- shape=12e7d576 vocab=d4169622
-/
theorem CerednikDrinfeld.Mumford.finite_setOf_exists_mem_darts_smul_mem_darts
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hfin : ∀ w : W, Finite (stabilizer G w))
    {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    {γ : G | ∃ d ∈ Q.darts, γ • d ∈ P.darts ∨ (γ • d).symm ∈ P.darts}.Finite := by exact @_root_.P2MW.S_CerednikDrinfeld_Mumford_finite_setOf_exists_mem_darts_smul_mem_darts.solution G _ W _ 𝒯 _ hfin u v u' v' P Q
