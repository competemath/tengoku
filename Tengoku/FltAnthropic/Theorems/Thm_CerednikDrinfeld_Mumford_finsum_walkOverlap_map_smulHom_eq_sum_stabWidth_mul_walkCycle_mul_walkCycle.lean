import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_WalkOverlap
import Tengoku.Seed.Algebra.BigOperators.Finprod
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Mumford_finsum_walkOverlap_map_smulHom_eq_sum_stabWidth_mul_walkCycle_mul_walkCycle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Mumford_finsum_walkOverlap_map_smulHom_eq_sum_stabWidth_mul_walkCycle_mul_walkCycle.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.finsum_walkOverlap_map_smulHom_eq_sum_stabWidth_mul_walkCycle_mul_walkCycle
    {G : Type} [Group G] {W : Type} [DecidableEq W] [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hfin : ∀ w : W, Finite (stabilizer G w))
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)] {E : Type} [Fintype E]
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    ∑ᶠ γ : G, walkOverlap P (Q.map (smulHom γ)) =
      ∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) *
        (walkCycle 𝒯 (fun e => (eE e).1) P e * walkCycle 𝒯 (fun e => (eE e).1) Q e) := by exact @_root_.P2MW.S_CerednikDrinfeld_Mumford_finsum_walkOverlap_map_smulHom_eq_sum_stabWidth_mul_walkCycle_mul_walkCycle.solution G _ W _ _ 𝒯 _ hfin τ hτ hadj _ E _ eE u v u' v' P Q
