import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_GenusNumerics
import Tengoku.FltAnthropic.P2M.Sol.S_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open ModularCurve
/--
@isnad1 id=eq.2h2v.s10.b2ddf0b0c31c from=translated src=- shape=23bf6158 vocab=9524b7f3
-/
theorem ZMod.natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree (n : ℕ) [NeZero n]
    (τ : ZMod n × ZMod n →+ ZMod n × ZMod n) (hτ : ∀ v, τ (τ v) + τ v + v = 0)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ v : ZMod n × ZMod n, addOrderOf v = p ∧ ∀ k : ℕ, τ v ≠ k • v) :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n ∧ H.map τ = H}
      = nuThree n := by exact @_root_.P2MW.S_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree.solution n _ τ hτ hns
