import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_BasicV2
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_PointsV2
import Tengoku.FltAnthropic.P2M.Sol.S_MvFormalGroup_cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvFormalGroup_cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
open scoped TensorProduct
open MvPowerSeries

universe u v

/--
@isnad1 id=eq.5h7v.s14.4d11a2b6f21b from=translated src=- shape=36843cb4 vocab=d7c23652
-/
theorem Tengoku.FltAnthropic.MvFormalGroup.cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
    {d : ℕ} (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hε : ∀ j, Coalgebra.counit (R := ZMod p) ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = 0)
    (δ δ' : CartierDual (ZMod p) (ZMod p ⊗[𝓞] R))
    (hδ : ∀ a b : ZMod p ⊗[𝓞] R, δ (a * b) =
      δ a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * δ b)
    (hδ' : ∀ a b : ZMod p ⊗[𝓞] R, δ' (a * b) =
      δ' a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * δ' b)
    (h : ∀ j, δ ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = δ' ((1 : ZMod p) ⊗ₜ[𝓞] π (X j))) :
    δ = δ' := by exact @_root_.P2MW.S_MvFormalGroup_cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul.solution 𝓞 _ p _ _ d R _ _ _ _ π hπ hε δ δ' hδ hδ' h
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
