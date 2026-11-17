import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_MumfordPeriod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Mumford_GraphAction_dist_smul_smul.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_Mumford_GraphAction_dist_smul_smul

set_option autoImplicit false

namespace CerednikDrinfeld
export _root_.CerednikDrinfeld (Mumford.GraphAction)
namespace Mumford
export _root_.CerednikDrinfeld.Mumford (GraphAction GraphAction.smul_adj)
namespace Isom
open _root_.CerednikDrinfeld.Mumford open _root_.CerednikDrinfeld

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

def smulHom (g : G) : 𝒯 →g 𝒯 where
  toFun := fun w => g • w
  map_rel' := fun h => GraphAction.smul_adj g h

theorem dist_smul_le (g : G) (x y : W) : 𝒯.dist (g • x) (g • y) ≤ 𝒯.dist x y := by
  by_cases h : 𝒯.Reachable x y
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
    have := SimpleGraph.dist_le (p.map (smulHom 𝒯 g))
    rw [SimpleGraph.Walk.length_map, hp] at this
    exact this
  ·
    have h' : ¬ 𝒯.Reachable (g • x) (g • y) := by
      intro hr
      apply h
      obtain ⟨p⟩ := hr
      have q : 𝒯.Walk (g⁻¹ • (g • x)) (g⁻¹ • (g • y)) := p.map (smulHom 𝒯 g⁻¹)
      rw [inv_smul_smul, inv_smul_smul] at q
      exact ⟨q⟩
    rw [SimpleGraph.dist_eq_zero_of_not_reachable h, SimpleGraph.dist_eq_zero_of_not_reachable h']

theorem main (g : G) (x y : W) : 𝒯.dist (g • x) (g • y) = 𝒯.dist x y := by
  refine le_antisymm (dist_smul_le 𝒯 g x y) ?_
  have := dist_smul_le 𝒯 g⁻¹ (g • x) (g • y)
  rwa [inv_smul_smul, inv_smul_smul] at this

end CerednikDrinfeld.Mumford.Isom

theorem solution
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W)
    [CerednikDrinfeld.Mumford.GraphAction G 𝒯] (g : G) (x y : W) :
    𝒯.dist (g • x) (g • y) = 𝒯.dist x y :=
  CerednikDrinfeld.Mumford.Isom.main 𝒯 g x y
