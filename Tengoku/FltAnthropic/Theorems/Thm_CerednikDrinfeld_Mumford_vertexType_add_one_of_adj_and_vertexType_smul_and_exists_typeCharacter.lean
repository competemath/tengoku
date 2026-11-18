import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hc : 𝒯.Connected) (hb : 𝒯.Colorable 2) (w₀ : W) :
    (∀ x y : W, 𝒯.Adj x y → vertexType 𝒯 w₀ y = vertexType 𝒯 w₀ x + 1) ∧
    (∀ (g : G) (w : W), vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ (g • w₀) + vertexType 𝒯 w₀ w) ∧
    (∃ ε : G →* Multiplicative (ZMod 2),
      (∀ g : G, Multiplicative.toAdd (ε g) = vertexType 𝒯 w₀ (g • w₀)) ∧ ε.ker = typePreserving G 𝒯 w₀) := by exact @_root_.P2MW.S_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter.solution G _ W _ 𝒯 _ hc hb w₀
