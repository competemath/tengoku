import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Mumford_fg_of_finite_stabilizer_of_finite_quotVert_of_finite_quotEdge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Mumford_fg_of_finite_stabilizer_of_finite_quotVert_of_finite_quotEdge.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.fg_of_finite_stabilizer_of_finite_quotVert_of_finite_quotEdge
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hconn : 𝒯.Connected)
    (hstab : ∀ w : W, Finite (MulAction.stabilizer G w))
    (hV : Finite (QuotVert G W)) (hE : Finite (QuotEdge G 𝒯)) :
    Group.FG G := by exact @_root_.P2MW.S_CerednikDrinfeld_Mumford_fg_of_finite_stabilizer_of_finite_quotVert_of_finite_quotEdge.solution G _ W _ 𝒯 _ hconn hstab hV hE
