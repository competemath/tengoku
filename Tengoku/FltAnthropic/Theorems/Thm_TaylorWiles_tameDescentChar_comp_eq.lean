import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Deformations_TameDescent
import Tengoku.FltAnthropic.P2M.Sol.S_TaylorWiles_tameDescentChar_comp_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_TaylorWiles_tameDescentChar_comp_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v w

open Function
/--
@isnad1 id=eq.2h6v.s9.7f4dc6db4760 from=translated src=- shape=47879318 vocab=7ccbcbbf
-/
theorem TaylorWiles.tameDescentChar_comp_eq {G : Type u} {Δ : Type v} {A : Type w} [Group G] [Group Δ] [CommRing A]
    (π : G →* Δ) (hπ : Function.Surjective π) (χ : G →* Aˣ)
    (hχ : ∀ g ∈ π.ker, χ g = 1) (g : G) :
    TaylorWiles.tameDescentChar π hπ χ hχ (π g) = χ g := by exact @_root_.P2MW.S_TaylorWiles_tameDescentChar_comp_eq.solution G Δ A _ _ _ π hπ χ hχ g
