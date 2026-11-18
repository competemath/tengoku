import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

theorem _root_.Tengoku.FltAnthropic.iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : Convex ℝ s) (hs' : (interior s).Nonempty)
    {n : ℕ} {f : E → F} (hf : ContDiffOn ℝ n f s) {x : E} (hx : x ∈ s)
    (σ : Equiv.Perm (Fin n)) (v : Fin n → E) :
    iteratedFDerivWithin ℝ n f s x (v ∘ σ) = iteratedFDerivWithin ℝ n f s x v := by exact @_root_.P2MW.S_iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex.solution E _ _ F _ _ s hs hs' n f hf x hx σ v
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
