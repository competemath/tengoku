import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.P2M.Sol.S_CartierDual_exists_bialgEquiv_bidual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CartierDual_exists_bialgEquiv_bidual.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
theorem Tengoku.FltAnthropic.CartierDual.exists_bialgEquiv_bidual
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A] :
    ∃ e : A ≃ₐc[R] CartierDual R (CartierDual R A), ∀ (a : A) (φ : CartierDual R A), e a φ = φ a := by exact @_root_.P2MW.S_CartierDual_exists_bialgEquiv_bidual.solution R _ A _ _ _ _ _
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
