import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualMap
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualInstances
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_isReduced_cartierDual_of_isReduced_cartierDual_baseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_isReduced_cartierDual_of_isReduced_cartierDual_baseChange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.isReduced_cartierDual_of_isReduced_cartierDual_baseChange
    (K : Type) [Field K] (A : Type) [CommRing A] [HopfAlgebra K A] [Coalgebra.IsCocomm K A]
    [Module.Finite K A] [Module.Free K A]
    (L : Type) [Field L] [Algebra K L]
    (hL : IsReduced (CartierDual L (L ⊗[K] A))) :
    IsReduced (CartierDual K A) := by exact @_root_.P2MW.S_HopfAlgebra_isReduced_cartierDual_of_isReduced_cartierDual_baseChange.solution K _ A _ _ _ _ _ L _ _ hL
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
