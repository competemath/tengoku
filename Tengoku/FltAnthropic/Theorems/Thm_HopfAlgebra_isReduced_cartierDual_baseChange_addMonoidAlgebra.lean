import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualMap
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualInstances
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_isReduced_cartierDual_baseChange_addMonoidAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_isReduced_cartierDual_baseChange_addMonoidAlgebra.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.isReduced_cartierDual_baseChange_addMonoidAlgebra
    (R : Type) [CommRing R] (L : Type) [Field L] [Algebra R L]
    (Γ : Type) [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ] :
    IsReduced (CartierDual L (L ⊗[R] AddMonoidAlgebra R Γ)) := by exact @_root_.P2MW.S_HopfAlgebra_isReduced_cartierDual_baseChange_addMonoidAlgebra.solution R _ L _ _ Γ _ _ _
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
