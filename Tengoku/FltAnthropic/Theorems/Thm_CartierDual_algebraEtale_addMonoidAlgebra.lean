import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualInstances
import Tengoku.FltAnthropic.P2M.Sol.S_CartierDual_algebraEtale_addMonoidAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CartierDual_algebraEtale_addMonoidAlgebra.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
universe u v

/--
@isnad1 id=etale.0h2v.s7.96c32d931308 from=translated src=- shape=a920673e vocab=b12ac5eb
-/
theorem Tengoku.FltAnthropic.CartierDual.algebraEtale_addMonoidAlgebra
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Finite M] :
    Algebra.Etale R (CartierDual R (AddMonoidAlgebra R M)) := by exact @_root_.P2MW.S_CartierDual_algebraEtale_addMonoidAlgebra.solution R _ M _ _
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
