import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_ModpRealization
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualInstances
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_finrank_primitives_cartierDual_eq_finrank_cotangentSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_finrank_primitives_cartierDual_eq_finrank_cotangentSpace.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

universe u v

/--
@isnad1 id=eq.0h2v.s12.4a7b688cd4ce from=translated src=- shape=f8533865 vocab=b65e7d2e
-/
theorem HopfAlgebra.finrank_primitives_cartierDual_eq_finrank_cotangentSpace
    (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
    [Module.Finite k A] :
    Module.finrank k ↥(primitives k (CartierDual k A)) = Module.finrank k (cotangentSpace k A) := by exact @_root_.P2MW.S_HopfAlgebra_finrank_primitives_cartierDual_eq_finrank_cotangentSpace.solution k _ A _ _ _ _
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
