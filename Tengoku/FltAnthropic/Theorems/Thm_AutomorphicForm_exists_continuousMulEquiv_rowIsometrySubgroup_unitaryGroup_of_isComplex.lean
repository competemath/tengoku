import Tengoku.Seed.LinearAlgebra.UnitaryGroup
import Tengoku.Seed.Topology.Algebra.ContinuousMonoidHom
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel

/--
@isnad1 id=ex.1h2v.s13.4373fc78ca40 from=translated src=- shape=03915d8a vocab=7e3661f6
-/
theorem AutomorphicForm.exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex
    (F : Type) [Field F] (w : InfinitePlace F) (_hw : w.IsComplex) :
    ∃ e : ↥(rowIsometrySubgroup w.Completion) ≃ₜ* ↥(Matrix.unitaryGroup (Fin 2) ℂ),
      ∀ (k : ↥(rowIsometrySubgroup w.Completion)) (i j : Fin 2),
        ((e k : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) i j
          = extensionEmbedding w
              (((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) := by exact @_root_.P2MW.S_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex.solution F _ w _hw
