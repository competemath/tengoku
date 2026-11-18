import Tengoku.Seed.LinearAlgebra.UnitaryGroup
import Tengoku.Seed.Topology.Algebra.ContinuousMonoidHom
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel

/--
@isnad1 id=ex.1h2v.s13.bfbf79e72c32 from=translated src=- shape=24ce2543 vocab=ba73f451
-/
theorem AutomorphicForm.exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal
    (F : Type) [Field F] (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ e : ↥(rowIsometrySubgroup w.Completion) ≃ₜ* ↥(Matrix.orthogonalGroup (Fin 2) ℝ),
      ∀ (k : ↥(rowIsometrySubgroup w.Completion)) (i j : Fin 2),
        ((e k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j
          = extensionEmbeddingOfIsReal hw
              (((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) := by exact @_root_.P2MW.S_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal.solution F _ w hw
