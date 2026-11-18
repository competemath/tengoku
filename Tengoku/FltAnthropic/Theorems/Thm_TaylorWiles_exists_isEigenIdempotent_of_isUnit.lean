import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Deformations_LocalSplitting
import Tengoku.FltAnthropic.P2M.Sol.S_TaylorWiles_exists_isEigenIdempotent_of_isUnit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_TaylorWiles_exists_isEigenIdempotent_of_isUnit.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open Matrix
/--
@isnad1 id=ex.3h4v.s7.73aac756175f from=translated src=- shape=3b3939e3 vocab=0da02831
-/
theorem TaylorWiles.exists_isEigenIdempotent_of_isUnit {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A} {a b : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) (hu : IsUnit (a - b)) :
    ∃ e, TaylorWiles.IsEigenIdempotent M a b e := by exact @_root_.P2MW.S_TaylorWiles_exists_isEigenIdempotent_of_isUnit.solution A _ M a b htr hdet hu
