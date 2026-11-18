import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_Place_exists_sub_algebraMap_mem_nonunits_of_isAlgClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_Place_exists_sub_algebraMap_mem_nonunits_of_isAlgClosed.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open AlgebraicCurve
open scoped Pointwise

theorem AlgebraicCurve.Place.exists_sub_algebraMap_mem_nonunits_of_isAlgClosed
    {κ' : Type*} [Field κ'] [IsAlgClosed κ'] {F' : Type*} [Field F'] [Algebra κ' F']
    (P' : Place κ' F') [P'.FiniteResidue]
    (x : F') (hx : x ∈ P'.toValuationSubring) :
    ∃ c : κ', x - algebraMap κ' F' c ∈ P'.toValuationSubring.nonunits := by exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_sub_algebraMap_mem_nonunits_of_isAlgClosed.solution κ' _ _ F' _ _ P' _ x hx
