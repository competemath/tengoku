import Tengoku.FltAnthropic.Definitions.Def_LatticeTreeBaseChange
import Tengoku.FltAnthropic.P2M.Sol.S_LT_LatticeTree_Vertex_isWithin_add_of_isWithin_of_isWithin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LT_LatticeTree_Vertex_isWithin_add_of_isWithin_of_isWithin.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=iswithin.3h8v.s7.92a3ca957f12 from=translated src=- shape=e42fbc22 vocab=94084d32
-/
theorem LT.LatticeTree.Vertex.isWithin_add_of_isWithin_of_isWithin
    (R K : Type) [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (v w x : LT.LatticeTree.Vertex R K) (n m : ℕ)
    (h₁ : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v w)
    (h₂ : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) m w x) :
    LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + m) v x := by exact @_root_.P2MW.S_LT_LatticeTree_Vertex_isWithin_add_of_isWithin_of_isWithin.solution R K _ _ _ _ ϖ hϖ v w x n m h₁ h₂
