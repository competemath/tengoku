import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_FGSubalgebra
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/--
@isnad1 id=nonempty.0h2v.s6.97f6d210b7e4 from=translated src=- shape=44e94ced vocab=56dabcd3
-/
theorem AlgebraicGeometry.FGSubalgebra.nonempty_isColimit_cocone
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    Nonempty (IsColimit (FGSubalgebra.cocone R A)) := by exact @_root_.P2MW.S_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone.solution R _ A _ _
