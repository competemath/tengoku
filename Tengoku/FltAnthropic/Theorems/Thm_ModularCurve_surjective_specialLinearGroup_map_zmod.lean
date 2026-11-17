import Tengoku.Seed.LinearAlgebra.Matrix.SpecialLinearGroup
import Tengoku.Seed.Data.ZMod.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_surjective_specialLinearGroup_map_zmod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_surjective_specialLinearGroup_map_zmod.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=surjecti.0h1v.s9.a9276878e40b from=translated src=- shape=f709f38e vocab=1944a2b7
-/
theorem ModularCurve.surjective_specialLinearGroup_map_zmod (N : ℕ) [NeZero N] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by exact @_root_.P2MW.S_ModularCurve_surjective_specialLinearGroup_map_zmod.solution N _
