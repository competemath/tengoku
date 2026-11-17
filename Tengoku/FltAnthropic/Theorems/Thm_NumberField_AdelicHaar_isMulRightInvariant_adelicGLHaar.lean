import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicHaar
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel

/--
@isnad1 id=ismulrig.0h1v.s8.0571911e1a8f from=translated src=- shape=2c8b62bd vocab=d869842f
-/
theorem NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar (F : Type) [Field F] [NumberField F] :
    (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant := by exact @_root_.P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar.solution F _ _
