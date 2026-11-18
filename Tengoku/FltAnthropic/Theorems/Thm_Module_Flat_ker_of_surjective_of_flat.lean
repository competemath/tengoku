import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_Flat_ker_of_surjective_of_flat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_Flat_ker_of_surjective_of_flat.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open TensorProduct

/--
@isnad1 id=flat.1h4v.s8.627b6bccc69a from=translated src=- shape=9fe60d0f vocab=25293bb2
-/
theorem Module.Flat.ker_of_surjective_of_flat
    {R : Type u} [CommRing R] {M P : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [Module.Flat R M] [Module.Flat R P] (g : M →ₗ[R] P) (hg : Function.Surjective g) :
    Module.Flat R (LinearMap.ker g) := by exact @_root_.P2MW.S_Module_Flat_ker_of_surjective_of_flat.solution R _ M P _ _ _ _ _ _ g hg
