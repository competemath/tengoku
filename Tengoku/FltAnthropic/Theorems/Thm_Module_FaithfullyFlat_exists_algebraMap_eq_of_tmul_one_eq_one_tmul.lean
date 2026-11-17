import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open TensorProduct

/--
@isnad1 id=ex.1h3v.s8.9cb9d2b8d2af from=translated src=- shape=de0ccc05 vocab=4f5e8bb4
-/
theorem Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {b : B} (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) :
    ∃ a : A, algebraMap A B a = b := by exact @_root_.P2MW.S_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul.solution A B _ _ _ _ b hb
