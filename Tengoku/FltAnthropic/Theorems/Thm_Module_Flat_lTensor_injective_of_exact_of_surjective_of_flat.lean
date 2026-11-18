import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat
    {R : Type u} [CommRing R] {N M P : Type u}
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Flat R P]
    (A : Type u) [AddCommGroup A] [Module R A] :
    Function.Injective (f.lTensor A) := by exact @_root_.P2MW.S_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat.solution R _ N M P _ _ _ _ _ _ f g hf hfg hg _ A _ _
