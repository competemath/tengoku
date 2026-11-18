import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AdicCompletion_map_ker_subtype_injective_and_range_eq_ker_map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AdicCompletion_map_ker_subtype_injective_and_range_eq_ker_map.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

/--
@isnad1 id=and.0h5v.s14.ba976ff21957 from=translated src=- shape=1c098671 vocab=13597d9e
-/
theorem AdicCompletion.map_ker_subtype_injective_and_range_eq_ker_map
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] (ρ : M →ₗ[R] N) :
    Function.Injective (AdicCompletion.map I (LinearMap.ker ρ).subtype) ∧
      LinearMap.range (AdicCompletion.map I (LinearMap.ker ρ).subtype) =
        LinearMap.ker (AdicCompletion.map I ρ) := by exact @_root_.P2MW.S_AdicCompletion_map_ker_subtype_injective_and_range_eq_ker_map.solution R _ _ I M N _ _ _ _ _ _ ρ
