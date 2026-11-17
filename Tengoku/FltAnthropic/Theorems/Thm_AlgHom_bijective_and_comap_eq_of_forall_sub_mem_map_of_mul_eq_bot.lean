import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgHom_bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgHom_bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u
/--
@isnad1 id=and.2h4v.s8.8e987805ddef from=translated src=- shape=ef25435a vocab=e79c0196
-/
theorem AlgHom.bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot
    {T' : Type u} [CommRing T'] (I : Ideal T') (hI2 : I * I = ⊥)
    (C : Type u) [CommRing C] [Algebra T' C]
    (ψ : C →ₐ[T'] C) (hψ : ∀ c : C, ψ c - c ∈ I.map (algebraMap T' C)) :
    Function.Bijective ψ ∧ ∀ p : PrimeSpectrum C, PrimeSpectrum.comap ψ.toRingHom p = p := by exact @_root_.P2MW.S_AlgHom_bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot.solution T' _ I hI2 C _ _ ψ hψ
