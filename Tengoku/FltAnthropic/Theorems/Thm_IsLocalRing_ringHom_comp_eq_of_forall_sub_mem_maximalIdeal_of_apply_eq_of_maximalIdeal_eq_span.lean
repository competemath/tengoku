import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IsLocalRing

/--
@isnad1 id=eq.3h5v.s8.cc4f4c368cfe from=translated src=- shape=17d385d8 vocab=f142f4f4
-/
theorem IsLocalRing.ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : maximalIdeal W = Ideal.span {ϖ})
    (R : Type) [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [Finite (ResidueField R)]
    (κ : W →+* R) [IsLocalHom κ]
    (θ : R →+* R) (hres : ∀ r : R, θ r - r ∈ maximalIdeal R) (hfix : θ (κ ϖ) = κ ϖ) :
    θ.comp κ = κ := by exact @_root_.P2MW.S_IsLocalRing_ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span.solution W _ _ _ _ ϖ hϖ R _ _ _ _ κ _ θ hres hfix
