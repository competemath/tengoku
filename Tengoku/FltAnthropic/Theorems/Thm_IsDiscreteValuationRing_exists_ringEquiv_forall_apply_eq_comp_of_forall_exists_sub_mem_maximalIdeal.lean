import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsDiscreteValuationRing_exists_ringEquiv_forall_apply_eq_comp_of_forall_exists_sub_mem_maximalIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsDiscreteValuationRing_exists_ringEquiv_forall_apply_eq_comp_of_forall_exists_sub_mem_maximalIdeal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IsLocalRing

/--
@isnad1 id=ex.8h10v.s10.c95f2ff7104b from=translated src=- shape=bfab8aea vocab=02054c62
-/
theorem IsDiscreteValuationRing.exists_ringEquiv_forall_apply_eq_comp_of_forall_exists_sub_mem_maximalIdeal
    (A W₀ W S : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀] [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    [CommRing S] (I : Ideal S) [IsHausdorff I S]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (σ₀ : A →+* W₀) (hσ₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {σ₀ ϖ})
    (hres₀ : ∀ w : W₀, ∃ a : A, w - σ₀ a ∈ IsLocalRing.maximalIdeal W₀)
    (σ : A →+* W) (hσ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
    (hres : ∀ w : W, ∃ a : A, w - σ a ∈ IsLocalRing.maximalIdeal W)
    (C₀ : W₀ →+* S) (C : W →+* S)
    (hC₀ : ∀ w ∈ IsLocalRing.maximalIdeal W₀, C₀ w ∈ I) (hC : ∀ w ∈ IsLocalRing.maximalIdeal W, C w ∈ I)
    (h : ∀ a : A, C₀ (σ₀ a) = C (σ a)) :
    ∃ βW : W₀ ≃+* W, (∀ w : W₀, C₀ w = C (βW w)) ∧ (∀ a : A, βW (σ₀ a) = σ a) := by exact @_root_.P2MW.S_IsDiscreteValuationRing_exists_ringEquiv_forall_apply_eq_comp_of_forall_exists_sub_mem_maximalIdeal.solution A W₀ W S _ _ _ _ _ _ _ _ _ _ _ _ I _ ϖ hϖ σ₀ hσ₀ hres₀ σ hσ hres C₀ C hC₀ hC h
