import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v w

theorem Algebra.Etale.algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (E : Type v) [CommRing E] [Algebra R E] [Module.Finite R E] [Algebra.Etale R E]
    (B : Type w) [CommRing B] [Algebra R B] [Module.Finite R B]
    (φ ψ : E →ₐ[R] B)
    (h : ∀ x : E, φ x - ψ x ∈ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) :
    φ = ψ := by exact @_root_.P2MW.S_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing.solution R _ _ E _ _ _ _ B _ _ _ φ ψ h
