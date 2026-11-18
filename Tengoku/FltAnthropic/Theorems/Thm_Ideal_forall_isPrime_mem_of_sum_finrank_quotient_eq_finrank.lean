import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Ideal_forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Ideal_forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Ideal.forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank
    (F R : Type) [Field F] [CommRing R] [Algebra F R] [Module.Finite F R] [IsReduced R]
    (S : Finset (Ideal R)) (hS : ∀ 𝔭 ∈ S, 𝔭.IsPrime)
    (hsum : ∑ 𝔭 ∈ S, Module.finrank F (R ⧸ 𝔭) = Module.finrank F R) :
    ∀ 𝔭 : Ideal R, 𝔭.IsPrime → 𝔭 ∈ S := by exact @_root_.P2MW.S_Ideal_forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank.solution F R _ _ _ _ _ S hS hsum
