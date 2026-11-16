import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Ideal_exists_mem_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_eq_span_singleton

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Ideal_exists_mem_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_eq_span_singleton.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Ideal.exists_mem_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_eq_span_singleton
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]
    (I : Ideal R) (π : S) (hI : I.map (algebraMap R S) = Ideal.span {π}) (hπ : π ∈ nonZeroDivisors S) :
    ∃ g ∈ I, I.map (algebraMap R S) = Ideal.span {algebraMap R S g} ∧ algebraMap R S g ∈ nonZeroDivisors S := by exact @_root_.P2MW.S_Ideal_exists_mem_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_eq_span_singleton.solution R S _ _ _ _ I π hI hπ
