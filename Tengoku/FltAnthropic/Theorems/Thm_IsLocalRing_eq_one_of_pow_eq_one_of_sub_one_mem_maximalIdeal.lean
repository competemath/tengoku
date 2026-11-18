import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open IsLocalRing
theorem IsLocalRing.eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal {A : Type u} [CommRing A] [IsLocalRing A]
    {u : A} (hu : u - 1 ∈ IsLocalRing.maximalIdeal A) {n : ℕ} (hn : IsUnit (n : A)) (hun : u ^ n = 1) : u = 1 := by exact @_root_.P2MW.S_IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal.solution A _ _ u hu n hn hun
