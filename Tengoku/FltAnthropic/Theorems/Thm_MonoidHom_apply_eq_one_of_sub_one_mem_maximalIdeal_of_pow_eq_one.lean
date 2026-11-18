import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u w

open IsLocalRing
theorem MonoidHom.apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one {G : Type u} {A : Type w} [Group G] [CommRing A] [IsLocalRing A]
    (χ : G →* Aˣ) (g : G) (hprin : (χ g : A) - 1 ∈ IsLocalRing.maximalIdeal A)
    {n : ℕ} (hn : IsUnit (n : A)) (hgn : g ^ n = 1) : χ g = 1 := by exact @_root_.P2MW.S_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one.solution G A _ _ _ χ g hprin n hn hgn
