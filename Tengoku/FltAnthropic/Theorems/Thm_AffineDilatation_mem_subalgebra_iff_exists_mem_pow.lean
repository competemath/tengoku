import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_RingTheory_AffineDilatation
import Tengoku.FltAnthropic.P2M.Sol.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AffineDilatation_mem_subalgebra_iff_exists_mem_pow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

theorem AffineDilatation.mem_subalgebra_iff_exists_mem_pow
    {A : Type u} [CommRing A] (I : Ideal A) (a : A) (ha : a ∈ I) (x : Localization.Away a) :
    x ∈ AffineDilatation.subalgebra I a ↔
      ∃ (n : ℕ) (g : A), g ∈ I ^ n ∧
        IsLocalization.mk' (Localization.Away a) g (⟨a ^ n, n, rfl⟩ : Submonoid.powers a) = x := by exact @_root_.P2MW.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow.solution A _ I a ha x
