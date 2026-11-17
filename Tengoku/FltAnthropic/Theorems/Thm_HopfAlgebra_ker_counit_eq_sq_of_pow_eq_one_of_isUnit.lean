import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_ker_counit_eq_sq_of_pow_eq_one_of_isUnit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_ker_counit_eq_sq_of_pow_eq_one_of_isUnit.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

/--
@isnad1 id=eq.2h3v.s9.422cb48f1a1f from=translated src=- shape=ff261760 vocab=16bbcd21
-/
theorem HopfAlgebra.ker_counit_eq_sq_of_pow_eq_one_of_isUnit
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    (n : ℕ) (hn : IsUnit (n : R))
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ n = 1) :
    RingHom.ker (Bialgebra.counitAlgHom R H) = RingHom.ker (Bialgebra.counitAlgHom R H) ^ 2 := by exact @_root_.P2MW.S_HopfAlgebra_ker_counit_eq_sq_of_pow_eq_one_of_isUnit.solution R _ H _ _ n hn hH
