import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_formallyUnramified_of_ker_counit_eq_sq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_formallyUnramified_of_ker_counit_eq_sq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

/--
@isnad1 id=formally.1h2v.s8.a3ed1f978c02 from=translated src=- shape=dc223f09 vocab=06a5c3fd
-/
theorem HopfAlgebra.formallyUnramified_of_ker_counit_eq_sq
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    (hI : RingHom.ker (Bialgebra.counitAlgHom R H) = RingHom.ker (Bialgebra.counitAlgHom R H) ^ 2) :
    Algebra.FormallyUnramified R H := by exact @_root_.P2MW.S_HopfAlgebra_formallyUnramified_of_ker_counit_eq_sq.solution R _ H _ _ hI
