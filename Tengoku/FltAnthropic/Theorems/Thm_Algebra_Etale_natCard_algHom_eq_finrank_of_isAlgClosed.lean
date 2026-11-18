import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.0h2v.s6.63eb8cd87179 from=translated src=- shape=31007b4a vocab=1bea3fe5
-/
theorem Algebra.Etale.natCard_algHom_eq_finrank_of_isAlgClosed
    (k : Type*) [Field k] [IsAlgClosed k] (R : Type*) [CommRing R] [Algebra k R] [Algebra.Etale k R] :
    Nat.card (R →ₐ[k] k) = Module.finrank k R := by exact @_root_.P2MW.S_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed.solution k _ _ R _ _ _
