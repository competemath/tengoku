import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

/--
@isnad1 id=eq.0h3v.s6.16c0bf7cd504 from=translated src=- shape=59cf8c71 vocab=fec76491
-/
theorem Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
    (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (P : Ideal A) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) = ringKrullDim A := by exact @_root_.P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.solution k _ A _ _ _ _ P _
