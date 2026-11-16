import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

/--
@isnad1 id=isstanda.0h2v.s6.8995eef0a9a1 from=translated src=- shape=23624712 vocab=03071e93
-/
theorem MvPolynomial.isStandardSmoothOfRelativeDimension_natCard
    (S : Type u) [CommRing S] (ι : Type v) [Finite ι] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) S (MvPolynomial ι S) := by exact @_root_.P2MW.S_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard.solution S _ ι _
