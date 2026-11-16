import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=etale.0h4v.s6.6e4e588446d7 from=translated src=- shape=4470ed55 vocab=13d1c9ae
-/
theorem Algebra.Etale.of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension n R T]
    [Algebra.FormallyUnramified S T] :
    Algebra.Etale S T := by exact @_root_.P2MW.S_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension.solution R S T _ _ _ _ _ _ _ n _ _ _
