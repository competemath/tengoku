import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_FormallyEtale_of_formallySmooth_of_bijective_mapBaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_FormallyEtale_of_formallySmooth_of_bijective_mapBaseChange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=formally.1h3v.s9.46e143375364 from=translated src=- shape=c1e35f2c vocab=075dd1bf
-/
theorem Algebra.FormallyEtale.of_formallySmooth_of_bijective_mapBaseChange
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallySmooth R T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by exact @_root_.P2MW.S_Algebra_FormallyEtale_of_formallySmooth_of_bijective_mapBaseChange.solution R S T _ _ _ _ _ _ _ _ h
