import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
open scoped TensorProduct

/--
@isnad1 id=formally.1h2v.s7.1eac94e217dd from=translated src=- shape=b9474670 vocab=349db73c
-/
theorem Algebra.FormallyUnramified.of_residueField_baseChange_of_finite (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (h : Algebra.FormallyUnramified (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S)) :
    Algebra.FormallyUnramified R S := by exact @_root_.P2MW.S_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite.solution R S _ _ _ _ _ h
