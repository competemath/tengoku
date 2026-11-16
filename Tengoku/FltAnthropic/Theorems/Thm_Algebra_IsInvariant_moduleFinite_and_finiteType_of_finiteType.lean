import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=and.0h4v.s7.a5e06cd02d8b from=translated src=- shape=1555dc3d vocab=c0f5249e
-/
theorem Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (A : Type*) [CommRing A] [Algebra R A]
    (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [FaithfulSMul A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
    [Algebra.FiniteType R B] :
    Module.Finite A B ∧ Algebra.FiniteType R A := by exact @_root_.P2MW.S_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType.solution R _ _ A _ _ B _ _ _ _ _ G _ _ _ _ _
