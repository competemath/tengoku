import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsIntegrallyClosed_bijective_algebraMap_of_finrank_eq_finrank_fractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsIntegrallyClosed_bijective_algebraMap_of_finrank_eq_finrank_fractionRing.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=bijectiv.1h5v.s9.70f0af40d70d from=translated src=- shape=6bd68444 vocab=5341b9b2
-/
theorem IsIntegrallyClosed.bijective_algebraMap_of_finrank_eq_finrank_fractionRing
    {O W C : Type*} [CommRing O] [IsDomain O] [CommRing W] [IsDomain W] [IsIntegrallyClosed W]
    [CommRing C] [IsDomain C]
    [Algebra O W] [Module.Finite O W] [Module.Free O W] [FaithfulSMul O W]
    [Algebra O C] [Algebra.IsIntegral O C] [Algebra W C] [IsScalarTower O W C] [FaithfulSMul W C]
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra O K₁] [IsFractionRing O K₁]
    [Algebra C K] [IsFractionRing C K] [Algebra K₁ K] [Algebra O K]
    [IsScalarTower O C K] [IsScalarTower O K₁ K]
    (h : Module.finrank O W = Module.finrank K₁ K) :
    Function.Bijective (algebraMap W C) := by exact @_root_.P2MW.S_IsIntegrallyClosed_bijective_algebraMap_of_finrank_eq_finrank_fractionRing.solution O W C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K₁ K _ _ _ _ _ _ _ _ _ _ h
