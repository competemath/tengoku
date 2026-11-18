import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IsLocalRing in

/--
@isnad1 id=etale.1h4v.s9.1e32f94e6b44 from=translated src=- shape=d95db035 vocab=74b7b39a
-/
theorem IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete
    {O C : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O]
    [IsAdicComplete (maximalIdeal O) O]
    [CommRing C] [IsDomain C] [IsLocalRing C] [IsAdicComplete (maximalIdeal C) C]
    [Algebra O C] [Module.Finite O C] [FaithfulSMul O C] [IsLocalHom (algebraMap O C)]
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra O K₁] [IsFractionRing O K₁]
    [Algebra C K] [IsFractionRing C K] [Algebra K₁ K] [Algebra O K]
    [IsScalarTower O C K] [IsScalarTower O K₁ K]
    [Algebra.IsSeparable (ResidueField O) (ResidueField C)]
    (hcount : Module.finrank K₁ K = Module.finrank (ResidueField O) (ResidueField C)) :
    Algebra.Etale O C := by exact @_root_.P2MW.S_IsLocalRing_etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete.solution O C _ _ _ _ _ _ _ _ _ _ _ _ _ K₁ K _ _ _ _ _ _ _ _ _ _ _ hcount
