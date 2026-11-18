import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct in

theorem IsLocalRing.etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField
    {O C : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsLocalRing O]
    [CommRing C] [IsDomain C] [IsNoetherianRing C] [IsLocalRing C]
    [Algebra O C] [Module.Finite O C] [FaithfulSMul O C] [IsLocalHom (algebraMap O C)]
    (hO : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal O) O) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal O) O))
    (hC : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal C) C))
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra O K₁] [IsFractionRing O K₁]
    [Algebra C K] [IsFractionRing C K] [Algebra K₁ K] [Algebra O K]
    [IsScalarTower O C K] [IsScalarTower O K₁ K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField C)]
    (hcount : Module.finrank K₁ K =
      Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField C)) :
    Algebra.Etale (AdicCompletion (IsLocalRing.maximalIdeal O) O)
      ((AdicCompletion (IsLocalRing.maximalIdeal O) O) ⊗[O] C) := by exact @_root_.P2MW.S_IsLocalRing_etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField.solution O C _ _ _ _ _ _ _ _ _ _ _ _ hO hC K₁ K _ _ _ _ _ _ _ _ _ _ _ hcount
