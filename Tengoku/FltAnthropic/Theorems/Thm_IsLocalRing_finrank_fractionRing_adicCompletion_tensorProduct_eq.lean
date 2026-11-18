import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_finrank_fractionRing_adicCompletion_tensorProduct_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_finrank_fractionRing_adicCompletion_tensorProduct_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open IsLocalRing in
open scoped TensorProduct in

theorem IsLocalRing.finrank_fractionRing_adicCompletion_tensorProduct_eq
    {O : Type u} {C : Type v} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsLocalRing O]
    [CommRing C] [IsDomain C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra O K₁] [IsFractionRing O K₁]
    [Algebra C K] [IsFractionRing C K] [Algebra K₁ K] [Algebra O K]
    [IsScalarTower O C K] [IsScalarTower O K₁ K]
    [IsDomain (AdicCompletion (maximalIdeal O) O)] [IsDomain ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)]
    (L M : Type*) [Field L] [Field M]
    [Algebra (AdicCompletion (maximalIdeal O) O) L] [IsFractionRing (AdicCompletion (maximalIdeal O) O) L]
    [Algebra ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) M] [IsFractionRing ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) M]
    [Algebra L M] [Algebra (AdicCompletion (maximalIdeal O) O) M]
    [IsScalarTower (AdicCompletion (maximalIdeal O) O) ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) M]
    [IsScalarTower (AdicCompletion (maximalIdeal O) O) L M] :
    Module.finrank L M = Module.finrank K₁ K := by exact @_root_.P2MW.S_IsLocalRing_finrank_fractionRing_adicCompletion_tensorProduct_eq.solution O C _ _ _ _ _ _ _ _ _ K₁ K _ _ _ _ _ _ _ _ _ _ _ _ L M _ _ _ _ _ _ _ _ _ _
