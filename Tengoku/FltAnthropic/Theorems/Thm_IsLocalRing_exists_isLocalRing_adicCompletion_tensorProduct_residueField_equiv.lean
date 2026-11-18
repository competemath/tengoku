import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_exists_isLocalRing_adicCompletion_tensorProduct_residueField_equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_exists_isLocalRing_adicCompletion_tensorProduct_residueField_equiv.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open IsLocalRing in
open scoped TensorProduct in

/--
@isnad1 id=ex.0h2v.s14.21806c078035 from=translated src=- shape=bb198e3c vocab=804937cd
-/
theorem IsLocalRing.exists_isLocalRing_adicCompletion_tensorProduct_residueField_equiv
    {O : Type u} {C : Type v} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
    [Algebra O C] [Module.Finite O C] [IsLocalHom (algebraMap O C)] :
    ∃ (_ : IsLocalRing ((AdicCompletion (maximalIdeal O) O) ⊗[O] C))
      (_ : IsLocalHom (algebraMap (AdicCompletion (maximalIdeal O) O) ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)))
      (e : ResidueField C ≃+* ResidueField ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)),
      IsAdicComplete (maximalIdeal ((AdicCompletion (maximalIdeal O) O) ⊗[O] C))
        ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) ∧
      (IsDomain (AdicCompletion (maximalIdeal C) C) → IsDomain ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)) ∧
      (FaithfulSMul O C → FaithfulSMul (AdicCompletion (maximalIdeal O) O) ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)) ∧
      ∀ c : C, e (residue C c) = residue ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) (1 ⊗ₜ[O] c) := by exact @_root_.P2MW.S_IsLocalRing_exists_isLocalRing_adicCompletion_tensorProduct_residueField_equiv.solution O C _ _ _ _ _ _ _ _ _
