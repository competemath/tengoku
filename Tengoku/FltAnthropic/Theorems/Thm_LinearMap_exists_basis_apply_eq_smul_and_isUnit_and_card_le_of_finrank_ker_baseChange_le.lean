import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LinearMap_exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LinearMap_exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

/--
@isnad1 id=ex.2h4v.s12.99952dfe5b80 from=translated src=- shape=099e9228 vocab=f941db96
-/
theorem LinearMap.exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (hf : Function.Injective f) (r : ℕ)
    (hker : Module.finrank (IsLocalRing.ResidueField R)
        (LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R))) ≤ r) :
    ∃ (n : ℕ) (b b' : Module.Basis (Fin n) R M) (a : Fin n → R) (s : Finset (Fin n)),
      (∀ i, f (b i) = a i • b' i) ∧ (∀ i ∉ s, IsUnit (a i)) ∧ s.card ≤ r := by exact @_root_.P2MW.S_LinearMap_exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le.solution R _ _ _ _ M _ _ _ _ f hf r hker
