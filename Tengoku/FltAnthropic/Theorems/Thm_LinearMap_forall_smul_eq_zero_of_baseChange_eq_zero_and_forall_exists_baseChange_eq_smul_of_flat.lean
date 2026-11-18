import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v w w'

open TensorProduct

/--
@isnad1 id=and.2h6v.s11.20bc32a73ec8 from=translated src=- shape=946615c5 vocab=4a3f4749
-/
theorem LinearMap.forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat
    {R₀ : Type u} [CommRing R₀] {R : Type v} [CommRing R] [Algebra R₀ R] [Module.Flat R₀ R]
    {M : Type w} [AddCommGroup M] [Module R₀ M] {N : Type w'} [AddCommGroup N] [Module R₀ N]
    (u : M →ₗ[R₀] N) (J : Ideal R₀)
    (hk : ∀ x : M, u x = 0 → ∀ a ∈ J, a • x = 0)
    (hc : ∀ (y : N), ∀ a ∈ J, ∃ x : M, u x = a • y) :
    (∀ x : R ⊗[R₀] M, u.baseChange R x = 0 → ∀ a ∈ J.map (algebraMap R₀ R), a • x = 0) ∧
    (∀ (y : R ⊗[R₀] N), ∀ a ∈ J.map (algebraMap R₀ R), ∃ x : R ⊗[R₀] M, u.baseChange R x = a • y) := by exact @_root_.P2MW.S_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat.solution R₀ _ R _ _ _ M _ _ N _ _ u J hk hc
