import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Ideal_eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Ideal_eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

theorem Ideal.eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq
    {W W' : Type*} [CommRing W] [CommRing W'] [Algebra W W']
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
    (hinv : ∀ w' : W', (∀ γ : Γ, γ • w' = w') → w' ∈ Set.range (algebraMap W W'))
    {n : ℕ} (x y : Fin n → W') (hxy : ∀ γ : Γ, ∑ i, x i * γ • y i = if γ = 1 then 1 else 0)
    (S : Type*) [CommRing S] [Algebra W S]
    (J' : Ideal (S ⊗[W] W'))
    (hstab : ∀ γ : Γ, J'.map (Algebra.TensorProduct.map (AlgHom.id S S) (MulSemiringAction.toAlgHom W W' γ)) = J') :
    J' = (J'.comap (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[W] W')).map
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[W] W') := by exact @_root_.P2MW.S_Ideal_eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq.solution W W' _ _ _ Γ _ _ _ _ _ hinv n x y hxy S _ _ J' hstab
