import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural
    (R : Type u) [CommRing R]
    (K₀ K₁ : Type u) [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Free R K₀]
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Free R K₁]
    (d : K₀ →ₗ[R] K₁) :
    ∃ e : ∀ (B : Type u) [AddCommGroup B] [Module R B],
        ((Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) →ₗ[R] B) ≃ₗ[R] LinearMap.ker (d.lTensor B),
      (∀ (B B' : Type u) [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B'] (u : B →ₗ[R] B')
          (g : (Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) →ₗ[R] B),
          ((e B' (u ∘ₗ g) : LinearMap.ker (d.lTensor B')) : B' ⊗[R] K₀) =
            u.rTensor K₀ ((e B g : LinearMap.ker (d.lTensor B)) : B ⊗[R] K₀)) ∧
      (∀ (B : Type u) [AddCommGroup B] [Module R B] (t : LinearMap.ker (d.lTensor B)) (φ : Module.Dual R K₀),
          (e B).symm t (Submodule.Quotient.mk φ) = TensorProduct.rid R B (φ.lTensor B (t : B ⊗[R] K₀))) := by exact @_root_.P2MW.S_Module_exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural.solution R _ K₀ K₁ _ _ _ _ _ _ _ _ d
