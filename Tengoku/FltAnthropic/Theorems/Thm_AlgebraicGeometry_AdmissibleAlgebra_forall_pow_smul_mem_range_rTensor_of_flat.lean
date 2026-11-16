import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_AdmissibleAlgebra_forall_pow_smul_mem_range_rTensor_of_flat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_AdmissibleAlgebra_forall_pow_smul_mem_range_rTensor_of_flat.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open TensorProduct

universe u v w

theorem AlgebraicGeometry.AdmissibleAlgebra.forall_pow_smul_mem_range_rTensor_of_flat
    {B : Type u} [CommRing B] {M N P : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    [AddCommGroup P] [Module B P] (f : M →ₗ[B] N) (g : N →ₗ[B] P) (hfg : g.comp f = 0) (t : B) (e : ℕ)
    (h : ∀ n : N, g n = 0 → (∃ k : ℕ, t ^ k • n ∈ LinearMap.range f) → t ^ e • n ∈ LinearMap.range f)
    (S : Type v) [AddCommGroup S] [Module B S] [Module.Flat B S]
    (n : N ⊗[B] S) (hn : LinearMap.rTensor S g n = 0) (hk : ∃ k : ℕ, t ^ k • n ∈ LinearMap.range (LinearMap.rTensor S f)) :
    t ^ e • n ∈ LinearMap.range (LinearMap.rTensor S f) := by exact @_root_.P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_forall_pow_smul_mem_range_rTensor_of_flat.solution B _ M N P _ _ _ _ _ _ f g hfg t e h S _ _ _ n hn hk
