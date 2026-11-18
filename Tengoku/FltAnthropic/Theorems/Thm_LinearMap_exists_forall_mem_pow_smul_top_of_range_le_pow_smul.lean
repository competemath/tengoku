import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_forall_mem_pow_smul_top_of_range_le_pow_smul
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N] :
    ∃ c : ℕ, ∀ (n : ℕ) (g : M →ₗ[B] N),
      LinearMap.range g ≤ I ^ (n + c) • (⊤ : Submodule B N) →
      g ∈ I ^ n • (⊤ : Submodule B (M →ₗ[B] N)) := by exact @_root_.P2MW.S_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul.solution B _ _ I M _ _ _ N _ _ _
