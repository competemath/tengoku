import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Submodule_exists_smul_eq_self_and_smul_mem_torsionBySet_of_torsionBySet_pow_succ_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Submodule_exists_smul_eq_self_and_smul_mem_torsionBySet_of_torsionBySet_pow_succ_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Submodule.exists_smul_eq_self_and_smul_mem_torsionBySet_of_torsionBySet_pow_succ_eq
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite M]
    (I : Ideal R) (N : ℕ)
    (hN : Submodule.torsionBySet R M (↑(I ^ (N + 1)) : Set R) = Submodule.torsionBySet R M (↑(I ^ N) : Set R)) :
    ∃ t : R, (∀ v ∈ Submodule.torsionBySet R M (↑(I ^ N) : Set R), t • v = v) ∧
      ∀ m : M, t • m ∈ Submodule.torsionBySet R M (↑(I ^ N) : Set R) := by exact @_root_.P2MW.S_Submodule_exists_smul_eq_self_and_smul_mem_torsionBySet_of_torsionBySet_pow_succ_eq.solution R M _ _ _ _ I N hN
