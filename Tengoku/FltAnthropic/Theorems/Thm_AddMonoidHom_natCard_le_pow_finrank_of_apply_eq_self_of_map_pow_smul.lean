import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AddMonoidHom_natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AddMonoidHom_natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=and.4h8v.s10.4cd2c40fba3e from=translated src=- shape=f673d670 vocab=a88a22a3
-/
theorem AddMonoidHom.natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul
    {K F M : Type*} [Field K] [Field F] [Algebra K F] [AddCommGroup M] [Module F M]
    [Module K M] [IsScalarTower K F M]
    (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (C : M →+ M) (hsemi : ∀ (f : F) (m : M), C (f ^ p • m) = f • C m)
    (W : Submodule K M) [FiniteDimensional K W]
    {G : Type*} [AddCommGroup G] (φ : G →+ M) (hφ : Function.Injective φ)
    (hfix : ∀ g : G, C (φ g) = φ g) (hW : ∀ g : G, φ g ∈ W) :
    Finite G ∧ Nat.card G ≤ p ^ Module.finrank K W := by exact @_root_.P2MW.S_AddMonoidHom_natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul.solution K F M _ _ _ _ _ _ _ p _ _ _ C hsemi W _ G _ φ hφ hfix hW
