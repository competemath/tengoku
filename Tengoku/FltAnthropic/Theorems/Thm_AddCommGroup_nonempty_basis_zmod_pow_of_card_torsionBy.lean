import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AddCommGroup_nonempty_basis_zmod_pow_of_card_torsionBy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AddCommGroup_nonempty_basis_zmod_pow_of_card_torsionBy.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem AddCommGroup.nonempty_basis_zmod_pow_of_card_torsionBy (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] (r m : ℕ)
    (hcard : ∀ j ≤ m, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
    {V : Type*} [AddCommGroup V] [Module (ZMod (ℓ ^ m)) V]
    (ι : V →+ M) (hι : Function.Injective ι)
    (hιr : ∀ x : M, x ∈ ι.range ↔ ((ℓ ^ m : ℕ) : ℤ) • x = 0) :
    Nonempty (Module.Basis (Fin r) (ZMod (ℓ ^ m)) V) := by exact @_root_.P2MW.S_AddCommGroup_nonempty_basis_zmod_pow_of_card_torsionBy.solution ℓ _ M _ r m hcard V _ _ ι hι hιr
