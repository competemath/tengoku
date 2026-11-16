import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AddCommGroup_exists_mem_torsionBy_smul_eq_of_card_torsionBy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AddCommGroup_exists_mem_torsionBy_smul_eq_of_card_torsionBy.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.2h5v.s8.08d6fd69f111 from=translated src=- shape=71cd743a vocab=400e5980
-/
theorem AddCommGroup.exists_mem_torsionBy_smul_eq_of_card_torsionBy (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] (r m : ℕ)
    (hcard : ∀ j ≤ m + 1, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
    (x : M) (hx : x ∈ Submodule.torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ)) :
    ∃ y ∈ Submodule.torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ), ℓ • y = x := by exact @_root_.P2MW.S_AddCommGroup_exists_mem_torsionBy_smul_eq_of_card_torsionBy.solution ℓ _ M _ r m hcard x hx
