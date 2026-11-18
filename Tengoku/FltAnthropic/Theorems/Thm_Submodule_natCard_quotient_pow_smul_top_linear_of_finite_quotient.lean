import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Submodule_natCard_quotient_pow_smul_top_linear_of_finite_quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Submodule_natCard_quotient_pow_smul_top_linear_of_finite_quotient.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem Submodule.natCard_quotient_pow_smul_top_linear_of_finite_quotient
    (R : Type*) [CommRing R] [IsNoetherianRing R] (q : ℕ) [Fact q.Prime]
    (hRq : Finite (R ⧸ Ideal.span {(q : R)}))
    (I : Ideal R) (hqI : (q : R) ∈ I)
    (X : Type*) [AddCommGroup X] [Module R X] [Module.Finite R X] :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card (X ⧸ (I ^ m • (⊤ : Submodule R X))) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card (X ⧸ (I ^ m • (⊤ : Submodule R X))) * q ^ C := by exact @_root_.P2MW.S_Submodule_natCard_quotient_pow_smul_top_linear_of_finite_quotient.solution R _ _ q _ hRq I hqI X _ _ _
