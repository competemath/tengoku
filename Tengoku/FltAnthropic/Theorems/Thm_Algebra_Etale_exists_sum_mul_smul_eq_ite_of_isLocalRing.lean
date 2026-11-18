import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_Etale_exists_sum_mul_smul_eq_ite_of_isLocalRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_Etale_exists_sum_mul_smul_eq_ite_of_isLocalRing.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.2h3v.s9.d9a7109f71f3 from=translated src=- shape=341ca2f9 vocab=0b39e9da
-/
theorem Algebra.Etale.exists_sum_mul_smul_eq_ite_of_isLocalRing
    {W W' : Type*} [CommRing W] [IsLocalRing W] [CommRing W'] [IsLocalRing W']
    [Algebra W W'] [Module.Finite W W'] [Module.Flat W W'] [FaithfulSMul W W'] [Algebra.Etale W W']
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
    (hinv : ∀ w' : W', (∀ γ : Γ, γ • w' = w') ↔ w' ∈ Set.range (algebraMap W W'))
    (hcard : Fintype.card Γ = Module.finrank W W') :
    ∃ (n : ℕ) (x y : Fin n → W'), ∀ γ : Γ, ∑ i, x i * γ • y i = if γ = 1 then 1 else 0 := by exact @_root_.P2MW.S_Algebra_Etale_exists_sum_mul_smul_eq_ite_of_isLocalRing.solution W W' _ _ _ _ _ _ _ _ _ Γ _ _ _ _ _ hinv hcard
