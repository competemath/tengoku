import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.3h4v.s10.319c33e0a0cd from=translated src=- shape=5384dfe0 vocab=c97a09f4
-/
theorem ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F] :
    ∃ a : ℕ, ∀ x ∈ F, (σ ^ (q ^ a)) x = x := by exact @_root_.P2MW.S_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild.solution q hq P hP σ hwild F _ _
