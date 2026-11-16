import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.NumberTheory.Cyclotomic.CyclotomicCharacter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicClosure_exists_apply_eq_pow_of_pow_eq_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicClosure_exists_apply_eq_pow_of_pow_eq_one

/--
@isnad1 id=ex.1h2v.s8.7d9f4f13f1b7 from=translated src=- shape=d7600af0 vocab=f3c08465
-/
theorem solution (n : ℕ) (hn : n ≠ 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ a : ℕ, ∀ μ : AlgebraicClosure ℚ, μ ^ n = 1 → σ μ = μ ^ a := by
  haveI : NeZero n := ⟨hn⟩
  refine ⟨(modularCyclotomicCharacter.toFun n
    (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)).val, fun μ hμ => ?_⟩
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hμ
    exact zero_ne_one hμ
  have hmem : Units.mk0 μ hμ0 ∈ rootsOfUnity n (AlgebraicClosure ℚ) := by
    rw [mem_rootsOfUnity']
    exact hμ
  have h := modularCyclotomicCharacter.toFun_spec'
    (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) hmem
  simpa using h
