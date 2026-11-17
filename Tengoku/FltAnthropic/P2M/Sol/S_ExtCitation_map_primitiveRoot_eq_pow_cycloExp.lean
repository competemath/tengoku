import Tengoku.FltAnthropic.Definitions.Def_ExtCitation_KummerBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ExtCitation_map_primitiveRoot_eq_pow_cycloExp.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ExtCitation_map_primitiveRoot_eq_pow_cycloExp

open ExtCitation
open ValuationSubring
variable {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
  [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]

/--
@isnad1 id=eq.1h3v.s8.aab1fb832016 from=translated src=- shape=530a943f vocab=2f56ef57
-/
theorem solution (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {ξ : AlgebraicClosure ℚ} (hξ : IsPrimitiveRoot ξ p) : σ ξ = ξ ^ cycloExp p σ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hspec := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ)
    (card_rootsOfUnity_eq_self p) (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)
    (SetLike.coe_mem hξ.toRootsOfUnity)
  rw [cycloExp]
  simpa [hξ.val_toRootsOfUnity_coe, Units.val_pow_eq_pow_val] using hspec
