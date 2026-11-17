import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge
import Tengoku.FltAnthropic.Definitions.Def_ExtCitation_KummerBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal

set_option autoImplicit false
open ExtCitation
open scoped IntermediateField Pointwise

/--
@isnad1 id=ex.0h2v.s12.e80d3306c7d1 from=translated src=- shape=45b430bb vocab=c491dfdb
-/
theorem solution
    (q : ℕ) [Fact q.Prime] (p : ℕ) [Fact p.Prime] :
    ∃ ζ : (PadicAlgCl q)ˣ, IsPrimitiveRoot ζ p ∧ ∀ g : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      g • ζ = ζ ^ (cycloChar p (localGaloisToGlobal q g) : ZMod p).val := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero p := ⟨hp0⟩
  haveI : NeZero (p : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hp0⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have hξu : IsUnit ξ := hξ.isUnit hp0
  have hιξ : IsPrimitiveRoot (padicEmbedding q ξ) p :=
    hξ.map_of_injective (padicEmbedding q : AlgebraicClosure ℚ →+* PadicAlgCl q).injective
  have hιξu : IsUnit (padicEmbedding q ξ) := hιξ.isUnit hp0
  refine ⟨hιξu.unit, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hιξ), fun g => ?_⟩
  ext

  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  change g (padicEmbedding q ξ) = _
  rw [← padicEmbedding_localGaloisToGlobal, ← map_pow]
  congr 1

  have hmem : hξu.unit ∈ rootsOfUnity p (AlgebraicClosure ℚ) := by
    rw [mem_rootsOfUnity]; ext; rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hξ.pow_eq_one, Units.val_one]
  have := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
    (localGaloisToGlobal q g : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) hmem
  simp [IsUnit.unit_spec] at this
  exact this
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
