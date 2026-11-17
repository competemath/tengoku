import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ExtCitation_KummerBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot

set_option autoImplicit false
open ExtCitation

/--
@isnad1 id=eq.2h3v.s10.2ca77c99ac8f from=translated src=- shape=515536f7 vocab=f50e6bdc
-/
theorem solution
    (p : ℕ) [Fact p.Prime] (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {ξ : AlgebraicClosure ℚ} (hξ : IsPrimitiveRoot ξ p) (hg : g ξ = ξ) :
    cycloChar p g = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h1 : (1 : ZMod p) = (cycloChar p g : ZMod p) := by
    refine modularCyclotomicCharacter.unique (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
      (g : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (fun t ht => ?_)
    rw [ZMod.val_one, pow_one]
    have ht' : ((t : AlgebraicClosure ℚ)) ^ p = 1 := by
      rw [mem_rootsOfUnity] at ht
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    obtain ⟨i, -, hi⟩ := hξ.eq_pow_of_pow_eq_one ht'
    change g (t : AlgebraicClosure ℚ) = t
    rw [← hi, map_pow]
    exact congrArg (· ^ i) hg
  exact Units.ext h1.symm
