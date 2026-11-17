import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ExtEndgame_ProductionDatum
import Tengoku.FltAnthropic.Definitions.Def_EllipticCurve_FrobeniusTrace
import Tengoku.FltAnthropic.Definitions.Def_ExtCitation_InertiaKummerCharacter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

/--
@isnad1 id=eq.2h3v.s10.bc98b02a2230 from=translated src=- shape=c068adfa vocab=0ea255ff
-/
theorem solution
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p)
    {σ : primeLocalGaloisGroup q}
    (hσ : σ ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) :
    cycloChar p (primeLocalToGlobal q σ) = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h1 : (1 : ZMod p) = (cycloChar p (primeLocalToGlobal q σ) : ZMod p) := by
    refine modularCyclotomicCharacter.unique (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
      (primeLocalToGlobal q σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (fun t ht => ?_)
    rw [ZMod.val_one, pow_one]
    have ht' : ((t : AlgebraicClosure ℚ)) ^ p = 1 := by
      rw [mem_rootsOfUnity] at ht
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    exact inertiaPullback_smul_eq_of_pow_eq_one q hσ (not_dvd_of_ne p q hqp) ht'
  exact Units.ext h1.symm
