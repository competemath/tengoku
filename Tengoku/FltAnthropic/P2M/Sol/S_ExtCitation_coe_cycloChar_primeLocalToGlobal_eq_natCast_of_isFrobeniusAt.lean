import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ExtEndgame_ProductionDatum
import Tengoku.FltAnthropic.Definitions.Def_EllipticCurve_FrobeniusTrace
import Tengoku.FltAnthropic.Definitions.Def_ExtCitation_InertiaKummerCharacter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ExtCitation_coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ExtCitation_coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem solution
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p)
    {φ : primeLocalGaloisGroup q}
    (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q) :
    ((cycloChar p (primeLocalToGlobal q φ) : (ZMod p)ˣ) : ZMod p) = ((q : ℕ) : ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  symm
  refine modularCyclotomicCharacter.unique (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
    (primeLocalToGlobal q φ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (fun t ht => ?_)
  have ht' : ((t : AlgebraicClosure ℚ)) ^ p = 1 := by
    rw [mem_rootsOfUnity] at ht
    rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  rw [ZMod.val_natCast]
  change primeLocalToGlobal q φ (t : AlgebraicClosure ℚ) = _
  rw [frobenius_smul_eq_pow_of_pow_eq_one q hφ (not_dvd_of_ne p q hqp) ht']
  conv_lhs => rw [← Nat.mod_add_div (q : ℕ) p, pow_add, pow_mul, ht', one_pow, mul_one]
