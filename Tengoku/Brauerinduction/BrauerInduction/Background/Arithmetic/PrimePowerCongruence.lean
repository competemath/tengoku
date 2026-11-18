import Tengoku.Seed.Data.ZMod.Units
import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.Seed.RingTheory.Int.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Congruences modulo prime powers

This file contains elementary congruence results used by the Bernstein proof of
Brauer induction.
-/

namespace Int

/--
If an integer `m` is not divisible by a prime `p`, then its Euler-totient
power is congruent to `1` modulo `p ^ r`.-/
lemma pow_totient_primePow_modEq_one
    (p r : ℕ) [Fact p.Prime] {m : ℤ}
    (hm : ¬ (p : ℤ) ∣ m) :
    m ^ (p ^ r).totient ≡ 1 [ZMOD ((p ^ r : ℕ) : ℤ)] := by
  have hp_not_dvd : ¬ p ∣ m.natAbs := by
    intro h
    exact hm (Int.ofNat_dvd_left.mpr h)
  have hcopNat : m.natAbs.Coprime (p ^ r) := by
    have hcop : m.natAbs.Coprime p :=
      ((Nat.Prime.coprime_iff_not_dvd
        (Fact.out : Nat.Prime p)).2 hp_not_dvd).symm
    simpa using hcop.pow 1 r
  have hcopInt : IsCoprime m (((p ^ r : ℕ) : ℤ)) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hcopNat
  let z : (ZMod (p ^ r))ˣ :=
    ZMod.unitOfIsCoprime m hcopInt
  have hz := ZMod.pow_totient z
  apply
    (ZMod.intCast_eq_intCast_iff
      (m ^ (p ^ r).totient) 1 (p ^ r)).mp
  simp only [Int.cast_pow, Int.cast_one]
  have hz' :=
    congrArg
      (fun a : (ZMod (p ^ r))ˣ =>
        (a : ZMod (p ^ r))) hz
  change
    (z : ZMod (p ^ r)) ^ (p ^ r).totient = 1
    at hz'
  simpa only [z, ZMod.unitOfIsCoprime] using hz'

end Int
