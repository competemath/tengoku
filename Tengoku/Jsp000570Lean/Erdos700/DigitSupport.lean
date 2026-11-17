/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.Jsp000570Lean.Erdos700.Lucas
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Three-digit support obtained from Lucas's theorem

The statements use natural numbers, so nonnegativity of all digits is automatic.
The coefficient above the first three digits may be arbitrary.
-/

namespace Erdos700

/-- Euclidean division twice gives the three-term expansion; the leading
coefficient need not itself be a digit unless `x < p^3`.-/
theorem nat_three_digit_expansion (p x : ℕ) :
    x = (x / p ^ 2) * p ^ 2 + (x / p % p) * p + x % p := by
  have hdiv : (x / p) / p = x / p ^ 2 := by
    rw [Nat.div_div_eq_div_mul, pow_two]
  calc
    x = x % p + p * (x / p) := (Nat.mod_add_div x p).symm
    _ = x % p + p * ((x / p) % p + p * ((x / p) / p)) := by
      rw [Nat.mod_add_div (x / p) p]
    _ = (x / p ^ 2) * p ^ 2 + (x / p % p) * p + x % p := by
      rw [hdiv]
      ring

/-- Identify the lowest three digits from an explicit expansion. No upper
bound on the fourth coefficient is needed.-/
theorem first_three_digits_of_expansion (p x A3 A2 A1 A0 : ℕ)
    (hp : 0 < p) (h0 : A0 < p) (h1 : A1 < p) (h2 : A2 < p)
    (hx : x = A3 * p ^ 3 + A2 * p ^ 2 + A1 * p + A0) :
    x % p = A0 ∧ x / p % p = A1 ∧ x / p ^ 2 % p = A2 := by
  have hnorm : x = A0 + p * (A1 + p * (A2 + p * A3)) := by
    rw [hx]
    ring
  have hdiv1 : x / p = A1 + p * (A2 + p * A3) := by
    rw [hnorm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt h0, zero_add]
  have hdiv2 : x / p ^ 2 = A2 + p * A3 := by
    rw [pow_two, ← Nat.div_div_eq_div_mul, hdiv1,
      Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt h1, zero_add]
  constructor
  · rw [hnorm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  constructor
  · rw [hdiv1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  · rw [hdiv2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]

/-- Convert the Lucas inequalities into the three integer digits used in
the arithmetic pair exclusions.-/
theorem exists_three_digits_of_not_dvd_choose
    (p n k A3 A2 A1 A0 : ℕ) (hp : p.Prime) (hpn : p ∣ n)
    (hmiss : ¬ p ∣ n.choose k) (hk : k / p < p ^ 3)
    (h0 : A0 < p) (h1 : A1 < p) (h2 : A2 < p)
    (hn : n / p = A3 * p ^ 3 + A2 * p ^ 2 + A1 * p + A0) :
    ∃ u v w : ℕ,
      k = p * (u * p ^ 2 + v * p + w) ∧
      u < p ∧ v < p ∧ w < p ∧ u ≤ A2 ∧ v ≤ A1 ∧ w ≤ A0 := by
  obtain ⟨hpk, hdigits⟩ := lucas_quotient_digits p n k hp hpn hmiss
  obtain ⟨hD0, hD1, hD2⟩ :=
    first_three_digits_of_expansion p (n / p) A3 A2 A1 A0 hp.pos h0 h1 h2 hn
  have hu : (k / p) / p ^ 2 < p := by
    apply (Nat.div_lt_iff_lt_mul (pow_pos hp.pos 2)).mpr
    simpa only [pow_succ, mul_comm] using hk
  have hu_le : (k / p) / p ^ 2 ≤ A2 := by
    simpa only [Nat.mod_eq_of_lt hu, hD2] using hdigits 2
  have hv_le : (k / p) / p % p ≤ A1 := by
    simpa only [pow_one, hD1] using hdigits 1
  have hw_le : (k / p) % p ≤ A0 := by
    simpa only [pow_zero, Nat.div_one, hD0] using hdigits 0
  refine ⟨(k / p) / p ^ 2, (k / p) / p % p, (k / p) % p, ?_,
    hu, Nat.mod_lt _ hp.pos, Nat.mod_lt _ hp.pos, hu_le, hv_le, hw_le⟩
  calc
    k = p * (k / p) := (Nat.mul_div_cancel' hpk).symm
    _ = p * ((k / p) / p ^ 2 * p ^ 2 + ((k / p) / p % p) * p + (k / p) % p) := by
      rw [← nat_three_digit_expansion p (k / p)]

end Erdos700
