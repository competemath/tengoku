import Tengoku.Seed.NumberTheory.LucasPrimality
import Tengoku.Seed.Tactic.ReduceModChar
import Tengoku.Seed.Tactic.NormNum.Prime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Primality certificates for the concrete boundary counterexample

The four large primes are certified using mathlib's Lucas primality criterion.
Each factor of one less than a target is certified by `norm_num`; the modular
power checks use the proof-producing `reduce_mod_char` tactic.
-/

namespace Erdos700.Counterexample

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private theorem prime_3 : Nat.Prime 3 := by norm_num
private theorem prime_5 : Nat.Prime 5 := by norm_num
private theorem prime_7 : Nat.Prime 7 := by norm_num
private theorem prime_13 : Nat.Prime 13 := by norm_num
private theorem prime_17 : Nat.Prime 17 := by norm_num
private theorem prime_37 : Nat.Prime 37 := by norm_num
private theorem prime_263 : Nat.Prime 263 := by norm_num
private theorem prime_523 : Nat.Prime 523 := by norm_num
private theorem prime_563 : Nat.Prime 563 := by norm_num
private theorem prime_145471 : Nat.Prime 145471 := by norm_num
private theorem prime_507497 : Nat.Prime 507497 := by norm_num
private theorem prime_538789 : Nat.Prime 538789 := by norm_num
private theorem prime_3843199 : Nat.Prime 3843199 := by norm_num

/-- The smallest prime in the counterexample.-/
theorem prime_P : Nat.Prime 25480409371 := by
  apply lucas_primality 25480409371 (7 : ZMod 25480409371)
  · reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * (3 * (5 * (13 * (17 * 3843199)))) at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq Nat.prime_two,
      Nat.prime_dvd_prime_iff_eq hq prime_3,
      Nat.prime_dvd_prime_iff_eq hq prime_5,
      Nat.prime_dvd_prime_iff_eq hq prime_13,
      Nat.prime_dvd_prime_iff_eq hq prime_17,
      Nat.prime_dvd_prime_iff_eq hq prime_3843199] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

/-- The prime at offset six.-/
theorem prime_PA : Nat.Prime 25480409377 := by
  apply lucas_primality 25480409377 (13 : ZMod 25480409377)
  · reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * (2 * (2 * (2 * (2 * (3 * (523 * 507497)))))) at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq Nat.prime_two,
      Nat.prime_dvd_prime_iff_eq hq prime_3,
      Nat.prime_dvd_prime_iff_eq hq prime_523,
      Nat.prime_dvd_prime_iff_eq hq prime_507497] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

/-- The prime at offset eighteen.-/
theorem prime_PB : Nat.Prime 25480409389 := by
  apply lucas_primality 25480409389 (2 : ZMod 25480409389)
  · reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * (2 * (3 * (7 * (563 * 538789)))) at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq Nat.prime_two,
      Nat.prime_dvd_prime_iff_eq hq prime_3,
      Nat.prime_dvd_prime_iff_eq hq prime_7,
      Nat.prime_dvd_prime_iff_eq hq prime_563,
      Nat.prime_dvd_prime_iff_eq hq prime_538789] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

/-- The largest prime, at offset forty-eight.-/
theorem prime_PC : Nat.Prime 25480409419 := by
  apply lucas_primality 25480409419 (2 : ZMod 25480409419)
  · reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * (3 * (3 * (37 * (263 * 145471)))) at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq Nat.prime_two,
      Nat.prime_dvd_prime_iff_eq hq prime_3,
      Nat.prime_dvd_prime_iff_eq hq prime_37,
      Nat.prime_dvd_prime_iff_eq hq prime_263,
      Nat.prime_dvd_prime_iff_eq hq prime_145471] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

end Erdos700.Counterexample
