import Tengoku.Jsp000570Lean.Erdos700.Lucas
import Tengoku.Seed.Data.Nat.Prime.Int

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos700

/-- A distinct prime divisor of `k` divides the integer source quotient.
@isnad1 id=dvd.5h4v.s5.1e4a5a2bdee2 from=translated src=- shape=d8e73b12 vocab=36814fc3
-/
theorem prime_dvd_int_source (p q k : ℕ) (z : ℤ)
    (hp : p.Prime) (hq : q.Prime) (hneq : p ≠ q)
    (hqk : q ∣ k) (hk : (k : ℤ) = (p : ℤ)*z) : (q : ℤ) ∣ z := by
  have hi : (q : ℤ) ∣ (k : ℤ) := by exact_mod_cast hqk
  rw [hk] at hi
  rcases (Nat.prime_iff_prime_int.mp hq).dvd_mul.mp hi with hqp | hz
  · have hqpNat : q ∣ p := by exact_mod_cast hqp
    have heq := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqpNat
    exact False.elim (hneq heq.symm)
  · exact hz

/--
@isnad1 id=dvd.6h5v.s5.6aa35c6eb6fa from=translated src=- shape=292b7d43 vocab=b1b02ce4
-/
theorem missing_prime_dvd_int_source (p q N k : ℕ) (z : ℤ)
    (hp : p.Prime) (hq : q.Prime) (hneq : p ≠ q)
    (hqN : q ∣ N) (hmiss : ¬ q ∣ N.choose k)
    (hk : (k : ℤ) = (p : ℤ)*z) : (q : ℤ) ∣ z :=
  prime_dvd_int_source p q k z hp hq hneq
    (dvd_of_not_dvd_choose q N k hq hqN hmiss) hk

end Erdos700
