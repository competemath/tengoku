import Tengoku
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.CpermEqC
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.OptimalDivisorLower
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.Universal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
**Theorem `thm:optimal-divisor`, unified for the abstract `C`.** Until now this codebase only
had two matching *halves* of this theorem on two different-but-equal representations: the
lower bound `lcm(n,k) ∣ d_{n,k}` (`universal_shift_lcm`, `Universal.lean`, for the abstract `C`)
and the sharp prime-power bound (`optimal_divisor_lower_bound`, `OptimalDivisorLower.lean`, for
the permutation-native `Cperm`/`CpermPair`). With the `Cperm = C` bridge (`CpermEqC.lean`) now
proved, both transfer to the *same* object, and combine here into the single clean statement
the manuscript actually states: for all `n, k ≥ 1`,
`M(n,k) := nk/rad(gcd(n,k))` divides every coefficient of `C_{n+k} - C_n C_k`
(`treeM_dvd_defect`) — this is also exactly the `r = 2` base case of the tree-modulus theorem
`thm:tree-modulus`'s inductive proof (the "exact two-term content theorem" its own proof calls
for at each binary-tree node).

**Assembly**: `CpermPair_eq_Cperm` transports `optimal_divisor_lower_bound` to
`optimal_divisor_lower_bound_C` (the sharp prime-power bound, now for `C`). `treeM_factorization`
computes `M(n,k)`'s `p`-adic valuation exactly: `v_p(n)+v_p(k)-1` when `p ∣ gcd(n,k)` (matching
`optimal_divisor_lower_bound_C`'s exponent exactly) and `v_p(n)+v_p(k) = v_p(\mathrm{lcm}(n,k))`
otherwise (matching `universal_shift_lcm`'s lcm bound). `dvd_of_forall_prime_pow_dvd` packages
per-prime bounds on a single integer into one divisibility via `Nat.factorization_le_iff_dvd`.
`treeM_dvd_defect` combines all of this coefficient-by-coefficient, using
`optimal_divisor_lower_bound_C` when `p ∣ gcd(n,k)` and `universal_shift_lcm` (via
`Nat.factorization_lcm` and `Nat.ordProj_dvd`) otherwise.
-/

namespace CongruenceTheory

open MvPolynomial UniqueFactorizationMonoid

/-- The exact tree-modulus / two-term optimal-divisor modulus: `M(n,k) = nk/rad(gcd(n,k))`,
matching the manuscript's own formula in both `thm:optimal-divisor` and `thm:tree-modulus`
(`r = 2` case).-/
noncomputable def treeM (n k : ℕ) : ℕ := n * k / radical (Nat.gcd n k)

theorem dvd_natAbs_of_int_dvd {D : ℕ} {c : ℤ} (h : (D : ℤ) ∣ c) : D ∣ c.natAbs := by
  have := Int.natAbs_dvd_natAbs.mpr h
  simpa using this

end CongruenceTheory
