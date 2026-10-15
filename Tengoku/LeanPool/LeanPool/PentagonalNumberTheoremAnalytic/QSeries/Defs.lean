/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import Tengoku

/-!
# q-Pochhammer symbol and Gaussian binomial coefficient

This file defines the finite q-Pochhammer symbol $(a;q)_n$ and the Gaussian
binomial coefficient $\binom{n}{k}_q$, together with their basic properties.

## Main definitions

* `QSeries.qPochhammer a q n` — the finite q-Pochhammer symbol
  $(a;q)_n = \prod_{k=0}^{n-1}(1 - a q^k)$.
* `QSeries.qBinom n k q` — the Gaussian binomial coefficient $\binom{n}{k}_q$,
  defined via the q-Pascal recurrence.

## Main results

* `QSeries.qPochhammer_succ` — the recurrence $(a;q)_{n+1} = (a;q)_n (1 - aq^n)$.
* `QSeries.qBinom_succ_succ` — the q-Pascal recurrence.
* `QSeries.qBinom_eq_zero_of_lt` — vanishing above the diagonal.
* `QSeries.qBinom_self` — diagonal value is 1.
* `QSeries.qBinom_mul_qPochhammer_mul_qPochhammer` — closed-form identity
  $\binom{n}{k}_q (q;q)_k (q;q)_{n-k} = (q;q)_n$.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace QSeries.Nat

/-- Pascal's rule specialised to `C(·, 2)`.
@isnad1 id=eq.0h1v.s5.782b9f21d2d6 from=translated src=- shape=1dc9affc vocab=04865d53
-/
theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

/-- `C(m+k,2) + C(m,2) + m = C(k,2) + m*(m+k)`.
@isnad1 id=eq.0h2v.s6.78bcacf0843b from=translated src=- shape=d858ec2c vocab=14a23cc3
-/
theorem choose_two_add_choose_two (m k : ℕ) :
    (m + k).choose 2 + m.choose 2 + m = k.choose 2 + m * (m + k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 from by omega, choose_two_succ, choose_two_succ]; linarith

/-- `C(n,2) + C(n+l+1,2) + (n+l+1) = C(l+2,2) + n*(n+l+1)`.
@isnad1 id=eq.0h2v.s7.0d06c38093c6 from=translated src=- shape=855d2831 vocab=14a23cc3
-/
theorem choose_two_add_choose_two' (n l : ℕ) :
    n.choose 2 + (n + (l + 1)).choose 2 + (n + (l + 1)) =
    (l + 2).choose 2 + n * (n + (l + 1)) := by
  have h := choose_two_add_choose_two n (l + 1)
  have h2 : (l + 2).choose 2 = (l + 1).choose 2 + (l + 1) := choose_two_succ (l + 1)
  linarith

/-- `C(k,2)` is at least `k - 1`.
@isnad1 id=le.0h1v.s4.8499571f154f from=translated src=- shape=51b728fd vocab=8264a478
-/
theorem le_choose_two_add_one (k : ℕ) : k ≤ k.choose 2 + 1 := by
  induction k with
  | zero => omega
  | succ k ih => rw [choose_two_succ]; omega

/-- `C(k,2)` eventually dominates: `d < C(k,2)` as soon as `d + 2 ≤ k`.
@isnad1 id=lt.1h2v.s5.76d196e64e26 from=translated src=- shape=b73e2e88 vocab=97a98e93
-/
theorem lt_choose_two_of_add_two_le {d k : ℕ} (hk : d + 2 ≤ k) : d < k.choose 2 := by
  have := le_choose_two_add_one k
  omega

end QSeries.Nat

namespace QSeries

variable {R : Type*}

/-- **Finite q-Pochhammer symbol.**
$(a;q)_n = \prod_{k=0}^{n-1} (1 - a q^k)$. -/
def qPochhammer [CommRing R] (a q : R) (n : ℕ) : R :=
  ∏ k ∈ range n, (1 - a * q ^ k)

/-- The empty q-Pochhammer product $(a;q)_0 = 1$.
@isnad1 id=eq.0h3v.s5.dd2b303daff5 from=translated src=- shape=9c02e61a vocab=f547880d
-/
@[simp]
theorem qPochhammer_zero [CommRing R] (a q : R) : qPochhammer a q 0 = 1 := by
  simp [qPochhammer]

/-- **Recurrence for q-Pochhammer.** $(a;q)_{n+1} = (a;q)_n \cdot (1 - a q^n)$.
@isnad1 id=eq.0h4v.s6.558f08169639 from=translated src=- shape=d81e113d vocab=0fd15abc
-/
theorem qPochhammer_succ [CommRing R] (a q : R) (n : ℕ) :
    qPochhammer a q (n + 1) = qPochhammer a q n * (1 - a * q ^ n) := by
  simp [qPochhammer, prod_range_succ]

/-- **Gaussian binomial coefficient** $\binom{n}{k}_q$.

Defined by the q-Pascal recurrence so that the result is always a polynomial
in $q$ (no division). The boundary cases are
$\binom{0}{0}_q = 1$, $\binom{0}{k+1}_q = 0$, $\binom{n+1}{0}_q = 1$. -/
def qBinom [CommRing R] : ℕ → ℕ → R → R
  | 0,     0,     _ => 1
  | 0,     _ + 1, _ => 0
  | _ + 1, 0,     _ => 1
  | n + 1, k + 1, q => qBinom n (k + 1) q + q ^ (n - k) * qBinom n k q

/-- The Gaussian binomial coefficient $\binom{0}{0}_q = 1$.
@isnad1 id=eq.0h2v.s5.6945f316729d from=translated src=- shape=436a5181 vocab=5a7007e4
-/
@[simp] theorem qBinom_zero_zero [CommRing R] (q : R) : qBinom 0 0 q = 1 := rfl

/-- The Gaussian binomial coefficient $\binom{0}{k+1}_q = 0$.
@isnad1 id=eq.0h3v.s5.d6e31235247a from=translated src=- shape=62b0c9ee vocab=b11f0b75
-/
@[simp] theorem qBinom_zero_succ [CommRing R] (k : ℕ) (q : R) :
    qBinom 0 (k + 1) q = 0 := rfl

/-- The Gaussian binomial coefficient $\binom{n+1}{0}_q = 1$.
@isnad1 id=eq.0h3v.s5.3591f46e793a from=translated src=- shape=bbd5680c vocab=b11f0b75
-/
@[simp] theorem qBinom_succ_zero [CommRing R] (n : ℕ) (q : R) :
    qBinom (n + 1) 0 q = 1 := rfl

/-- The Gaussian binomial coefficient $\binom{n}{0}_q = 1$ for all $n$.
@isnad1 id=eq.0h3v.s5.5461992904ff from=translated src=- shape=addebc18 vocab=5a7007e4
-/
@[simp] theorem qBinom_zero_right [CommRing R] (n : ℕ) (q : R) :
    qBinom n 0 q = 1 := by cases n <;> rfl

/-- The q-Pascal recurrence $\binom{n+1}{k+1}_q = \binom{n}{k+1}_q + q^{n-k}\binom{n}{k}_q$.
@isnad1 id=eq.0h4v.s6.9504f31ee3ba from=translated src=- shape=4c1705c3 vocab=c398a8f0
-/
theorem qBinom_succ_succ [CommRing R] (n k : ℕ) (q : R) :
    qBinom (n + 1) (k + 1) q
      = qBinom n (k + 1) q + q ^ (n - k) * qBinom n k q := rfl

/-- $\binom{n}{k}_q = 0$ whenever $k > n$.
@isnad1 id=eq.1h4v.s5.18cc68db1619 from=translated src=- shape=95ec3710 vocab=0613e94f
-/
theorem qBinom_eq_zero_of_lt [CommRing R] (q : R) :
    ∀ {n k : ℕ}, n < k → qBinom n k q = 0
  | 0,     0,     h => absurd h (Nat.lt_irrefl _)
  | 0,     _ + 1, _ => rfl
  | _ + 1, 0,     h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [qBinom_succ_succ,
        qBinom_eq_zero_of_lt q (show n < k + 1 by omega),
        qBinom_eq_zero_of_lt q (show n < k by omega)]
    ring

/-- $\binom{n}{n}_q = 1$.
@isnad1 id=eq.0h3v.s4.ee4f4119c60b from=translated src=- shape=8405f082 vocab=5a7007e4
-/
theorem qBinom_self [CommRing R] (q : R) : ∀ n : ℕ, qBinom n n q = 1
  | 0 => rfl
  | n + 1 => by
    rw [qBinom_succ_succ, qBinom_eq_zero_of_lt q (Nat.lt_succ_self n),
        qBinom_self q n, Nat.sub_self, pow_zero]
    ring

/-- **Closed-form identity.**
For $k \leq n$: $\binom{n}{k}_q (q;q)_k (q;q)_{n-k} = (q;q)_n$.
@isnad1 id=eq.1h4v.s6.97b137ddd9cd from=translated src=- shape=c9879ebc vocab=c9bc88ba
-/
theorem qBinom_mul_qPochhammer_mul_qPochhammer [CommRing R] (q : R) :
    ∀ {n k : ℕ}, k ≤ n →
      qBinom n k q * qPochhammer q q k * qPochhammer q q (n - k)
        = qPochhammer q q n := by
  intro n
  induction n with
  | zero =>
    rintro k hk
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    rintro (_ | k) hk
    · simp
    obtain hlt | rfl : k + 1 ≤ n ∨ n = k := by omega
    · -- Interior case: write `n = k + 1 + m` and feed in both induction hypotheses.
      obtain ⟨m, rfl⟩ : ∃ m, n = k + 1 + m := ⟨n - (k + 1), by omega⟩
      have ih1 := ih (show k + 1 ≤ k + 1 + m by omega)
      have ih2 := ih (show k ≤ k + 1 + m by omega)
      rw [show k + 1 + m - (k + 1) = m from by omega, qPochhammer_succ q q k] at ih1
      rw [show k + 1 + m - k = m + 1 from by omega, qPochhammer_succ q q m] at ih2
      rw [qBinom_succ_succ, show k + 1 + m + 1 - (k + 1) = m + 1 from by omega,
        show k + 1 + m - k = m + 1 from by omega, qPochhammer_succ q q k,
        qPochhammer_succ q q m, qPochhammer_succ q q (k + 1 + m)]
      linear_combination (1 - q * q ^ m) * ih1 + q ^ (m + 1) * (1 - q * q ^ k) * ih2
    · -- Diagonal case `k = n`.
      rw [qBinom_succ_succ, qBinom_eq_zero_of_lt q (Nat.lt_succ_self _), qBinom_self,
        Nat.sub_self, Nat.sub_self, pow_zero, qPochhammer_zero]
      ring

end QSeries
