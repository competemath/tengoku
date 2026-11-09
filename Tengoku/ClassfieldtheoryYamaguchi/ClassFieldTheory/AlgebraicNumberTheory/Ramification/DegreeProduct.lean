/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.FieldTheory.Galois.GaloisClosure
import Tengoku.Seed.NumberTheory.Cyclotomic.PrimitiveRoots
import Tengoku.ClassfieldtheoryYamaguchi.ValuedFieldTheory.Ramification.InertiaCardinality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# A finite-group degree product

Once the chosen inertia groups generate the full abelian Galois group and
their orders satisfy the local prime-power bounds, the global degree is at
most the totient of the conductor candidate.  This file isolates that finite
group calculation from the arithmetic construction of the chosen primes.
-/

noncomputable section

namespace AlgebraicNumberTheory.Ramification

open RamificationTheory
open scoped BigOperators IsMulCommutative

/-- Euler's totient is multiplicative on a finite product of powers of
distinct primes.-/
theorem totient_prod_primePowers
    (S : Finset Nat.Primes) (e : Nat.Primes → ℕ) :
    Nat.totient (∏ p ∈ S, p.1 ^ e p) =
      ∏ p ∈ S, Nat.totient (p.1 ^ e p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      have hcoprime : Nat.Coprime (p.1 ^ e p) (∏ q ∈ S, q.1 ^ e q) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        apply Nat.Coprime.pow_left
        apply Nat.Coprime.pow_right
        exact (Nat.coprime_primes p.2 q.2).2
          (Subtype.coe_ne_coe.mpr fun hpq => hp (hpq.symm ▸ hq))
      rw [Finset.prod_insert hp, Finset.prod_insert hp,
        Nat.totient_mul hcoprime, ih]

end AlgebraicNumberTheory.Ramification

end
