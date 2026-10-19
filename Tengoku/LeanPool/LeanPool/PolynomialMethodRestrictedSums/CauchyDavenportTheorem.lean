/-
Copyright (c) 2026 Nick Adfor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Adfor
-/
module

public import Tengoku.Seed.Algebra.Field.ZMod
meta import Lean.Meta.Tactic.NormCast
import Tengoku.LeanPool.LeanPool.PolynomialMethodRestrictedSums.ANRPolynomialMethod
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Algebra.Order.Ring.Star
import Tengoku.Seed.Analysis.Normed.Group.Basic
import Tengoku.Seed.Data.EReal.Operations
import Tengoku.Seed.Data.Int.ConditionallyCompleteOrder
import Tengoku.Seed.Data.Int.Star
import Tengoku.Seed.Data.Nat.Choose.Sum
import Tengoku.Seed.Data.Nat.Prime.Factorial
import Tengoku.Seed.Data.Sym.Sym2.Init
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Order
import Tengoku.Seed.Topology.MetricSpace.Bounded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Cauchy-Davenport theorem

Derives the Cauchy-Davenport theorem `cauchy_davenport` on sumsets in `ZMod p`
from the Alon-Nathanson-Ruzsa polynomial method.
-/

@[expose] public section

open Finsupp
open scoped Finset
open MvPolynomial
open AddMonoidAlgebra (coeff)
open BigOperators

-- 2.1
variable {R : Type*} [CommRing R]
-- variable {p : ℕ} [Fact p.Prime]
variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

--
-- 1.  Fin 2
lemma sum_fin_two {M : Type*} [AddCommMonoid M] (f : Fin 2 → M) :
    ∑ i, f i = f 0 + f 1 := by
  rw [Fin.sum_univ_two]

-- 2.  ZMod p
lemma binomial_coeff_ne_zero_mod_p (n k : ℕ) (hp : p.Prime) (h_k : k ≤ n) (h_n : n < p) :
    (Nat.choose n k : ZMod p) ≠ 0 := by
  rw [ne_eq, CharP.cast_eq_zero_iff (ZMod p) p]
  intro hdiv
  have hchoose : n.choose k ∣ n.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial h_k, mul_assoc, mul_comm]
    exact Nat.dvd_mul_left _ _
  exact h_n.not_ge (hp.dvd_factorial.mp (dvd_trans hdiv hchoose))

/-- The sumset `A + B = { a + b | a ∈ A, b ∈ B }` as a `Finset`. -/
def sumset {α : Type*} [Add α] [DecidableEq α] (A B : Finset α) : Finset α :=
  (A ×ˢ B).image (fun x => x.1 + x.2)

variable {A B : Finset (ZMod p)}

-- 3.  "Case 1" ()
