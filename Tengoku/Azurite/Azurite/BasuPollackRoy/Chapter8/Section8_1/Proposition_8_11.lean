/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMatrixMvListProd

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §8.1: Proposition 8.11 (Substitution)

Let `P(Y, X) ∈ ℤ[Y, X]` with `Y = (Y_1, …, Y_ℓ)`, `X = (X_1, …, X_k)`, and let
`Q_i(Y, Z) ∈ ℤ[Y, Z]` for `i = 1, …, k`, with `Z = (Z_1, …, Z_m)`. Define
`R(Y, Z) := P(Y, Q_1(Y, Z), …, Q_k(Y, Z))`. With

* `d_Y`, `d_X`: degrees of `P` w.r.t. `Y` and `X`,
* `D_Y`, `D_Z`: degrees of every `Q_i` w.r.t. `Y` and `Z`,
* `τ_1`, `τ_2`: bounds on the bitsizes of the coefficients of `P` and the `Q_i`,

we have:

* `Y`-degree of `R` ≤ `d_X · D_Y + d_Y`;
* `Z`-degree of `R` ≤ `d_X · D_Z`;
* bitsize of every coefficient of `R` ≤
  `τ_1 + d_X · (τ_2 + ℓ · bit(D_Y) + m · bit(D_Z) + 1) + d_Y + ℓ + k`.

**Encoding.** We use the nested view with `X` outer and `Y` inner for `P`, and
`Y` outer and `Z` inner for `Q_i` and `R`:

* `P : MvPolynomial (Fin k) (MvPolynomial (Fin ℓ) ℤ)`.
* `Q : Fin k → MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)`.
* `R = MvPolynomial.eval₂Hom (MvPolynomial.map MvPolynomial.C) Q P`.

**Note on the bitsize bound.** The Lean bound matches BPR's exact statement.
The tail `+ d_Y + ℓ + k` is achieved via:
(a) the stars-and-bars cardinality bound `support.card ≤ 2^(d+k)`
    (`support_card_le_two_pow`),
(b) the sharper `Int.size_finset_sum_le'` that uses `Nat.size (card - 1)`
    instead of `Nat.size card`, and
(c) a case split on `α = 0` in the per-summand bound to avoid the loose `+1`
    from `Int.size_mul_le` for the constant-product case.
The `bit(D_Y)` / `bit(D_Z)` shape (rather than the slacker `bit(D_Y+1)`
inherited from the naive form of equation (8.2)) is obtained by combining
`p + 1 ≤ 2^bit(p)` with `Int.size_finset_sum_le'` inside the proof of (8.2)
itself; see `Nat.size_prod_succ_sub_one_le` in `BitsizeMatrixMvListProd.lean`. -/

namespace Azurite.BPR

open _root_.Azurite.BPR.MvPolynomial

variable {k ℓ m : ℕ}

/-- The substitution `P(Y, X) ↦ P(Y, Q_1(Y, Z), …, Q_k(Y, Z))`.-/
noncomputable def substitute
    (P : MvPolynomial (Fin k) (MvPolynomial (Fin ℓ) ℤ))
    (Q : Fin k → MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)) :
    MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ) :=
  MvPolynomial.eval₂Hom (MvPolynomial.map MvPolynomial.C) Q P

/-- Expansion of `substitute` as a sum over the support of `P`.
@isnad1 id=eq.0h5v.s9.47a973ed4351 from=translated src=- shape=a73cdf95 vocab=abb39840
-/
theorem substitute_eq_sum
    (P : MvPolynomial (Fin k) (MvPolynomial (Fin ℓ) ℤ))
    (Q : Fin k → MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)) :
    substitute P Q =
      ∑ α ∈ P.support,
        (MvPolynomial.map MvPolynomial.C (P.coeff α)) * ∏ i, (Q i) ^ (α i) :=
  MvPolynomial.eval₂_eq' _ _ _

/-! ### Auxiliary lemmas -/

/-- The Z-degree of a polynomial in the nested encoding
    `MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)`.-/
private noncomputable def zDeg
    (p : MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)) : ℕ :=
  p.support.sup (fun y => (p.coeff y).totalDegree)

/-! ### Cardinality and size helpers -/

/-! ### Decomposition of `((substitute P Q).coeff y).coeff z` -/

end Azurite.BPR
