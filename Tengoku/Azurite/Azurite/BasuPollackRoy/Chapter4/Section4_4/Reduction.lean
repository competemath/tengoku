/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Seed.RingTheory.MvPolynomial.MonomialOrder
import Tengoku.Seed.Logic.Relation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.4.1: reduction of polynomials

Fix a monomial ordering `m` on `M_k`. For a monomial `X^α` of `P` and another polynomial `G`,
the **reduction** of `(P, X^α)` by `G` is
`Red(P, X^α, G) = P − (cof(X^α, P) / lcof(G)) X^β G` if `X^α = X^β · lmon(G)` for some `β`
(equivalently `lmon(G) ∣ X^α`, i.e. `degree G ≤ α`), and `Red(P, X^α, G) = P` otherwise.

Given a finite set `𝒢 ⊆ K[X₁, …, X_k]`, `Q` is a **reduction of `P` modulo `𝒢`** if
`Q = Red(P, X^α, G)` for some `G ∈ 𝒢` and some monomial `X^α` of `P` (`IsReduction`); and `P`
is **reducible to `Q` modulo `𝒢`** if there is a finite sequence of reductions from `P` to `Q`
(`ReducibleTo`, the reflexive-transitive closure).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]

open scoped Classical in
/-- **Reduction of `(P, X^α)` by `G`.** If `lmon(G) ∣ X^α` (`m.degree G ≤ α`, so
`X^α = X^β · lmon(G)` with `β = α − degree G`), subtract `(cof(X^α,P)/lcof(G)) X^β G`;
otherwise leave `P` unchanged.-/
noncomputable def Red (m : MonomialOrder (Fin k)) (P : MvPolynomial (Fin k) K)
    (α : Fin k →₀ ℕ) (G : MvPolynomial (Fin k) K) : MvPolynomial (Fin k) K :=
  if m.degree G ≤ α then
    P - monomial (α - m.degree G) (P.coeff α / m.leadingCoeff G) * G
  else P

/--
@isnad1 id=eq.1h6v.s9.9a021e88b11d from=translated src=- shape=7b2143aa vocab=a62e7523
-/
theorem Red_of_le (m : MonomialOrder (Fin k)) (P : MvPolynomial (Fin k) K)
    {α : Fin k →₀ ℕ} (G : MvPolynomial (Fin k) K) (h : m.degree G ≤ α) :
    Red m P α G = P - monomial (α - m.degree G) (P.coeff α / m.leadingCoeff G) * G := by
  rw [Red, ite_eq_left h]

/--
@isnad1 id=eq.1h6v.s6.eae11efa8a55 from=translated src=- shape=c2e1b1da vocab=253fa150
-/
theorem Red_of_not_le (m : MonomialOrder (Fin k)) (P : MvPolynomial (Fin k) K)
    {α : Fin k →₀ ℕ} (G : MvPolynomial (Fin k) K) (h : ¬ m.degree G ≤ α) :
    Red m P α G = P := by
  rw [Red, ite_eq_right h]

/-- **`Q` is a reduction of `P` modulo `𝒢`**: `Q = Red(P, X^α, G)` for some `G ∈ 𝒢` and some
monomial `X^α` of `P` (`α ∈ P.support`).-/
def IsReduction (m : MonomialOrder (Fin k)) (𝒢 : Finset (MvPolynomial (Fin k) K))
    (P Q : MvPolynomial (Fin k) K) : Prop :=
  ∃ G ∈ 𝒢, ∃ α ∈ P.support, Q = Red m P α G

/-- **`P` is reducible to `Q` modulo `𝒢`**: there is a finite sequence of reductions modulo
`𝒢` starting with `P` and ending at `Q` (the reflexive-transitive closure of `IsReduction`).-/
def ReducibleTo (m : MonomialOrder (Fin k)) (𝒢 : Finset (MvPolynomial (Fin k) K))
    (P Q : MvPolynomial (Fin k) K) : Prop :=
  Relation.ReflTransGen (IsReduction m 𝒢) P Q

end Azurite.BPR.Chapter4
