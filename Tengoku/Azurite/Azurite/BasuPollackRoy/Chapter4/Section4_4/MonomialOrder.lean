/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Seed.Algebra.MvPolynomial.Division

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.4: the divisibility order on monomials

The set `M_k` of monomials in `k` variables `X₁, …, X_k` is identified with `ℕ^k`, namely the
exponent vectors `Fin k →₀ ℕ` (`MvPolynomial.monomial _ 1`). The **partial order of
divisibility** is the componentwise order
`α = (α₁, …, α_k) ≤ β = (β₁, …, β_k) ⟺ α₁ ≤ β₁, …, α_k ≤ β_k` (`Finsupp.le_def`), which is
exactly divisibility of the associated monomials (`monomial_one_dvd_one_iff`, from
`MvPolynomial.monomial_dvd_monomial`).

For `α ∈ ℕ^{k}` and `n ∈ ℕ` we write `(α, n) = monSnoc α n ∈ ℕ^{k+1}` for the exponent vector
obtained by appending `n` as the last coordinate.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]

/-- **The divisibility order on monomials is the componentwise order.** The monomial `Xᵅ`
(`monomial α 1`) divides `Xᵝ` if and only if `α ≤ β` componentwise (`Finsupp.le_def`).
@isnad1 id=iff.0h4v.s9.fb4148bfd3bb from=translated src=- shape=9e3adab1 vocab=3840615b
-/
theorem monomial_one_dvd_one_iff (i j : Fin k →₀ ℕ) :
    ((monomial i 1 : MvPolynomial (Fin k) K) ∣ monomial j 1) ↔ i ≤ j := by
  rw [monomial_dvd_monomial]
  simp

/-- **BPR notation `(α, n)`.** For `α ∈ ℕ^k` and `n ∈ ℕ`, the exponent vector
`(α₁, …, α_k, n) ∈ ℕ^{k+1}` obtained by appending `n` as the last coordinate.-/
noncomputable def monSnoc (α : Fin k →₀ ℕ) (n : ℕ) : Fin (k + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.snoc (α : Fin k → ℕ) n)

/--
@isnad1 id=eq.0h4v.s6.3ac2c0a6d9c3 from=translated src=- shape=a60d10e8 vocab=dd38c7fb
-/
@[simp] theorem monSnoc_castSucc (α : Fin k →₀ ℕ) (n : ℕ) (i : Fin k) :
    monSnoc α n i.castSucc = α i := by
  simp [monSnoc, Fin.snoc_castSucc]

/--
@isnad1 id=eq.0h3v.s6.bc0ee28a9d1c from=translated src=- shape=7dfe76b0 vocab=39b6dcf6
-/
@[simp] theorem monSnoc_last (α : Fin k →₀ ℕ) (n : ℕ) :
    monSnoc α n (Fin.last k) = n := by
  simp [monSnoc, Fin.snoc_last]

end Azurite.BPR.Chapter4
