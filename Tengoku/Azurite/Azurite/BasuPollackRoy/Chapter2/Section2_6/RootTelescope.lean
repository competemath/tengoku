/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.LimitSeries
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.RecursionInvariants

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 — telescoping the root through the recursion

With the limit `x̄` in hand, the root of `P₀` is reached by peeling off one substitution at a time.
Write `ηₙ = Σ_{k≤n} ξₖ` and the partial sum `Sⱼ = Σ_{n<j} xₙ ε^{ηₙ}`. The *tail root* at level `j`
is `ρⱼ = ε^{−η_{j-1}}·(x̄ − Sⱼ)` (with `η_{-1} = 0`), which satisfies the recursion

> `ρⱼ = ε^{ξⱼ}(xⱼ + ρ_{j+1})`  (pure field algebra),

with `ρ₀ = x̄`. Combined with `substPoly_eval` this telescopes `P₀.eval x̄` into
`ε^{Σ_{k<j}βₖ}·Pⱼ.eval ρⱼ`, whose order exceeds `Σ_{k<j}βₖ → ∞`, forcing `P₀.eval x̄ = 0`. -/

namespace Azurite.BPR

open Polynomial HahnSeries

variable {R : Type*} [Field R] [IsRealClosed R]

/-- `η_{j-1} = ξ₀ + ⋯ + ξ_{j-1}` (the exponent shift at level `j`; `prevEta 0 = 0`).-/
noncomputable def prevEta (s0 : RecState R) (j : ℕ) : ℚ := ∑ k ∈ Finset.range j, xiSeq s0 k

/--
@isnad1 id=eq.0h3v.s5.622a3bb8772c from=translated src=- shape=9eb9e132 vocab=caf2b75f
-/
theorem prevEta_succ (s0 : RecState R) (j : ℕ) :
    prevEta s0 (j + 1) = prevEta s0 j + xiSeq s0 j := Finset.sum_range_succ _ _

/-- `ηₙ = η_{(n+1)-1}`: the cumulative exponent is the next shift.
@isnad1 id=eq.0h3v.s5.d718ea151a56 from=translated src=- shape=cd4cbf58 vocab=edc12ceb
-/
theorem etaSeq_eq_prevEta_succ (s0 : RecState R) (n : ℕ) : etaSeq s0 n = prevEta s0 (n + 1) := rfl

/-- The partial sum `Sⱼ = Σ_{n<j} xₙ ε^{ηₙ}`.-/
noncomputable def partialSumP (s0 : RecState R) (j : ℕ) : PuiseuxSeries R :=
  ∑ n ∈ Finset.range j, constPuiseux (xSeq s0 n) * puiseuxMonomial (etaSeq s0 n)

/-- The tail root `ρⱼ = ε^{−η_{j-1}}·(x̄ − Sⱼ)`.-/
noncomputable def rho (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) (j : ℕ) :
    PuiseuxSeries R :=
  puiseuxMonomial (-(prevEta s0 j)) * (xbarP s0 hnb - partialSumP s0 j)

/-- The accumulated order increment `Σ_{k<j} βₖ`.-/
noncomputable def sumBeta (s0 : RecState R) (j : ℕ) : ℚ := ∑ k ∈ Finset.range j, betaSeq s0 k

/-! ### The barrier (finite) case and the final assembly -/

/-- The tail root relative to an arbitrary target `T` (the algebra needs no property of `T`).-/
noncomputable def rhoG (s0 : RecState R) (T : PuiseuxSeries R) (j : ℕ) : PuiseuxSeries R :=
  puiseuxMonomial (-(prevEta s0 j)) * (T - partialSumP s0 j)

end Azurite.BPR
