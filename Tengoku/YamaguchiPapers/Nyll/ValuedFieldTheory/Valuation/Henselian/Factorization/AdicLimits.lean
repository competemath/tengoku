/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Basic
import Tengoku.Seed.RingTheory.AdicCompletion.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# coefficientwise limit preparation

This file records the coefficientwise Cauchy form of the infinite Hensel
approximants.  It is the input needed for the adic-completeness step in
the coefficientwise proof of Hensel's lemma.
-/

noncomputable section

open scoped Polynomial
open scoped BigOperators

namespace AlgebraicNumberTheory
namespace Valuations

/-- the directed adic Cauchy estimate for a coefficient
sequence: later differences from stage `M` lie in `I^(M+1)`.-/
def henselFactorization_adicCoeffCauchy
    {R : Type*} [CommRing R] (I : Ideal R) (x : ℕ → R) : Prop :=
  ∀ {M N : ℕ}, M ≤ N → x N - x M ∈ I ^ (M + 1)

/-- assemble finitely many coefficient limits into the
polynomial supported in degrees at most `N`.-/
def henselFactorization_polyOfLimitCoeffs
    {R : Type*} [Semiring R] (N : ℕ) (c : ℕ → R) : R[X] :=
  Finset.sum (Finset.range (N + 1)) fun i => Polynomial.monomial i (c i)

end Valuations
end AlgebraicNumberTheory

end
