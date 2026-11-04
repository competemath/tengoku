/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Tengoku.T3ModelCompanion.T3.GroupTheory.Coproduct.CentralSeries
public import Tengoku.T3ModelCompanion.T3.GroupTheory.Coproduct.Generation
public import Tengoku.T3ModelCompanion.T3.GroupTheory.Coproduct.Strict
public import Tengoku.T3ModelCompanion.T3.GroupTheory.Roots.DerivedStrictification
public import Tengoku.T3ModelCompanion.T3.GroupTheory.Roots.LowerCentralStrictification
public import Tengoku.T3ModelCompanion.T3.ModelTheory.ExistentiallyClosedGroups

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded strict envelopes in existentially closed exponent-three groups

The two simultaneous strictification steps are followed by adjoining a free factor on two
generators. The resulting finite group has coincident lower and upper central series. Its
embedding into an extension is transferred back to the existentially closed group, fixing
the whole original subgroup. The trivial subgroup is handled separately, so the bound also
holds at zero.

The numerical function `strictEnvelopeBound` is defined here, at the paper result supplying it.
Both the model-theoretic conclusion and the preceding algebraic extension construction
work in every universe.

Paper-ID: structure.strict_envelope, main.proposition_a
TeX: T3_modelcompanion_v9.tex, `proposition:bdd LCS`, v9 Proposition 4.13, and Proposition A.
-/

@[expose] public section

universe u

namespace T3

/-- The bound supplied by the paper's strict-envelope construction.

Paper-ID: structure.strict_envelope, main.proposition_a
TeX: T3_modelcompanion_v9.tex, `proposition:bdd LCS`, the function `f₀(n) = 15n²`.-/
def strictEnvelopeBound (n : ℕ) : ℕ := 15 * n ^ 2

/-- The three generator counts fit the paper's quadratic bound for nontrivial input.

Paper-ID: structure.strict_envelope
TeX: T3_modelcompanion_v9.tex, `proposition:bdd LCS`, lines 1343–1347.
@isnad1 id=le.1h1v.s6.cff16bf57b5c from=translated src=- shape=717a326b vocab=41974395
-/
theorem three_stage_rank_le_strictEnvelopeBound {n : ℕ} (hn : 0 < n) :
    3 * n + 3 * (3 * n).choose 2 + 2 ≤ strictEnvelopeBound n := by
  rw [Nat.choose_two_right]
  have hdiv := Nat.mul_div_le ((3 * n) * (3 * n - 1)) 2
  have hsub : 3 * n - 1 + 1 = 3 * n := Nat.sub_add_cancel (by omega)
  unfold strictEnvelopeBound
  nlinarith

namespace StrictEnvelope

variable {G : Type u} [Group G]

end StrictEnvelope

open FirstOrder FirstOrder.Language FirstOrder.Group

end T3
