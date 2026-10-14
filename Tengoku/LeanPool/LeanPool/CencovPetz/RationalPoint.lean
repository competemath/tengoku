/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Tengoku.LeanPool.LeanPool.CencovPetz.SplittingUniform
public import Tengoku

/-!
# `CencovPetz.RationalPoint`

Common-denominator (“rational”) points of the finite open simplex.

The classical finite Čencov/Chentsov argument typically proves the scalar-multiple claim first at
the uniform point, then extends it to a dense family of points with rational coordinates by a
fiberwise splitting construction.

This file packages the notion of a common-denominator point and relates it to
`Simplex.IsSplitRepresentable`.

## Main definitions

- `CencovPetz.Simplex.IsRational`: `p(a) = m(a) / (∑ m)` for some `m : α → ℕ` with
  strictly positive coordinates.

## Main results

- `CencovPetz.Simplex.IsRational.isSplitRepresentable`
-/

@[expose] public section

namespace LeanPool.CencovPetz
open scoped BigOperators

universe u

namespace MarkovMorphism

variable {α : Type u} [Fintype α]

/--
@isnad1 id=eq.0h2v.s5.0ce46665d2d5 from=translated src=- shape=d20d038d vocab=b3903ac4
-/
lemma card_splitTarget (m : α → ℕ) :
    Fintype.card (SplitTarget (α := α) m) = ∑ a : α, m a := by
  classical
  simp [SplitTarget]

end MarkovMorphism

namespace Simplex

variable {α : Type u} [Fintype α]

/-- A simplex point whose coordinates have a finite common-denominator representation
`p(a) = m(a) / (∑ m)` for some strictly positive `m : α → ℕ`. -/
def IsRational (p : Simplex α) : Prop :=
  ∃ m : α → ℕ,
    (∀ a, 0 < m a) ∧
      ∀ a, p.p a = (m a : ℝ) / ((∑ a : α, m a : ℕ) : ℝ)

/--
@isnad1 id=issplitr.1h2v.s4.86ecc2d065e0 from=translated src=- shape=93e860ac vocab=d5bd54a5
-/
lemma IsRational.isSplitRepresentable {p : Simplex α} (hp : IsRational (α := α) p) :
    IsSplitRepresentable (α := α) p := by
  rcases hp with ⟨m, hm, hp⟩
  refine ⟨m, hm, ?_⟩
  simp_all

end Simplex
end LeanPool.CencovPetz
