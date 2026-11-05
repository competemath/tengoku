/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Geometry.Equivalence
import Tengoku.AclGeom.AclGeom.Geometry.FiniteRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A small geometry language for finite configurations

The finite collection of geometric relations used by the configuration layer
(blueprint §small geometry language):

* `MemCl P Q`: `P ∈ cl(Q₀, …, Qₙ₋₁)`, i.e. `P` lies below the join of the
  tuple `Q`;
* `line P Q = P ∨ Q` and `Col P Q R ↔ R ≤ P ∨ Q`;
* `IsPartialQuadrangle f`: six distinct points whose four named triples
  (`quadTriples`) are dependent, all other triples independent, and whose
  total join has rank three (blueprint Def partialquad), with the "every
  other" clause quantified over three-element finsets of `Fin 6`;
* the simplification lemmas naming the four dependent triples, and the
  permutation lemma `IsPartialQuadrangle.comp_perm` transporting the
  predicate along any permutation preserving `quadTriples`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4, checklist G1).
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

section Incidence

/-- `P ∈ cl(Q₀, …, Qₙ₋₁)`: the point `P` lies below the join of the finite
point tuple `Q` (blueprint §small geometry language).-/
def MemCl {n : ℕ} (P : Point k K) (Q : Fin n → Point k K) : Prop :=
  P.1 ≤ ⨆ i, (Q i).1

/-- The line through two points: their join in the closed lattice
(blueprint §small geometry language). When collinearity is intended to
describe a genuine line, distinctness hypotheses must be added at the use
site.-/
def line (P Q : Point k K) : ClosedIF k K :=
  P.1 ⊔ Q.1

/-- `Col P Q R`: the point `R` lies on the line through `P` and `Q`
(blueprint §small geometry language).-/
def Col (P Q R : Point k K) : Prop :=
  R.1 ≤ line P Q

end Incidence

section PartialQuadrangle

/-- The four dependent triples of the partial quadrangle in the canonical
ordering `(S, T, U, S', T', U') = (0, 1, 2, 3, 4, 5)`: `(S, T, U)`,
`(S, T', U')`, `(S', T, U')`, `(S', T', U)` (blueprint Def partialquad).-/
def quadTriples : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 4, 5}, {1, 3, 5}, {2, 3, 4}}

/-- Six distinct points form a *partial quadrangle* when the four named
triples are dependent (rank two), every other three-element subtuple is
independent (rank three), and the join of all six has rank three
(blueprint Def partialquad).-/
structure IsPartialQuadrangle (f : Fin 6 → Point k K) : Prop where
  /-- The six points are distinct.-/
  injective : Function.Injective f
  /-- Each named triple is dependent: its join has rank two.-/
  rank_dep : ∀ s ∈ quadTriples, RankEq 2 (s.sup fun i ↦ (f i).1)
  /-- Every other three-element subtuple is independent: rank three.-/
  rank_free : ∀ s : Finset (Fin 6), s.card = 3 → s ∉ quadTriples →
    RankEq 3 (s.sup fun i ↦ (f i).1)
  /-- The join of all six points has rank three.-/
  rank_total : RankEq 3 (Finset.univ.sup fun i ↦ (f i).1)

namespace IsPartialQuadrangle

variable {f : Fin 6 → Point k K}

/-- Simplification: the triple `(S, T, U)` is dependent.-/
theorem rank_STU (h : IsPartialQuadrangle f) :
    RankEq 2 ((f 0).1 ⊔ ((f 1).1 ⊔ (f 2).1)) := by
  have := h.rank_dep {0, 1, 2} (by decide)
  simpa [Finset.sup_insert] using this

/-- Simplification: the triple `(S, T', U')` is dependent.-/
theorem rank_STU' (h : IsPartialQuadrangle f) :
    RankEq 2 ((f 0).1 ⊔ ((f 4).1 ⊔ (f 5).1)) := by
  have := h.rank_dep {0, 4, 5} (by decide)
  simpa [Finset.sup_insert] using this

/-- Simplification: the triple `(S', T, U')` is dependent.-/
theorem rank_S'TU' (h : IsPartialQuadrangle f) :
    RankEq 2 ((f 1).1 ⊔ ((f 3).1 ⊔ (f 5).1)) := by
  have := h.rank_dep {1, 3, 5} (by decide)
  simpa [Finset.sup_insert] using this

/-- Simplification: the triple `(S', T', U)` is dependent.-/
theorem rank_S'T'U (h : IsPartialQuadrangle f) :
    RankEq 2 ((f 2).1 ⊔ ((f 3).1 ⊔ (f 4).1)) := by
  have := h.rank_dep {2, 3, 4} (by decide)
  simpa [Finset.sup_insert] using this

end IsPartialQuadrangle

end PartialQuadrangle

end

end AclGeom
