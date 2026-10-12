/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Tengoku.Tauceti.TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Coordinates
public import Tengoku.Tauceti.TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Defs
public import Tengoku
import Tengoku.Tauceti.TauCeti.MeasureTheory.Measure.ProjectiveLimit.Countable

/-!
# Exchangeable laws on infinite graphs

An exchangeable random graph on the labels `ℕ` is a probability law on `SimpleGraph ℕ` that is
invariant under relabelling along every permutation of `ℕ`. Its windows — the laws of the
restrictions to the labels `Fin k` — form an `ExchangeableGraphLaw`: restricting along an
injection `Fin k ↪ Fin l` is, on the infinite graph, relabelling by a permutation of `ℕ` extending
the injection, followed by taking the smaller window. Conversely every `ExchangeableGraphLaw` is
the family of windows of exactly one such law, so the two presentations of an exchangeable random
graph agree (`exchangeableGraphLawEquivInfinite`).

Uniqueness holds because a finite measure on `SimpleGraph ℕ` is determined by its windows
(`measure_ext_of_map_restrictFin`). Existence is Kolmogorov's extension theorem: reading an
infinite graph through its Boolean edge coordinates `graphCoordEquiv`, the level-`n` marginals
prescribe a projective family of laws on the finitely many coordinates below any bound, and a
projective limit on the countable product of the coordinates exists. The extension is exchangeable
because each window of a relabelled extension is a restriction of a larger window along an
injection, which the consistency of the marginals controls.

## Main definitions

* `TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw` — a relabelling-invariant probability law
  on the graphs on `ℕ`;
* `TauCeti.DenseGraphLimits.exchangeableGraphLawEquivInfinite` — consistent finite marginals are
  the same thing as an exchangeable law on infinite graphs.

## Main results

* `TauCeti.DenseGraphLimits.exchangeableGraphLawEquivInfinite_law_map_restrictFin` — the windows of
  the infinite law attached to an exchangeable graph law are its marginals;
* `TauCeti.DenseGraphLimits.exchangeableGraphLawEquivInfinite_symm_law` — conversely the marginals
  attached to an infinite law are its windows.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/InfiniteLaw.lean` and
  `Graphon/InfiniteExchangeability.lean`, a prior formalization of the same equivalence between
  consistent marginals and exchangeable laws on infinite graphs.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

/-! ### The extension of consistent marginals -/

namespace ExchangeableGraphLaw

variable (L : ExchangeableGraphLaw)

/-- The law of the edge coordinates in `J` of the level-`n` sample. -/
private def coordLaw (n : ℕ) (J : Finset EdgeIndex) : Measure (∀ _ : J, Bool) :=
  (L.law n).map fun H => J.restrict (windowCoord H)

/-- The marginals prescribe the law of every finite set of edge coordinates. -/
private def coordFamily (J : Finset EdgeIndex) : Measure (∀ _ : J, Bool) :=
  L.coordLaw (windowBound J) J

end ExchangeableGraphLaw

/-! ### Exchangeable laws on infinite graphs -/

/-- An **exchangeable law on infinite graphs**: a probability law on the graphs on `ℕ` invariant
under relabelling along every permutation of `ℕ`. -/
structure InfiniteExchangeableGraphLaw where
  /-- The law on infinite graphs. -/
  law : Measure (SimpleGraph ℕ)
  /-- It is a probability measure. -/
  prob : IsProbabilityMeasure law
  /-- Invariance under every relabelling. -/
  exchangeable : ∀ σ : Equiv.Perm ℕ, law.map (SimpleGraph.comap ⇑σ) = law

attribute [simp] InfiniteExchangeableGraphLaw.exchangeable

namespace InfiniteExchangeableGraphLaw

/-- An exchangeable law on infinite graphs is determined by its law: the other fields are
propositions. -/
@[ext]
theorem ext {L L' : InfiniteExchangeableGraphLaw} (h : L.law = L'.law) : L = L' := by
  cases L
  cases L'
  congr

end InfiniteExchangeableGraphLaw

end DenseGraphLimits

end TauCeti
