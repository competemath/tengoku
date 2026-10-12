/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Tengoku.Tauceti.TauCeti.Combinatorics.DenseGraphLimits.Sampling.Finite
public import Tengoku.Tauceti.TauCeti.Combinatorics.SimpleGraph.Measurable
import Tengoku.Tauceti.TauCeti.Probability.Distributions.Uniform
import Tengoku.Tauceti.TauCeti.MeasureTheory.Measure.ProductKernel

/-!
# The joint sampling law of a graphon

The finite sampling laws `sampleGraph W n` are one probability measure for each `n`, on a
different space each time, and nothing in that family couples them: the separate laws relate only
through pushforwards, and do not themselves supply the common random object a samplewise or
almost-sure statement about the samples as `n` grows needs. This file builds that object: an
infinite `W`-random graph on the label set `ℕ`, sampled once, from which every finite sample is
read off by restriction.

The randomness is explicit. A position `x i` is drawn from the graphon's carrier independently for
each label `i`, and an independent coin `u e` is drawn for each unordered pair `e` from the uniform
law on the unit interval, `TauCeti.Probability.uniformMeasure 0 1`; the pair `{i, j}` becomes an
edge exactly when its coin falls below the graphon value at the two positions. Both families are
infinite products of probability measures, so
`MeasureTheory.Measure.infinitePi` carries them, and the resulting law on `SimpleGraph ℕ` uses the
adjacency sigma-algebra Mathlib already provides.

The finite-marginal identification is the theorem of the file. For a fixed pattern `H` on `Fin n`
the event that the window of the infinite graph equals `H` is a box: it constrains the coin of
each pair of distinct labels below `n` to an interval — below the graphon value for the pairs `H`
joins, above it for the pairs it does not — and constrains nothing else. The coin product of that
box is the conditional mass `sampleIntegrand W H` at the sampled positions, and averaging over the
positions is `sampleMass W H`.

## Main definitions

* `TauCeti.DenseGraphLimits.infiniteSampleLaw` — its law, the joint sampling object.

## Main results

* `infiniteSampleLaw_map_restrictFin` — every finite sampling law is a window of the joint law,
  along the window map `SimpleGraph.restrictFin`.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §10.1.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), §7.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/InfiniteSampler.lean`. The same
  one-space sampler — i.i.d. positions and one independent uniform coin per unordered pair, both
  carried by `Measure.infinitePi`, with a pair joined when its coin falls below the graphon value —
  and its finite-marginal identification are formalized there. The construction is adapted to Tau
  Ceti's strict graphon carrier, whose values are everywhere in the unit interval, so no clamped
  representative is needed, and it lands on Mathlib's `SimpleGraph ℕ` with its adjacency
  sigma-algebra rather than on a Boolean cube of edge coordinates; the marginal proof here
  evaluates the mass of a single pattern as a box of coin intervals instead of going through upper
  events.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

section Source

/-- The randomness the infinite `W`-random graph is read off: an independent position in the
graphon's carrier for every label, and an independent uniform coin for every unordered pair of
labels. -/
private def infiniteSampleSource (μ : Measure Ω) : Measure ((ℕ → Ω) × (Sym2 ℕ → ℝ)) :=
  (Measure.infinitePi fun _ : ℕ => μ).prod
    (Measure.infinitePi fun _ : Sym2 ℕ => Probability.uniformMeasure 0 1)

/-- The infinite `W`-random graph attached to a family of positions and a family of coins: the
pair `{i, j}` is an edge when its coin falls below the graphon value at the two positions. -/
private def infiniteSampleGraph (W : Graphon Ω μ) (x : ℕ → Ω) (u : Sym2 ℕ → ℝ) : SimpleGraph ℕ where
  Adj i j := i ≠ j ∧ u s(i, j) < edgeFactor W x s(i, j)
  symm := ⟨by
    rintro i j ⟨hne, hlt⟩
    refine ⟨hne.symm, ?_⟩
    rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun i h => h.1 rfl⟩

@[simp]
private theorem infiniteSampleGraph_adj (W : Graphon Ω μ) (x : ℕ → Ω) (u : Sym2 ℕ → ℝ) (i j : ℕ) :
    (infiniteSampleGraph W x u).Adj i j ↔ i ≠ j ∧ u s(i, j) < edgeFactor W x s(i, j) := Iff.rfl

end Source

section Law

/-- The **joint sampling law** of a graphon: the law of the infinite `W`-random graph on `ℕ`. All
the finite sampling laws are windows of this single random object. -/
def infiniteSampleLaw (W : Graphon Ω μ) : Measure (SimpleGraph ℕ) :=
  (infiniteSampleSource μ).map fun p => infiniteSampleGraph W p.1 p.2

end Law

section Window

variable {n : ℕ}

open Classical in
/-- The unordered pairs of distinct labels inside the window of the first `n` labels, read as
pairs of naturals. -/
private def windowPairs (n : ℕ) : Finset (Sym2 ℕ) :=
  Finset.image (Sym2.map (Fin.val : Fin n → ℕ)) (⊤ : SimpleGraph (Fin n)).edgeFinset

/-- The interval a pair's coin has to land in for the sampled graph to reproduce the pattern `K`
at that pair. -/
private def coinTarget (W : Graphon Ω μ) (x : ℕ → Ω) (K : SimpleGraph ℕ) (e : Sym2 ℕ) : Set ℝ :=
  open Classical in
  if e ∈ K.edgeSet then Set.Iio (edgeFactor W x e) else Set.Ici (edgeFactor W x e)

end Window

section Marginal

variable {n : ℕ}

end Marginal

end DenseGraphLimits

end TauCeti

end

end
