/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Tengoku.Tauceti.TauCeti.Combinatorics.DenseGraphLimits.Sampling.Finite
public import Tengoku.Tauceti.TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Oscillation
public import Tengoku.Tauceti.TauCeti.Probability.Distributions.Uniform
public import Tengoku.Tauceti.TauCeti.Combinatorics.SimpleGraph.Measurable

/-!
# The padded vertex exposure of a sampled graph

The finite sampling law `sampleGraph W n` is defined by its masses, so it does not present the
sampled graph as a function of independent coordinates. A bounded-differences inequality needs
exactly such a presentation: a product of independent coordinates, together with a bound on how
much the estimator moves when one coordinate changes. Changing one sampled vertex position alone
is not such a coordinate, because the edges at that vertex also carry their own independent
randomness.

The *padded exposure* supplies the product structure. Each of the `n` vertices carries its
position in the graphon's carrier together with a full row of `n` independent uniform coins, and
the exposure source is the `n`-fold product of these vertex coordinates. The edge `{i, j}` reads
its coin from one designated row: row `max i j`, column `min i j`, and it is present when that coin
falls below the graphon value at the two positions. Every coin on or above the diagonal is
padding that no edge reads. Since every edge reads a coin carried by one of its endpoints,
changing the coordinate of one vertex changes only the pairs at that vertex.

The two results of the file make this a genuine representation of `G(n, W)`:

* the law identification: the exposure source pushed through the exposed graph is the finite
  sampling law. At fixed positions the event that the exposed graph is a prescribed pattern is a
  box in the coins, whose uniform product is the conditional mass `sampleIntegrand W H`;
* the oscillation bound: changing one vertex coordinate moves the ordinary homomorphism density
  of the exposed graph by at most `|V(F)| / n`.

## Main definitions

* `TauCeti.DenseGraphLimits.exposureMeasure` — the product source of positions and coin rows;
* `TauCeti.DenseGraphLimits.exposedSample` — the graph read off an exposure.

## Main results

* `exposedSample_adj` — the designated-row rule for the edges;
* `map_exposedSample` — the exposure source induces the finite sampling law;
* `exposedSample_update_adj_iff` — updating one vertex coordinate only changes pairs at it;
* `abs_homDensityFin_exposedSample_update_le` — the bounded-differences estimate.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §10.1.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/SampleExposure.lean`. The
  padded exposure source, the designated-row convention, the law identification and the `q / n`
  oscillation bound are formalized there. The construction here is adapted to Tau Ceti's strict
  graphon carrier and uses the uniform coin `TauCeti.Probability.uniformMeasure 0 1` and the strict
  comparison of the joint sampler `infiniteSampleLaw`; the law identification evaluates the mass of
  a single pattern as a box of coin intervals, and the oscillation bound is derived from a
  host-graph statement, `SimpleGraph.abs_homDensityFin_sub_le_of_adj_iff`.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

section Source

variable (μ) in
/-- The **exposure source** of the `n`-vertex sampled graph: `n` independent vertex coordinates,
each a position drawn from `μ` together with a row of `n` independent uniform coins on the unit
interval. -/
def exposureMeasure (n : ℕ) : Measure (Fin n → Ω × (Fin n → ℝ)) :=
  Measure.pi fun _ : Fin n => μ.prod (Measure.pi fun _ : Fin n => Probability.uniformMeasure 0 1)

omit [IsProbabilityMeasure μ] in
variable (μ) in
/-- The defining product of the exposure source. -/
theorem exposureMeasure_def (n : ℕ) :
    exposureMeasure μ n =
      Measure.pi fun _ : Fin n =>
        μ.prod (Measure.pi fun _ : Fin n => Probability.uniformMeasure 0 1) := (rfl)

end Source

section Graph

variable {n : ℕ}

/-- The **exposed sampled graph**: the pair `{i, j}` is an edge exactly when the coin in row
`max i j`, column `min i j` falls below the graphon value at the two positions. Every edge reads a
coin carried by one of its endpoints, so changing one vertex coordinate changes only the pairs at
that vertex. -/
def exposedSample (W : Graphon Ω μ) (x : Fin n → Ω × (Fin n → ℝ)) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (x (max i j)).2 (min i j) < W (x i).1 (x j).1
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [max_comm, min_comm, W.symm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **The designated-row rule.** The edge `{i, j}` of the exposed graph is present exactly when the
coin in row `max i j`, column `min i j` falls below the graphon value at the two positions. -/
@[simp]
theorem exposedSample_adj (W : Graphon Ω μ) (x : Fin n → Ω × (Fin n → ℝ)) (i j : Fin n) :
    (exposedSample W x).Adj i j ↔ i ≠ j ∧ (x (max i j)).2 (min i j) < W (x i).1 (x j).1 :=
  Iff.rfl

/-- The exposed graph depends measurably on the exposure. -/
theorem measurable_exposedSample (W : Graphon Ω μ) :
    Measurable (exposedSample (n := n) W) := by
  rw [SimpleGraph.measurable_iff_adj]
  intro i j
  refine measurableSet_setOfPred.mp ?_
  by_cases hij : i = j
  · simp [hij]
  · have hcoin : Measurable fun x : Fin n → Ω × (Fin n → ℝ) => (x (max i j)).2 (min i j) :=
      (measurable_pi_apply _).comp (measurable_snd.comp (measurable_pi_apply _))
    have hvalue : Measurable fun x : Fin n → Ω × (Fin n → ℝ) => W (x i).1 (x j).1 :=
      W.measurable.comp ((measurable_fst.comp (measurable_pi_apply _)).prodMk
        (measurable_fst.comp (measurable_pi_apply _)))
    simpa [hij] using measurableSet_lt hcoin hvalue

/-- Updating the coordinate of the vertex `i` leaves every pair avoiding `i` unchanged: such a pair
reads its positions and its coin from vertices other than `i`. -/
theorem exposedSample_update_adj_iff (W : Graphon Ω μ) (x : Fin n → Ω × (Fin n → ℝ)) (i : Fin n)
    (y : Ω × (Fin n → ℝ)) {a b : Fin n} (ha : a ≠ i) (hb : b ≠ i) :
    (exposedSample W (Function.update x i y)).Adj a b ↔ (exposedSample W x).Adj a b := by
  have hmax : max a b ≠ i := by
    rcases max_choice a b with h | h <;> rw [h] <;> assumption
  simp only [exposedSample_adj, Function.update_of_ne ha, Function.update_of_ne hb,
    Function.update_of_ne hmax]

end Graph

section Law

variable {n : ℕ}

open Classical in
/-- The coins that make the exposed graph equal to the pattern `H` at the pair read from row `r`,
column `s`. Only the coins below the diagonal are read; the others are padding and unconstrained. -/
private def coinBox (W : Graphon Ω μ) (y : Fin n → Ω) (H : SimpleGraph (Fin n)) (r s : Fin n) :
    Set ℝ :=
  if s < r then {t | t < W (y r) (y s) ↔ H.Adj r s} else Set.univ

end Law

section Oscillation

variable {V : Type*} [Fintype V]

/-- **The bounded-differences estimate of the exposure.** Changing the coordinate of one exposed
vertex moves the ordinary homomorphism density of the exposed graph by at most `|V(F)| / n`. -/
theorem abs_homDensityFin_exposedSample_update_le (F : SimpleGraph V) (W : Graphon Ω μ) {n : ℕ}
    (x : Fin n → Ω × (Fin n → ℝ)) (i : Fin n) (y : Ω × (Fin n → ℝ)) :
    |homDensityFin F (exposedSample W (Function.update x i y)) -
        homDensityFin F (exposedSample W x)| ≤ (Fintype.card V : ℝ) / n := by
  simpa using F.abs_homDensityFin_sub_le_of_adj_iff i
    fun a b ha hb => exposedSample_update_adj_iff W x i y ha hb

end Oscillation

end DenseGraphLimits

end TauCeti
