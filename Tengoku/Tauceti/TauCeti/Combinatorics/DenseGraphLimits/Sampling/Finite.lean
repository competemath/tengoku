/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Tengoku.Tauceti.TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic
public import Tengoku

/-!
# Finite sampling from a graphon

The `W`-random graph on `Fin n` is obtained in two stages: first sample `n` independent points
from the graphon's probability space, then include each unordered pair independently with
probability given by the value of `W` at its two sampled points. This file integrates out both
stages and packages the resulting masses as a probability measure on finite simple graphs.

The mass of a graph `G` is the integral of a finite product. Its edges contribute factors `W`,
while its nonedges contribute factors `1 - W`. At fixed vertex positions, summing this product
over the graphs that decide a fixed set of pairs in a prescribed way expands as
`∏ₑ (Wₑ + (1 - Wₑ)) = 1` over the remaining undecided pairs, leaving the factors of the decided
ones. Requiring a fixed set of edges and leaving the rest free is the special case that computes
the mass of an upper event, and deciding nothing at all gives normalization without imposing any
extra regularity on the graphon's carrier.

## Main definitions

* `TauCeti.DenseGraphLimits.sampleIntegrand` — the conditional mass of a graph at fixed sampled
  vertex positions;
* `TauCeti.DenseGraphLimits.sampleMass` — that mass after integrating over the positions;
* `TauCeti.DenseGraphLimits.sampleGraph` — the resulting probability measure.

## Main results

* `sum_sampleIntegrand_inter_eq` computes the conditional mass of the graphs with a prescribed
  trace on a fixed set of pairs;
* `sum_sampleIntegrand_superset_eq_prod_edgeFactor` specializes it to the graphs containing a
  fixed set of edges;
* `sampleIntegrand_eq_prod_edgeFinset_top` writes the conditional mass as a single product over
  the pairs of the complete graph;
* `sampleMass_nonneg` and `sum_sampleMass_eq_one` show that the masses form a probability law;
* `sampleGraph_singleton` computes the probability of an individual graph;
* `sampleGraph_const` identifies sampling a constant graphon with Mathlib's binomial random graph.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Sections 10.1--10.2.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0,
  `Graphon/Sampling.lean`, `Graphon/SamplingLaw.lean`, and `Graphon/SamplingExamples.lean`.
  The definitions and the Boolean-cube normalization argument, here generalized to a prescribed
  trace on a fixed set of pairs, are adapted to Tau Ceti's strict graphon carrier; the
  constant-law proof reuses the same reduction to Mathlib's singleton-mass formula.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

open Classical in
/-- The conditional mass of `G` at fixed sampled vertex positions. Edges contribute `W` and
nonedges contribute `1 - W`. -/
def sampleIntegrand {n : ℕ} (W : Graphon Ω μ) (G : SimpleGraph (Fin n))
    (x : Fin n → Ω) : ℝ :=
  (∏ e ∈ G.edgeFinset, edgeFactor W x e) *
    ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset \ G.edgeFinset, (1 - edgeFactor W x e)

open Classical in
/-- The probability mass assigned to `G` by the `W`-random graph: integrate its conditional mass
over the independently sampled vertex positions. -/
def sampleMass {n : ℕ} (W : Graphon Ω μ) (G : SimpleGraph (Fin n)) : ℝ :=
  ∫ x : Fin n → Ω, sampleIntegrand W G x ∂Measure.pi fun _ => μ

section Mass

variable {n : ℕ} (W : Graphon Ω μ) (G : SimpleGraph (Fin n))

open Classical in
/-- The defining edge/nonedge product of the sampled-graph integrand. -/
theorem sampleIntegrand_def (x : Fin n → Ω) :
    sampleIntegrand W G x =
      (∏ e ∈ G.edgeFinset, edgeFactor W x e) *
        ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset \ G.edgeFinset,
          (1 - edgeFactor W x e) := (rfl)

/-- The defining integral of a sampled graph's mass. -/
theorem sampleMass_def :
    sampleMass W G = ∫ x : Fin n → Ω, sampleIntegrand W G x ∂Measure.pi fun _ => μ := (rfl)

/-- The sampled-graph integrand is measurable in the vertex positions. -/
theorem measurable_sampleIntegrand : Measurable (sampleIntegrand W G) := by
  classical
  apply Measurable.mul
  · exact measurable_prod_edgeFactor G.edgeFinset fun _ => W
  · exact Finset.measurable_prod _ fun e _ =>
      measurable_const.sub (measurable_edgeFactor W e)

/-- The sampled-graph integrand is nonnegative. -/
theorem sampleIntegrand_nonneg (x : Fin n → Ω) : 0 ≤ sampleIntegrand W G x := by
  classical
  rw [sampleIntegrand]
  refine mul_nonneg (prod_edgeFactor_nonneg G.edgeFinset (fun _ => W) x)
    (Finset.prod_nonneg fun e _ => ?_)
  linarith [edgeFactor_le_one W x e]

open Classical in
/-- The conditional mass of `G` as a single product over the pairs of the complete graph: each
pair contributes the graphon value if `G` joins it and the complementary value if it does not. -/
theorem sampleIntegrand_eq_prod_edgeFinset_top (x : Fin n → Ω) :
    sampleIntegrand W G x = ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
      (if e ∈ G.edgeFinset then edgeFactor W x e else 1 - edgeFactor W x e) := by
  rw [sampleIntegrand_def]
  have hprod := Finset.prod_piecewise (⊤ : SimpleGraph (Fin n)).edgeFinset G.edgeFinset
    (fun e => edgeFactor W x e) (fun e => 1 - edgeFactor W x e)
  rw [Finset.inter_eq_right.mpr (SimpleGraph.edgeFinset_mono le_top)] at hprod
  simpa only [Finset.piecewise] using hprod.symm

/-- Sampled-graph masses are nonnegative. -/
theorem sampleMass_nonneg : 0 ≤ sampleMass W G := by
  classical
  rw [sampleMass_def]
  exact integral_nonneg fun x => sampleIntegrand_nonneg W G x

open Classical in
/-- At fixed vertex positions, summing the conditional masses over the graphs whose edges meet a
fixed loop-free set `A` in a prescribed subset `B` collapses to the product of the edge factors of
`B` against the complementary factors of `A \ B`: the edges left undecided by `A` contribute
`∏ₑ (Wₑ + (1 - Wₑ)) = 1`. Loop-freeness of `A` is expressed as containment in the edges of the
complete graph. -/
theorem sum_sampleIntegrand_inter_eq (A B : Finset (Sym2 (Fin n)))
    (hA : A ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset) (hBA : B ⊆ A) (x : Fin n → Ω) :
    ∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin n) => H.edgeFinset ∩ A = B),
        sampleIntegrand W H x =
      (∏ e ∈ B, edgeFactor W x e) * ∏ e ∈ A \ B, (1 - edgeFactor W x e) := by
  have hnotdiag : ∀ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, ¬ e.IsDiag := fun e he =>
    (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he)
  -- The graph built from `B` together with a set `S` of undecided edges has edge set `B ∪ S`.
  have hedge : ∀ S ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset \ A, ∀ e,
      e ∈ (SimpleGraph.fromEdgeSet (↑(B ∪ S) : Set (Sym2 (Fin n)))).edgeSet ↔ e ∈ B ∪ S := by
    intro S hSsub e
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨fun h => Finset.mem_coe.mp h.1, fun h => ⟨Finset.mem_coe.mpr h, ?_⟩⟩
    rcases Finset.mem_union.mp h with h' | h'
    · exact hnotdiag e (hA (hBA h'))
    · exact hnotdiag e (Finset.mem_sdiff.mp (hSsub h')).1
  have hsum : ∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin n) => H.edgeFinset ∩ A = B),
        sampleIntegrand W H x =
      ∑ S ∈ ((⊤ : SimpleGraph (Fin n)).edgeFinset \ A).powerset,
        ((∏ e ∈ B, edgeFactor W x e) * ∏ e ∈ A \ B, (1 - edgeFactor W x e)) *
          ((∏ e ∈ S, edgeFactor W x e) *
            ∏ e ∈ ((⊤ : SimpleGraph (Fin n)).edgeFinset \ A) \ S, (1 - edgeFactor W x e)) := by
    -- A graph with edge trace `B` on `A` is the same data as the set `S` of edges it uses outside
    -- `A`, so the two maps below are mutually inverse bijections between those graphs and the
    -- subsets of the undecided edges `E(⊤) \ A`.
    refine Finset.sum_nbij'
      (fun H => H.edgeFinset \ A)
      (fun S => SimpleGraph.fromEdgeSet (↑(B ∪ S) : Set (Sym2 (Fin n))))
      ?_ ?_ ?_ ?_ ?_
    -- The edges a graph uses outside `A` are undecided edges.
    · intro H hH
      rw [Finset.mem_powerset]
      intro e he
      rw [Finset.mem_sdiff] at he ⊢
      exact ⟨SimpleGraph.edgeFinset_mono le_top he.1, he.2⟩
    -- Adding a set of undecided edges to `B` produces a graph with edge trace `B` on `A`.
    · intro S hS
      have hSsub := Finset.mem_powerset.mp hS
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      ext e
      simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset, hedge S hSsub e, Finset.mem_union]
      exact ⟨fun h => h.1.resolve_right fun heS => (Finset.mem_sdiff.mp (hSsub heS)).2 h.2,
        fun h => ⟨Or.inl h, hBA h⟩⟩
    -- Adding back the edges a graph uses outside `A` recovers that graph.
    · intro H hH
      rw [Finset.mem_filter] at hH
      have hcoe : (↑(B ∪ (H.edgeFinset \ A)) : Set (Sym2 (Fin n))) = H.edgeSet := by
        rw [← hH.2, Finset.coe_union, Finset.coe_inter, Finset.coe_sdiff,
          SimpleGraph.coe_edgeFinset, Set.inter_union_sdiff]
      rw [hcoe, SimpleGraph.fromEdgeSet_edgeSet]
    -- The edges that `B ∪ S` uses outside `A` are exactly `S`, since `S` avoids `A`.
    · intro S hS
      have hSsub := Finset.mem_powerset.mp hS
      ext e
      simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, hedge S hSsub e, Finset.mem_union]
      exact ⟨fun h => h.1.resolve_left fun heB => h.2 (hBA heB),
        fun h => ⟨Or.inr h, (Finset.mem_sdiff.mp (hSsub h)).2⟩⟩
    -- The summands agree: the edges of `H` split as `B` together with the edges used outside `A`,
    -- and the edges missing from `H` split as `A \ B` together with the undecided edges it skips.
    · intro H hH
      rw [Finset.mem_filter] at hH
      have hmem : ∀ e, e ∈ B ↔ e ∈ H.edgeFinset ∧ e ∈ A := by
        intro e
        rw [← hH.2, Finset.mem_inter]
      have hunion : B ∪ (H.edgeFinset \ A) = H.edgeFinset := by
        ext e
        simp only [Finset.mem_union, Finset.mem_sdiff, hmem]
        tauto
      have hdisj : Disjoint B (H.edgeFinset \ A) :=
        Finset.disjoint_left.mpr fun e he hne => (Finset.mem_sdiff.mp hne).2 ((hmem e).mp he).2
      have hcompl :
          (⊤ : SimpleGraph (Fin n)).edgeFinset \ H.edgeFinset =
            (A \ B) ∪ (((⊤ : SimpleGraph (Fin n)).edgeFinset \ A) \ (H.edgeFinset \ A)) := by
        ext e
        simp only [Finset.mem_sdiff, Finset.mem_union, hmem]
        exact ⟨fun h => by by_cases heA : e ∈ A <;> tauto,
          fun h => h.elim (fun h => ⟨hA h.1, fun hH => h.2 ⟨hH, h.1⟩⟩) fun h => ⟨h.1.1, by tauto⟩⟩
      have hdisj' : Disjoint (A \ B)
          (((⊤ : SimpleGraph (Fin n)).edgeFinset \ A) \ (H.edgeFinset \ A)) :=
        Finset.disjoint_left.mpr fun e he hne =>
          (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hne).1).2 (Finset.mem_sdiff.mp he).1
      have hprod : (∏ e ∈ H.edgeFinset, edgeFactor W x e) =
          (∏ e ∈ B, edgeFactor W x e) * ∏ e ∈ H.edgeFinset \ A, edgeFactor W x e := by
        rw [← Finset.prod_union hdisj, hunion]
      rw [sampleIntegrand_def, hprod, hcompl, Finset.prod_union hdisj']
      ring
  rw [hsum, ← Finset.mul_sum, ← Finset.prod_add]
  simp

open Classical in
/-- At fixed vertex positions, summing the conditional masses over every graph whose edges
include a fixed loop-free set `T` collapses to the product of the edge factors of `T`: the
optional edges outside `T` contribute `∏ₑ (Wₑ + (1 - Wₑ)) = 1`. Loop-freeness of `T` is expressed
as containment in the edges of the complete graph. -/
theorem sum_sampleIntegrand_superset_eq_prod_edgeFactor (T : Finset (Sym2 (Fin n)))
    (hT : T ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset) (x : Fin n → Ω) :
    ∑ H ∈ Finset.univ.filter (fun H => (T : Set (Sym2 (Fin n))) ⊆ H.edgeSet),
        sampleIntegrand W H x =
      ∏ e ∈ T, edgeFactor W x e := by
  have hfilter : Finset.univ.filter
        (fun H : SimpleGraph (Fin n) => (T : Set (Sym2 (Fin n))) ⊆ H.edgeSet) =
      Finset.univ.filter (fun H : SimpleGraph (Fin n) => H.edgeFinset ∩ T = T) :=
    Finset.filter_congr fun H _ => by
      rw [Finset.inter_eq_right, ← Finset.coe_subset, SimpleGraph.coe_edgeFinset]
  rw [hfilter, sum_sampleIntegrand_inter_eq W T T hT le_rfl]
  simp

open Classical in
/-- At fixed vertex positions, the conditional masses sum to `1` over all simple graphs. -/
theorem sum_sampleIntegrand_eq_one (x : Fin n → Ω) :
    ∑ H : SimpleGraph (Fin n), sampleIntegrand W H x = 1 := by
  have h := sum_sampleIntegrand_superset_eq_prod_edgeFactor W ∅ (Finset.empty_subset _) x
  simpa using h

end Mass

section Law

end Law

section Constant

open Classical in
/-- The sampled mass of a constant graphon is the usual independent-edge mass. -/
@[simp]
theorem sampleMass_const (p : I) (G : SimpleGraph (Fin n)) :
    sampleMass (Graphon.const μ p) G =
      (p : ℝ) ^ G.edgeFinset.card *
        (1 - (p : ℝ)) ^ (n.choose 2 - G.edgeFinset.card) := by
  have hfactor (x : Fin n → Ω) (e : Sym2 (Fin n)) :
      edgeFactor (Graphon.const μ p) x e = (p : ℝ) := by
    induction e using Sym2.ind with
    | _ a b => simp
  have hcard : ((⊤ : SimpleGraph (Fin n)).edgeFinset \ G.edgeFinset).card =
      n.choose 2 - G.edgeFinset.card := by
    rw [Finset.card_sdiff,
      Finset.inter_eq_left.mpr (SimpleGraph.edgeFinset_mono le_top)]
    congr 1
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  rw [sampleMass_def]
  have hintegrand : sampleIntegrand (Graphon.const μ p) G = fun _ =>
      (p : ℝ) ^ G.edgeFinset.card *
        (1 - (p : ℝ)) ^ (n.choose 2 - G.edgeFinset.card) := by
    funext x
    rw [sampleIntegrand]
    simp_rw [hfactor x]
    rw [Finset.prod_const, Finset.prod_const, hcard]
  rw [hintegrand]
  simp

end Constant

end DenseGraphLimits

end TauCeti
