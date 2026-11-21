/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.MixedTailChaining

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Countable chaining: the summable-limit step

This file formalizes the passage from the finite telescoping argument in
`FiniteChaining` and `MixedTailChaining` to countably many levels.  The
successive projections are assumed to converge pointwise to the original
process value, expressed by convergence to zero of the final remainder.
Summable nonnegative thresholds then turn the finite telescope into an
infinite one.

The large-deviation event remains existential, rather than being written as
the upper tail of a supremum.  Thus no measurability of an uncountable
supremum is silently assumed.  Every level has a finite edge graph, and the
probability estimate is a countable union bound with an explicit `tsum` of
the level costs.

This is only the summable, countable-limit step of chaining.  It does not
construct entropy-optimal nets, prove separability of a process, or claim a
Dudley or Dirksen theorem.
-/

open Filter Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {Omega T : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The bad-increment event over countably many finite edge graphs.-/
def countableChainingEdgeEvent (Z : Omega → T → ℝ)
    (edges : ℕ → Finset (T × T)) (threshold : ℕ → ℝ) : Set Omega :=
  ⋃ k, ⋃ e ∈ edges k,
    {omega | threshold k < |Z omega e.1 - Z omega e.2|}

/-- The full-product bad-increment event over countably many pairs of
adjacent finite nets.  The edge-graph version is usually sharper.-/
def countableChainingIncrementEvent (Z : Omega → T → ℝ)
    (N : ℕ → Finset T) (threshold : ℕ → ℝ) : Set Omega :=
  ⋃ k, ⋃ u ∈ N (k + 1), ⋃ v ∈ N k,
    {omega | threshold k < |Z omega u - Z omega v|}

/-- Simultaneous choice of projections onto a countable family of finite
nets.  No measurability of the projections is needed in the chaining bounds,
because all bad events are enlarged to unions over the finite nets or edge
graphs.
@isnad1 id=ex.1h3v.s6.7f0747bae71e from=translated src=- shape=9196d4dd vocab=4bc95c1e
-/
theorem exists_countableNetProjections [PseudoMetricSpace T] [Nonempty T]
    (N : ℕ → Finset T) (eps : ℕ → ℝ)
    (hnet : ∀ k t, ∃ u ∈ N k, dist t u ≤ eps k) :
    ∃ proj : ℕ → T → T,
      (∀ k t, proj k t ∈ N k) ∧
      ∀ k t, dist t (proj k t) ≤ eps k := by
  classical
  let proj : ℕ → T → T := fun k t ↦ Classical.choose (hnet k t)
  refine ⟨proj, ?_, ?_⟩
  · intro k t
    exact (Classical.choose_spec (hnet k t)).1
  · intro k t
    exact (Classical.choose_spec (hnet k t)).2

omit [MeasurableSpace Omega] in
/-- Infinite telescoping bound.  Pointwise convergence of the final
remainder and summability of the increment majorants are the exact extra
hypotheses needed beyond the finite telescope.
@isnad1 id=le.3h7v.s7.f973e6c6c9cb from=translated src=- shape=4b9dfa29 vocab=a515cec8
-/
theorem abs_process_le_countableChainingSum
    (Z : Omega → T → ℝ) (proj : ℕ → T → T)
    (threshold : ℕ → ℝ) (omega : Omega) (t : T)
    (hthreshold : ∀ k,
      |Z omega (proj (k + 1) t) - Z omega (proj k t)| ≤ threshold k)
    (hsummable : Summable threshold)
    (hremainder : Tendsto
      (fun m ↦ |Z omega t - Z omega (proj m t)|) atTop (nhds 0)) :
    |Z omega t| ≤ |Z omega (proj 0 t)| + ∑' k, threshold k := by
  have hprojLimit :
      Tendsto (fun m ↦ Z omega (proj m t)) atTop (nhds (Z omega t)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    simpa only [Real.dist_eq, abs_sub_comm] using hremainder
  have hincrements : ∀ k,
      dist (Z omega (proj k t)) (Z omega (proj (k + 1) t)) ≤ threshold k := by
    intro k
    simpa only [Real.dist_eq, abs_sub_comm] using hthreshold k
  have hdistance :
      dist (Z omega (proj 0 t)) (Z omega t) ≤ ∑' k, threshold k :=
    dist_le_tsum_of_dist_le_of_tendsto₀ threshold hincrements hsummable hprojLimit
  calc
    |Z omega t| =
        |Z omega (proj 0 t) +
          (Z omega t - Z omega (proj 0 t))| := by ring_nf
    _ ≤ |Z omega (proj 0 t)| +
          |Z omega t - Z omega (proj 0 t)| := abs_add_le _ _
    _ ≤ |Z omega (proj 0 t)| + ∑' k, threshold k := by
      apply add_le_add_right
      simpa only [Real.dist_eq, abs_sub_comm] using hdistance

omit [MeasurableSpace Omega] in
/-- Deterministic countable chaining inclusion for finite edge graphs at
each level.  Summability of the thresholds permits the infinite telescope;
their effective nonnegativity follows on every traversed edge from the
increment bounds.  A large deviation therefore forces either a bad
coarsest-net value or one bad increment at a finite level.
@isnad1 id=le.4h8v.s7.fe055ed94805 from=translated src=- shape=ad72b5a2 vocab=83a03961
-/
theorem countableChaining_largeDeviation_subset_edges
    (Z : Omega → T → ℝ) (N0 : Finset T)
    (edges : ℕ → Finset (T × T)) (proj : ℕ → T → T)
    (threshold : ℕ → ℝ) (baseThreshold : ℝ)
    (hbase : ∀ t, proj 0 t ∈ N0)
    (hedge : ∀ k t, (proj (k + 1) t, proj k t) ∈ edges k)
    (hthresholdSummable : Summable threshold)
    (hremainder : ∀ omega t, Tendsto
      (fun m ↦ |Z omega t - Z omega (proj m t)|) atTop (nhds 0)) :
    {omega | ∃ t,
        baseThreshold + (∑' k, threshold k) < |Z omega t|} ⊆
      finiteChainingBaseEvent Z N0 baseThreshold ∪
        countableChainingEdgeEvent Z edges threshold := by
  classical
  intro omega homega
  obtain ⟨t, ht⟩ := homega
  by_cases hbaseBad : omega ∈ finiteChainingBaseEvent Z N0 baseThreshold
  · exact Or.inl hbaseBad
  right
  by_contra hedgeBad
  have hbase_le : |Z omega (proj 0 t)| ≤ baseThreshold := by
    by_contra hbad
    apply hbaseBad
    refine Set.mem_iUnion.2 ⟨proj 0 t, Set.mem_iUnion.2 ⟨hbase t, ?_⟩⟩
    exact lt_of_not_ge hbad
  have hincrement_le : ∀ k,
      |Z omega (proj (k + 1) t) - Z omega (proj k t)| ≤ threshold k := by
    intro k
    by_contra hbad
    apply hedgeBad
    refine Set.mem_iUnion.2 ⟨k,
      Set.mem_iUnion.2 ⟨(proj (k + 1) t, proj k t),
        Set.mem_iUnion.2 ⟨hedge k t, ?_⟩⟩⟩
    exact lt_of_not_ge hbad
  have hchain := abs_process_le_countableChainingSum
    Z proj threshold omega t hincrement_le hthresholdSummable
      (hremainder omega t)
  have htotal : |Z omega t| ≤
      baseThreshold + ∑' k, threshold k :=
    hchain.trans (add_le_add hbase_le le_rfl)
  exact (not_lt_of_ge htotal) ht

/-- Countable subadditivity for `Measure.real`, under the explicit
summability hypothesis needed to keep the right-hand side finite.  The
corresponding `ℝ≥0∞` statement `measure_iUnion_le` needs no such hypothesis.
@isnad1 id=le.1h3v.s6.fa4cd9399772 from=translated src=- shape=f8989b3a vocab=05eb3f76
-/
theorem measureReal_iUnion_nat_le_of_summable [IsFiniteMeasure mu]
    (A : ℕ → Set Omega)
    (hA : Summable fun k ↦ mu.real (A k)) :
    mu.real (⋃ k, A k) ≤ ∑' k, mu.real (A k) := by
  let c : ℕ → ℝ≥0 := fun k ↦ (mu (A k)).toNNReal
  have hcReal : (fun k ↦ (c k : ℝ)) = fun k ↦ mu.real (A k) := by
    funext k
    exact ENNReal.coe_toNNReal_eq_toReal (mu (A k))
  have hc : Summable c := by
    rw [← NNReal.summable_coe]
    simpa only [hcReal] using hA
  have hterm : ∀ k, (c k : ℝ≥0∞) = mu (A k) := by
    intro k
    exact ENNReal.coe_toNNReal (measure_ne_top mu (A k))
  have hsumFinite : (∑' k, mu (A k)) ≠ ∞ := by
    have hsumEq :
        (∑' k, mu (A k)) = ((∑' k, c k : ℝ≥0) : ℝ≥0∞) := by
      calc
        (∑' k, mu (A k)) = ∑' k, (c k : ℝ≥0∞) :=
          tsum_congr fun k ↦ (hterm k).symm
        _ = ((∑' k, c k : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_tsum hc).symm
    rw [hsumEq]
    exact ENNReal.coe_ne_top
  have hmeasure := measure_iUnion_le (μ := mu) A
  have htoReal :
      (mu (⋃ k, A k)).toReal ≤ (∑' k, mu (A k)).toReal :=
    (ENNReal.toReal_le_toReal (measure_ne_top mu _) hsumFinite).2 hmeasure
  rw [ENNReal.tsum_toReal_eq (fun k ↦ measure_ne_top mu (A k))] at htoReal
  simpa only [measureReal_def] using htoReal

/-- Countable chaining with arbitrary pointwise edge-tail bounds, stated in
the canonical `ℝ≥0∞` measure scale.  This form needs no measurability or
summability assumption on the costs: countable subadditivity is valid even
when the right-hand side is infinite.
@isnad1 id=le.6h11v.s8.20810dcd587e from=translated src=- shape=a0fa2035 vocab=8d477eeb
-/
theorem measure_countableChaining_edges_largeDeviation_le
    (Z : Omega → T → ℝ) (N0 : Finset T)
    (edges : ℕ → Finset (T × T)) (proj : ℕ → T → T)
    (threshold : ℕ → ℝ) (delta : ℕ → ℝ≥0∞)
    (baseThreshold : ℝ) (delta0 : ℝ≥0∞)
    (hbase : ∀ t, proj 0 t ∈ N0)
    (hedge : ∀ k t, (proj (k + 1) t, proj k t) ∈ edges k)
    (hthresholdSummable : Summable threshold)
    (hremainder : ∀ omega t, Tendsto
      (fun m ↦ |Z omega t - Z omega (proj m t)|) atTop (nhds 0))
    (hbaseTail : ∀ u ∈ N0,
      mu {omega | baseThreshold < |Z omega u|} ≤ delta0)
    (hedgeTail : ∀ k, ∀ e ∈ edges k,
      mu {omega | threshold k < |Z omega e.1 - Z omega e.2|} ≤ delta k) :
    mu {omega | ∃ t,
        baseThreshold + (∑' k, threshold k) < |Z omega t|} ≤
      N0.card * delta0 +
        ∑' k, (edges k).card * delta k := by
  classical
  let Base : Set Omega := finiteChainingBaseEvent Z N0 baseThreshold
  let Level : ℕ → Set Omega := fun k ↦
    ⋃ e ∈ edges k,
      {omega | threshold k < |Z omega e.1 - Z omega e.2|}
  have hsubset :
      {omega | ∃ t,
          baseThreshold + (∑' k, threshold k) < |Z omega t|} ⊆
        Base ∪ ⋃ k, Level k := by
    simpa only [Base, Level, countableChainingEdgeEvent] using
      countableChaining_largeDeviation_subset_edges
        Z N0 edges proj threshold baseThreshold hbase hedge
          hthresholdSummable hremainder
  have hBase : mu Base ≤ N0.card * delta0 := by
    calc
      mu Base ≤ ∑ u ∈ N0,
          mu {omega | baseThreshold < |Z omega u|} := by
        simpa only [Base, finiteChainingBaseEvent] using
          (measure_biUnion_finset_le (μ := mu) N0
            (fun u ↦ {omega | baseThreshold < |Z omega u|}))
      _ ≤ ∑ _u ∈ N0, delta0 := Finset.sum_le_sum hbaseTail
      _ = N0.card * delta0 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hLevel : ∀ k, mu (Level k) ≤ (edges k).card * delta k := by
    intro k
    calc
      mu (Level k) ≤ ∑ e ∈ edges k,
          mu {omega | threshold k < |Z omega e.1 - Z omega e.2|} := by
        simpa only [Level] using
          (measure_biUnion_finset_le (μ := mu) (edges k)
            (fun e ↦
              {omega | threshold k < |Z omega e.1 - Z omega e.2|}))
      _ ≤ ∑ _e ∈ edges k, delta k :=
        Finset.sum_le_sum fun e he ↦ hedgeTail k e he
      _ = (edges k).card * delta k := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    mu {omega | ∃ t,
        baseThreshold + (∑' k, threshold k) < |Z omega t|} ≤
        mu (Base ∪ ⋃ k, Level k) := measure_mono hsubset
    _ ≤ mu Base + mu (⋃ k, Level k) := measure_union_le _ _
    _ ≤ mu Base + ∑' k, mu (Level k) :=
      add_le_add_right (measure_iUnion_le Level) _
    _ ≤ N0.card * delta0 +
        ∑' k, (edges k).card * delta k :=
      add_le_add hBase (ENNReal.tsum_le_tsum hLevel)

/-- Real-valued countable chaining bound.  In contrast with the `ℝ≥0∞`
version, summability of the level costs is explicit and essential: it is what
allows `Measure.real` to commute with the countable upper bound.  Event
measurability is not needed for this one-sided estimate, since countable
subadditivity applies to arbitrary sets.
@isnad1 id=le.7h11v.s8.23bd4abba1f2 from=translated src=- shape=d8245f47 vocab=4fc4c2fe
-/
theorem measureReal_countableChaining_edges_largeDeviation_le
    [IsFiniteMeasure mu]
    (Z : Omega → T → ℝ) (N0 : Finset T)
    (edges : ℕ → Finset (T × T)) (proj : ℕ → T → T)
    (threshold delta : ℕ → ℝ)
    (baseThreshold delta0 : ℝ)
    (hbase : ∀ t, proj 0 t ∈ N0)
    (hedge : ∀ k t, (proj (k + 1) t, proj k t) ∈ edges k)
    (hthresholdSummable : Summable threshold)
    (hremainder : ∀ omega t, Tendsto
      (fun m ↦ |Z omega t - Z omega (proj m t)|) atTop (nhds 0))
    (hcostSummable : Summable fun k ↦ (edges k).card * delta k)
    (hbaseTail : ∀ u ∈ N0,
      mu.real {omega | baseThreshold < |Z omega u|} ≤ delta0)
    (hedgeTail : ∀ k, ∀ e ∈ edges k,
      mu.real {omega | threshold k < |Z omega e.1 - Z omega e.2|} ≤
        delta k) :
    mu.real {omega | ∃ t,
        baseThreshold + (∑' k, threshold k) < |Z omega t|} ≤
      N0.card * delta0 +
        ∑' k, (edges k).card * delta k := by
  classical
  let Base : Set Omega := finiteChainingBaseEvent Z N0 baseThreshold
  let Level : ℕ → Set Omega := fun k ↦
    ⋃ e ∈ edges k,
      {omega | threshold k < |Z omega e.1 - Z omega e.2|}
  have hsubset :
      {omega | ∃ t,
          baseThreshold + (∑' k, threshold k) < |Z omega t|} ⊆
        Base ∪ ⋃ k, Level k := by
    simpa only [Base, Level, countableChainingEdgeEvent] using
      countableChaining_largeDeviation_subset_edges
        Z N0 edges proj threshold baseThreshold hbase hedge
          hthresholdSummable hremainder
  have hBase : mu.real Base ≤ N0.card * delta0 := by
    calc
      mu.real Base ≤ ∑ u ∈ N0,
          mu.real {omega | baseThreshold < |Z omega u|} := by
        simpa only [Base, finiteChainingBaseEvent] using
          (measureReal_biUnion_finset_le (μ := mu) N0
            (fun u ↦ {omega | baseThreshold < |Z omega u|}))
      _ ≤ ∑ _u ∈ N0, delta0 := Finset.sum_le_sum hbaseTail
      _ = N0.card * delta0 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hLevel : ∀ k,
      mu.real (Level k) ≤ (edges k).card * delta k := by
    intro k
    calc
      mu.real (Level k) ≤ ∑ e ∈ edges k,
          mu.real {omega |
            threshold k < |Z omega e.1 - Z omega e.2|} := by
        simpa only [Level] using
          (measureReal_biUnion_finset_le (μ := mu) (edges k)
            (fun e ↦
              {omega | threshold k < |Z omega e.1 - Z omega e.2|}))
      _ ≤ ∑ _e ∈ edges k, delta k :=
        Finset.sum_le_sum fun e he ↦ hedgeTail k e he
      _ = (edges k).card * delta k := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hLevelSummable : Summable fun k ↦ mu.real (Level k) :=
    Summable.of_nonneg_of_le
      (fun _ ↦ measureReal_nonneg) hLevel hcostSummable
  have hIncr : mu.real (⋃ k, Level k) ≤
      ∑' k, (edges k).card * delta k := by
    calc
      mu.real (⋃ k, Level k) ≤ ∑' k, mu.real (Level k) :=
        measureReal_iUnion_nat_le_of_summable Level hLevelSummable
      _ ≤ ∑' k, (edges k).card * delta k :=
        Summable.tsum_le_tsum hLevel hLevelSummable hcostSummable
  calc
    mu.real {omega | ∃ t,
        baseThreshold + (∑' k, threshold k) < |Z omega t|} ≤
        mu.real (Base ∪ ⋃ k, Level k) := measureReal_mono hsubset
    _ ≤ mu.real Base + mu.real (⋃ k, Level k) :=
      measureReal_union_le _ _
    _ ≤ N0.card * delta0 +
        ∑' k, (edges k).card * delta k := add_le_add hBase hIncr

/-- Countable mixed-tail Bernstein chaining over finite edge graphs.  The
variance and scale proxies may depend on both endpoints, while `V k` and
`B k` are deterministic levelwise envelopes.  Both the threshold series and
the confidence-cost series are required to be summable explicitly.

No independence between different edges is used.  The `HasBernsteinMGF`
certificates supply the scalar measurability and tail estimates; the
existential large-deviation event avoids any measurability assumption on an
uncountable supremum.
@isnad1 id=le.15h17v.s9.bb6b3e584dfe from=translated src=- shape=6edff444 vocab=ae7f2f23
-/
theorem measureReal_countableChaining_edges_largeDeviation_le_of_bernstein
    [IsProbabilityMeasure mu]
    (Z : Omega → T → ℝ) (N0 : Finset T)
    (edges : ℕ → Finset (T × T)) (proj : ℕ → T → T)
    (baseVariance baseScale : T → ℝ≥0)
    (edgeVariance edgeScale : ℕ → T → T → ℝ≥0)
    (V B : ℕ → ℝ≥0) (V0 B0 : ℝ≥0)
    (x : ℕ → ℝ) (x0 : ℝ)
    (hbase : ∀ t, proj 0 t ∈ N0)
    (hedge : ∀ k t, (proj (k + 1) t, proj k t) ∈ edges k)
    (hremainder : ∀ omega t, Tendsto
      (fun m ↦ |Z omega t - Z omega (proj m t)|) atTop (nhds 0))
    (hx0 : 0 ≤ x0) (hx : ∀ k, 0 ≤ x k)
    (hthresholdSummable : Summable fun k ↦
      bernsteinMixedThreshold (V k : ℝ) (B k : ℝ) (x k))
    (hcostSummable : Summable fun k ↦
      (edges k).card * (2 * exp (-x k)))
    (hbaseVariance : ∀ u ∈ N0, 0 < (baseVariance u : ℝ))
    (hedgeVariance : ∀ k, ∀ e ∈ edges k,
      0 < (edgeVariance k e.1 e.2 : ℝ))
    (hbaseVariance_le : ∀ u ∈ N0, baseVariance u ≤ V0)
    (hbaseScale_le : ∀ u ∈ N0, baseScale u ≤ B0)
    (hedgeVariance_le : ∀ k, ∀ e ∈ edges k,
      edgeVariance k e.1 e.2 ≤ V k)
    (hedgeScale_le : ∀ k, ∀ e ∈ edges k,
      edgeScale k e.1 e.2 ≤ B k)
    (hbaseBernstein : ∀ u ∈ N0,
      HasBernsteinMGF (fun omega ↦ Z omega u)
        (baseVariance u) (baseScale u) mu)
    (hedgeBernstein : ∀ k, ∀ e ∈ edges k,
      HasBernsteinMGF (fun omega ↦ Z omega e.1 - Z omega e.2)
        (edgeVariance k e.1 e.2) (edgeScale k e.1 e.2) mu) :
    mu.real {omega | ∃ t,
        bernsteinMixedThreshold (V0 : ℝ) (B0 : ℝ) x0 +
            (∑' k, bernsteinMixedThreshold
              (V k : ℝ) (B k : ℝ) (x k)) < |Z omega t|} ≤
      N0.card * (2 * exp (-x0)) +
        ∑' k, (edges k).card * (2 * exp (-x k)) := by
  apply measureReal_countableChaining_edges_largeDeviation_le
    Z N0 edges proj
      (fun k ↦ bernsteinMixedThreshold (V k : ℝ) (B k : ℝ) (x k))
      (fun k ↦ 2 * exp (-x k))
      (bernsteinMixedThreshold (V0 : ℝ) (B0 : ℝ) x0)
      (2 * exp (-x0)) hbase hedge hthresholdSummable hremainder
      hcostSummable
  · intro u hu
    have hthreshold :
        bernsteinMixedThreshold (baseVariance u : ℝ)
            (baseScale u : ℝ) x0 ≤
          bernsteinMixedThreshold (V0 : ℝ) (B0 : ℝ) x0 :=
      bernsteinMixedThreshold_mono
        (by exact_mod_cast hbaseVariance_le u hu)
        (by exact_mod_cast hbaseScale_le u hu) hx0
    have htail :=
      (hbaseBernstein u hu).measureReal_abs_gt_mixedThreshold_le
        hx0 (hbaseVariance u hu)
    exact (measureReal_mono (by
      intro omega homega
      exact lt_of_le_of_lt hthreshold homega)).trans htail
  · intro k e he
    have hthreshold :
        bernsteinMixedThreshold (edgeVariance k e.1 e.2 : ℝ)
            (edgeScale k e.1 e.2 : ℝ) (x k) ≤
          bernsteinMixedThreshold (V k : ℝ) (B k : ℝ) (x k) :=
      bernsteinMixedThreshold_mono
        (by exact_mod_cast hedgeVariance_le k e he)
        (by exact_mod_cast hedgeScale_le k e he) (hx k)
    have htail :=
      (hedgeBernstein k e he).measureReal_abs_gt_mixedThreshold_le
        (hx k) (hedgeVariance k e he)
    exact (measureReal_mono (by
      intro omega homega
      exact lt_of_le_of_lt hthreshold homega)).trans htail

/-- Anchored form of countable Bernstein chaining.  When the process
vanishes on the coarsest net, neither a base MGF certificate nor a base
confidence cost is required.
@isnad1 id=le.11h12v.s9.8fc895dbfbb5 from=translated src=- shape=7ed2506b vocab=ae7f2f23
-/
theorem measureReal_countableChaining_edges_largeDeviation_le_of_bernstein_anchored
    [IsProbabilityMeasure mu]
    (Z : Omega → T → ℝ) (N0 : Finset T)
    (edges : ℕ → Finset (T × T)) (proj : ℕ → T → T)
    (edgeVariance edgeScale : ℕ → T → T → ℝ≥0)
    (V B : ℕ → ℝ≥0) (x : ℕ → ℝ)
    (hbase : ∀ t, proj 0 t ∈ N0)
    (hedge : ∀ k t, (proj (k + 1) t, proj k t) ∈ edges k)
    (hremainder : ∀ omega t, Tendsto
      (fun m ↦ |Z omega t - Z omega (proj m t)|) atTop (nhds 0))
    (hbaseZero : ∀ omega, ∀ u ∈ N0, Z omega u = 0)
    (hx : ∀ k, 0 ≤ x k)
    (hthresholdSummable : Summable fun k ↦
      bernsteinMixedThreshold (V k : ℝ) (B k : ℝ) (x k))
    (hcostSummable : Summable fun k ↦
      (edges k).card * (2 * exp (-x k)))
    (hedgeVariance : ∀ k, ∀ e ∈ edges k,
      0 < (edgeVariance k e.1 e.2 : ℝ))
    (hedgeVariance_le : ∀ k, ∀ e ∈ edges k,
      edgeVariance k e.1 e.2 ≤ V k)
    (hedgeScale_le : ∀ k, ∀ e ∈ edges k,
      edgeScale k e.1 e.2 ≤ B k)
    (hedgeBernstein : ∀ k, ∀ e ∈ edges k,
      HasBernsteinMGF (fun omega ↦ Z omega e.1 - Z omega e.2)
        (edgeVariance k e.1 e.2) (edgeScale k e.1 e.2) mu) :
    mu.real {omega | ∃ t,
        (∑' k, bernsteinMixedThreshold
          (V k : ℝ) (B k : ℝ) (x k)) < |Z omega t|} ≤
      ∑' k, (edges k).card * (2 * exp (-x k)) := by
  have hbaseTail : ∀ u ∈ N0,
      mu.real {omega | (0 : ℝ) < |Z omega u|} ≤ 0 := by
    intro u hu
    simp only [hbaseZero _ u hu, abs_zero, lt_self_iff_false,
      Set.ofPred_false, measureReal_empty, le_refl]
  have hedgeTail : ∀ k, ∀ e ∈ edges k,
      mu.real {omega |
        bernsteinMixedThreshold (V k : ℝ) (B k : ℝ) (x k) <
          |Z omega e.1 - Z omega e.2|} ≤ 2 * exp (-x k) := by
    intro k e he
    have hthreshold :
        bernsteinMixedThreshold (edgeVariance k e.1 e.2 : ℝ)
            (edgeScale k e.1 e.2 : ℝ) (x k) ≤
          bernsteinMixedThreshold (V k : ℝ) (B k : ℝ) (x k) :=
      bernsteinMixedThreshold_mono
        (by exact_mod_cast hedgeVariance_le k e he)
        (by exact_mod_cast hedgeScale_le k e he) (hx k)
    have htail :=
      (hedgeBernstein k e he).measureReal_abs_gt_mixedThreshold_le
        (hx k) (hedgeVariance k e he)
    exact (measureReal_mono (by
      intro omega homega
      exact lt_of_le_of_lt hthreshold homega)).trans htail
  simpa only [zero_add, Nat.cast_ofNat, Nat.cast_zero, mul_zero] using
    (measureReal_countableChaining_edges_largeDeviation_le
      Z N0 edges proj
        (fun k ↦ bernsteinMixedThreshold (V k : ℝ) (B k : ℝ) (x k))
        (fun k ↦ 2 * exp (-x k)) 0 0 hbase hedge
        hthresholdSummable hremainder hcostSummable hbaseTail hedgeTail)

end ProbabilityTheory
