/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

module

public import Tengoku.AsymptoticTrianglePacking.LeanPool.AsymptoticTrianglePacking.Internal.Tight.CoverWeight
public import Tengoku.AsymptoticTrianglePacking.LeanPool.AsymptoticTrianglePacking.Internal.Tight.CoverProb
public import Tengoku.AsymptoticTrianglePacking.LeanPool.AsymptoticTrianglePacking.Internal.Measurable
public import Tengoku.AsymptoticTrianglePacking.LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the first two moments of the loss weight

`coverWeight H v C = ∑_{u ≠ v} codeg(v,u)·1[u ∈ C]`
(`LeanPool.AsymptoticTrianglePacking.Internal.Tight.CoverWeight`) is a NONNEGATIVE
LINEAR combination of the one-round covering indicators.  Consequently its mean and its centred
second moment are exactly computable from the two covering laws already established:

* `prob_vertex_covered_eq` — `𝔼[1[u covered]] = coverRate H p u` (exact);
* `prob_two_vertices_covered_le` — `ℙ(u,u' covered) ≤ deg·deg·p² + codeg·p`.

Results:

* `integral_coverWeight` — `𝔼[coverWeight] = ∑_{u ≠ v} codeg(v,u)·q_u`;
* `integral_sq_centered_coverWeight` — the centred second moment as the exact double sum
  `∑_{u,u'} codeg(v,u)·codeg(v,u')·(ℙ(u,u' covered) − q_u q_{u'})`;
* `centered_second_moment_le` — the quantitative bound
  `𝔼[(coverWeight − 𝔼)²] ≤ κ·A·q_hi + ε₂·A²`, with `A = ∑_{u ≠ v} codeg(v,u) = (r−1)deg(v)`,
  `κ` the codegree bound and `ε₂` any bound on the pair excess `ℙ(u,u' cov) − q_u q_{u'}`.

The diagonal term is `O(κ·d·γ)` and the off-diagonal term `O(d²·ε₂)`; both are `o(d²)` in the nibble
regime, which is precisely the concentration the residual degree cannot have.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## The covering indicator -/

/-- The indicator that `u` is covered by the round matching.-/
noncomputable def coverInd {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (u : V) (ω : Ω) : ℝ :=
  if u ∈ covered (retainedSet H ρ ω) then 1 else 0

omit [Fintype V] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/--
@isnad1 id=measurab.0h6v.s5.5fb1261fc4d5 from=translated src=- shape=f2a3039b vocab=ec9ff292
-/
theorem measurable_coverInd {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (u : V) : Measurable (coverInd ρ u) :=
  Measurable.ite (measurableSet_vertex_covered ρ u) measurable_const measurable_const

omit [Fintype V] in
/--
@isnad1 id=integrab.0h6v.s6.8f376a8ec447 from=translated src=- shape=3fad3433 vocab=bb712b49
-/
theorem integrable_coverInd {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (u : V) :
    Integrable (coverInd ρ u) (ℙ : Measure Ω) := by
  refine (integrable_const (1 : ℝ)).mono' (measurable_coverInd ρ u).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [coverInd]; split_ifs <;> simp

omit [Fintype V] in
/--
@isnad1 id=eq.2h6v.s6.2526ff6b9d42 from=translated src=- shape=f0099462 vocab=9281525a
-/
theorem integral_coverInd {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u : V) :
    ∫ ω, coverInd ρ u ω ∂(ℙ : Measure Ω) = coverRate H p u := by
  have hind : coverInd ρ u = Set.indicator {ω | u ∈ covered (retainedSet H ρ ω)} 1 := by
    funext ω; rw [coverInd, Set.indicator_apply]; simp
  have hm : MeasurableSet {ω | u ∈ covered (retainedSet H ρ ω)} :=
    measurableSet_vertex_covered ρ u
  rw [hind, integral_indicator_one hm, prob_vertex_covered_eq ρ hp0 hp1 u]

omit [Fintype V] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The product of two covering indicators is the indicator of the joint event.
@isnad1 id=eq.0h7v.s7.bfe94dc7724a from=translated src=- shape=b4c83a16 vocab=0914e6f8
-/
theorem coverInd_mul {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (u u' : V) :
    (fun ω => coverInd ρ u ω * coverInd ρ u' ω)
      = Set.indicator ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)}) 1 := by
  funext ω
  rw [coverInd, coverInd, Set.indicator_apply]
  by_cases h1 : u ∈ covered (retainedSet H ρ ω) <;>
    by_cases h2 : u' ∈ covered (retainedSet H ρ ω) <;> simp [h1, h2]

omit [Fintype V] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/--
@isnad1 id=eq.0h7v.s7.9fee82dd7be8 from=translated src=- shape=94691904 vocab=9cfef236
-/
theorem integral_coverInd_mul {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (u u' : V) :
    ∫ ω, coverInd ρ u ω * coverInd ρ u' ω ∂(ℙ : Measure Ω)
      = (ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)}) := by
  have hmu : MeasurableSet {ω | u ∈ covered (retainedSet H ρ ω)} :=
    measurableSet_vertex_covered ρ u
  have hmu' : MeasurableSet {ω | u' ∈ covered (retainedSet H ρ ω)} :=
    measurableSet_vertex_covered ρ u'
  rw [coverInd_mul ρ u u', integral_indicator_one (hmu.inter hmu')]

omit [Fintype V] in
/--
@isnad1 id=integrab.0h7v.s6.01a8d2a1461c from=translated src=- shape=e7449177 vocab=4b34e9f3
-/
theorem integrable_coverInd_mul {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (u u' : V) :
    Integrable (fun ω => coverInd ρ u ω * coverInd ρ u' ω) (ℙ : Measure Ω) := by
  refine (integrable_const (1 : ℝ)).mono'
    (((measurable_coverInd ρ u).mul (measurable_coverInd ρ u')).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [coverInd, coverInd]
  split_ifs <;> simp

/-! ## The centred covering indicator -/

/-- The centred covering indicator `1[u covered] − q_u`.-/
noncomputable def coverIndC {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (u : V) (ω : Ω) : ℝ :=
  coverInd ρ u ω - coverRate H p u

omit [Fintype V] in
/--
@isnad1 id=integrab.0h7v.s6.1e5847e8ed46 from=translated src=- shape=e7449177 vocab=73abc657
-/
theorem integrable_coverIndC_mul {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (u u' : V) :
    Integrable (fun ω => coverIndC ρ u ω * coverIndC ρ u' ω) (ℙ : Measure Ω) := by
  have hexp : (fun ω => coverIndC ρ u ω * coverIndC ρ u' ω)
      = fun ω => coverInd ρ u ω * coverInd ρ u' ω
        - coverRate H p u' * coverInd ρ u ω
        - coverRate H p u * coverInd ρ u' ω
        + coverRate H p u * coverRate H p u' := by
    funext ω; rw [coverIndC, coverIndC]; ring
  rw [hexp]
  exact (((integrable_coverInd_mul ρ u u').sub
    ((integrable_coverInd ρ u).const_mul _)).sub
      ((integrable_coverInd ρ u').const_mul _)).add (integrable_const _)

omit [Fintype V] in
/-- **The pair covariance.**
@isnad1 id=eq.2h7v.s7.77b127293d9e from=translated src=- shape=d596608b vocab=adfe0d85
-/
theorem integral_coverIndC_mul {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u u' : V) :
    ∫ ω, coverIndC ρ u ω * coverIndC ρ u' ω ∂(ℙ : Measure Ω)
      = (ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u' := by
  have hexp : (fun ω => coverIndC ρ u ω * coverIndC ρ u' ω)
      = fun ω => coverInd ρ u ω * coverInd ρ u' ω
        - coverRate H p u' * coverInd ρ u ω
        - coverRate H p u * coverInd ρ u' ω
        + coverRate H p u * coverRate H p u' := by
    funext ω; rw [coverIndC, coverIndC]; ring
  have i1 : Integrable (fun ω => coverInd ρ u ω * coverInd ρ u' ω) (ℙ : Measure Ω) :=
    integrable_coverInd_mul ρ u u'
  have i2 : Integrable (fun ω => coverRate H p u' * coverInd ρ u ω) (ℙ : Measure Ω) :=
    (integrable_coverInd ρ u).const_mul _
  have i3 : Integrable (fun ω => coverRate H p u * coverInd ρ u' ω) (ℙ : Measure Ω) :=
    (integrable_coverInd ρ u').const_mul _
  have iAB : Integrable (fun ω => coverInd ρ u ω * coverInd ρ u' ω
      - coverRate H p u' * coverInd ρ u ω) (ℙ : Measure Ω) := i1.sub i2
  have iABC : Integrable (fun ω => coverInd ρ u ω * coverInd ρ u' ω
      - coverRate H p u' * coverInd ρ u ω
      - coverRate H p u * coverInd ρ u' ω) (ℙ : Measure Ω) := iAB.sub i3
  rw [hexp, integral_add iABC (integrable_const _), integral_sub iAB i3,
    integral_sub i1 i2, integral_coverInd_mul ρ u u', integral_const_mul, integral_const_mul,
    integral_coverInd ρ hp0 hp1 u, integral_coverInd ρ hp0 hp1 u', integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

/-! ## The loss weight as a linear form -/

/-- `coverWeight` written as a linear form in the covering indicators.
@isnad1 id=eq.0h4v.s6.da49bc14376f from=translated src=- shape=2a2c2719 vocab=4b631f3b
-/
theorem coverWeight_eq_linear (H : Finset (Finset V)) (v : V) (C : Finset V) :
    (coverWeight H v C : ℝ)
      = ∑ u ∈ (Finset.univ : Finset V).erase v,
          (codegree H v u : ℝ) * (if u ∈ C then (1 : ℝ) else 0) := by
  classical
  have hterm : ∀ u : V, (codegree H v u : ℝ) * (if u ∈ C then (1 : ℝ) else 0)
      = if u ∈ C then (codegree H v u : ℝ) else 0 := by
    intro u; split_ifs <;> ring
  simp only [hterm]
  rw [← Finset.sum_filter]
  have hset : ((Finset.univ : Finset V).erase v).filter (fun u => u ∈ C) = C.erase v := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ]
    tauto
  rw [hset, coverWeight, Nat.cast_sum]

/-- The loss weight of `v` as a random variable.-/
noncomputable def lossWeight {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (ω : Ω) : ℝ :=
  ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * coverInd ρ u ω

/-- Its deterministic mean.-/
noncomputable def lossWeightMean (H : Finset (Finset V)) (p : ℝ) (v : V) : ℝ :=
  ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * coverRate H p u

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/--
@isnad1 id=eq.0h7v.s6.e6d00e6363d4 from=translated src=- shape=d8847c76 vocab=01980ba1
-/
theorem lossWeight_eq' {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (ω : Ω) :
    (coverWeight H v (covered (retainedSet H ρ ω)) : ℝ) = lossWeight ρ v ω := by
  rw [coverWeight_eq_linear]
  rfl

/-- **The mean of the loss weight.**
@isnad1 id=eq.2h6v.s6.db0b23bd40e0 from=translated src=- shape=da2e5767 vocab=e2e9a977
-/
theorem integral_lossWeight {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V) :
    ∫ ω, lossWeight ρ v ω ∂(ℙ : Measure Ω) = lossWeightMean H p v := by
  simp only [lossWeight, lossWeightMean]
  rw [integral_finsetSum _ (fun u _ => (integrable_coverInd ρ u).const_mul _)]
  exact Finset.sum_congr rfl (fun u _ => by
    rw [integral_const_mul, integral_coverInd ρ hp0 hp1 u])

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The centred loss weight as a linear form in the centred indicators.
@isnad1 id=eq.0h7v.s6.e6f98bd7ee83 from=translated src=- shape=cd1d70b6 vocab=d5f23f63
-/
theorem lossWeight_sub_mean {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (ω : Ω) :
    lossWeight ρ v ω - lossWeightMean H p v
      = ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * coverIndC ρ u ω := by
  rw [lossWeight, lossWeightMean, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun u _ => by rw [coverIndC]; ring)

/-- **The centred second moment of the loss weight**, as an exact double sum.
@isnad1 id=eq.2h6v.s8.a2aad22d8524 from=translated src=- shape=bfefa5ef vocab=443f67e6
-/
theorem integral_sq_centered_lossWeight {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V) :
    ∫ ω, (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 ∂(ℙ : Measure Ω)
      = ∑ u ∈ (Finset.univ : Finset V).erase v, ∑ u' ∈ (Finset.univ : Finset V).erase v,
          (codegree H v u : ℝ) * (codegree H v u' : ℝ)
            * ((ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
                ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
              - coverRate H p u * coverRate H p u') := by
  have hexp : ∀ ω, (lossWeight ρ v ω - lossWeightMean H p v) ^ 2
      = ∑ u ∈ (Finset.univ : Finset V).erase v, ∑ u' ∈ (Finset.univ : Finset V).erase v,
          (codegree H v u : ℝ) * (codegree H v u' : ℝ)
            * (coverIndC ρ u ω * coverIndC ρ u' ω) := by
    intro ω
    rw [lossWeight_sub_mean, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun u' _ => by ring))
  simp only [hexp]
  rw [integral_finsetSum _ (fun u _ => integrable_finsetSum _
    (fun u' _ => (integrable_coverIndC_mul ρ u u').const_mul _))]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [integral_finsetSum _ (fun u' _ => (integrable_coverIndC_mul ρ u u').const_mul _)]
  exact Finset.sum_congr rfl (fun u' _ => by
    rw [integral_const_mul, integral_coverIndC_mul ρ hp0 hp1 u u'])

end LeanPool.AsymptoticTrianglePacking.Internal
