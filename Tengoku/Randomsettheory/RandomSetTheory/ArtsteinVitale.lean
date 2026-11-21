/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.Basic
import Tengoku.Randomsettheory.RandomSetTheory.Geometry
import Tengoku.Randomsettheory.RandomSetTheory.SupportSelection
import Tengoku.Seed.Probability.StrongLaw

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Deterministic foundations for the Artstein--Vitale law of large numbers

This file collects the finite-dimensional compactness and support-function
arguments used to turn scalar laws of large numbers into Hausdorff convergence
of compact convex random sets.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory Filter TopologicalSpace ProbabilityTheory
open scoped InnerProductSpace Topology

noncomputable section

namespace Tengoku.Randomsettheory.RandomSet

/-- Effros measurability is preserved by a measurable change of the sample
space.  In particular, an Effros random set may be evaluated along each
measurable coordinate of a random sequence.
@isnad1 id=iseffros.2h5v.s5.f508e8e5a21a from=translated src=- shape=21079e98 vocab=46f7a675
-/
theorem IsEffrosMeasurable.comp_measurable
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [TopologicalSpace E] {S : Ω → Set E} (hS : IsEffrosMeasurable S)
    {f : Ω' → Ω} (hf : Measurable f) :
    IsEffrosMeasurable (fun ω => S (f ω)) := by
  intro U hU
  change MeasurableSet (f ⁻¹' {ω | (S ω ∩ U).Nonempty})
  exact (hS U hU).preimage hf

end Tengoku.Randomsettheory.RandomSet

namespace RandomSetTheory

/-- The closed unit ball of a finite-dimensional normed real vector space has
a finite net at every positive scale.  The centres can themselves be chosen
in the unit ball.
@isnad1 id=ex.1h2v.s6.3b9847a758ac from=translated src=- shape=20ee206b vocab=653242af
-/
theorem exists_finset_unitBall_net
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset E, ∀ u : E, ‖u‖ ≤ 1 →
      ∃ v ∈ N, dist u v < ε := by
  classical
  obtain ⟨t, htunit, htfinite, hcover⟩ :=
    finite_cover_balls_of_compact
      (isCompact_closedBall (0 : E) 1) hε
  refine ⟨htfinite.toFinset, ?_⟩
  intro u hu
  have hu' : u ∈ closedBall (0 : E) 1 := by
    simpa [mem_closedBall, dist_zero_right] using hu
  obtain ⟨v, hvt, huv⟩ := Set.mem_iUnion₂.mp (hcover hu')
  exact ⟨v, by simpa using hvt, by simpa [mem_ball] using huv⟩

/-- In a separable finite-dimensional space, the finite net can be chosen
from the canonical dense sequence.  This is the countable reduction needed
to intersect the almost-sure scalar convergence events.
@isnad1 id=ex.1h2v.s6.ab17bf6bdd72 from=translated src=- shape=e40e9355 vocab=e91f230c
-/
theorem exists_finset_denseSeq_unitBall_net
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ε : ℝ} (hε : 0 < ε) :
    ∃ I : Finset ℕ, ∀ u : E, ‖u‖ ≤ 1 →
      ∃ k ∈ I, dist u (denseSeq E k) < ε := by
  classical
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨N, hN⟩ := exists_finset_unitBall_net (E := E) hhalf
  let index : E → ℕ := fun v =>
    Nat.find ((denseRange_denseSeq E).exists_dist_lt v hhalf)
  have hindex : ∀ v : E, dist (denseSeq E (index v)) v < ε / 2 := by
    intro v
    simpa [dist_comm] using
      Nat.find_spec ((denseRange_denseSeq E).exists_dist_lt v hhalf)
  refine ⟨N.image index, ?_⟩
  intro u hu
  obtain ⟨v, hvN, huv⟩ := hN u hu
  refine ⟨index v, Finset.mem_image.mpr ⟨v, hvN, rfl⟩, ?_⟩
  calc
    dist u (denseSeq E (index v)) ≤
        dist u v + dist v (denseSeq E (index v)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 :=
      add_lt_add huv (by simpa [dist_comm] using hindex v)
    _ = ε := by ring

/-- Averaging sets contained in a closed ball preserves the same radius
bound, including for the empty index set (whose Minkowski sum is `{0}`).
@isnad1 id=le.3h6v.s6.3eb70f1d9e14 from=translated src=- shape=50cd1443 vocab=976307be
-/
theorem norm_le_radius_of_mem_minkowskiAverage
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (K : ι → Set E) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ i ∈ s, ∀ x ∈ K i, ‖x‖ ≤ R)
    {x : E} (hx : x ∈ minkowskiAverage s K) :
    ‖x‖ ≤ R := by
  have hx' := norm_le_average_radius_of_mem_minkowskiAverage
    s K (fun _ => R) hbound hx
  by_cases hs : s.card = 0
  · have hx0 : ‖x‖ ≤ 0 := by simpa [hs] using hx'
    exact hx0.trans hR
  · have hs' : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs
    simpa [hs'] using hx'

/-- Pointwise convergence of support functions on the canonical dense
sequence implies Hausdorff convergence, provided all sets are compact,
nonempty, convex and share a deterministic radius bound.  This is the
deterministic core of the finite-dimensional Artstein--Vitale argument.
@isnad1 id=tendsto.10h4v.s8.19e70ba6b284 from=translated src=- shape=e24799a0 vocab=e9b610e7
-/
theorem tendsto_hausdorffDist_of_tendsto_supportFunction_denseSeq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : ℕ → Set E} {L : Set E} {R : ℝ}
    (hKcompact : ∀ n, IsCompact (K n)) (hLcompact : IsCompact L)
    (hKne : ∀ n, (K n).Nonempty) (hLne : L.Nonempty)
    (hKconv : ∀ n, Convex ℝ (K n)) (hLconv : Convex ℝ L)
    (hR : 0 ≤ R)
    (hKbound : ∀ n, ∀ x ∈ K n, ‖x‖ ≤ R)
    (hLbound : ∀ x ∈ L, ‖x‖ ≤ R)
    (hsupport : ∀ k : ℕ,
      Tendsto (fun n => supportFunction (K n) (denseSeq E k)) atTop
        (𝓝 (supportFunction L (denseSeq E k)))) :
    Tendsto (fun n => hausdorffDist (K n) L) atTop (𝓝 0) := by
  classical
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  let δ : ℝ := ε / (8 * (R + 1))
  have hRone : 0 < R + 1 := by linarith
  have hden : 0 < 8 * (R + 1) := mul_pos (by norm_num) hRone
  have hδ : 0 < δ := div_pos hε hden
  have hprod : (R + R) * δ ≤ ε / 4 := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hR hε.le]
  obtain ⟨I, hInet⟩ :=
    exists_finset_denseSeq_unitBall_net (E := E) hδ
  let N : Finset E := I.image (denseSeq E)
  have hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ δ := by
    intro u hu
    obtain ⟨k, hkI, huk⟩ := hInet u hu
    refine ⟨denseSeq E k, ?_, huk.le⟩
    exact Finset.mem_image.mpr ⟨k, hkI, rfl⟩
  have heach : ∀ k ∈ I, ∀ᶠ n in atTop,
      |supportFunction (K n) (denseSeq E k) -
        supportFunction L (denseSeq E k)| ≤ ε / 2 := by
    intro k _
    obtain ⟨m, hm⟩ :=
      Metric.tendsto_atTop.mp (hsupport k) (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop m] with n hn
    have hmn := (hm n hn).le
    simpa [Real.dist_eq] using hmn
  have hall : ∀ᶠ n in atTop, ∀ k ∈ I,
      |supportFunction (K n) (denseSeq E k) -
        supportFunction L (denseSeq E k)| ≤ ε / 2 :=
    I.eventually_all.mpr heach
  apply eventually_atTop.mp
  filter_upwards [hall] with n hn
  have hNsupport : ∀ v ∈ N,
      |supportFunction (K n) v - supportFunction L v| ≤ ε / 2 := by
    intro v hv
    obtain ⟨k, hkI, rfl⟩ := Finset.mem_image.mp hv
    exact hn k hkI
  have hhd : hausdorffDist (K n) L ≤
      ε / 2 + (R + R) * δ :=
    hausdorffDist_le_of_finset_net_supportFunction
      (hKcompact n) hLcompact (hKne n) hLne
      (hKconv n) hLconv (hKbound n) hLbound
      hδ.le (half_pos hε).le N hnet hNsupport
  have hlt : hausdorffDist (K n) L < ε :=
    hhd.trans_lt <| calc
      ε / 2 + (R + R) * δ ≤ ε / 2 + ε / 4 :=
        add_le_add (le_refl _) hprod
      _ < ε := by linarith
  simpa [Real.dist_eq, abs_of_nonneg hausdorffDist_nonneg] using hlt

/-- Tail version of the deterministic support-to-Hausdorff theorem.  A
common radius bound is needed only eventually, which is the form supplied by
the scalar strong law for an integrable random envelope.
@isnad1 id=tendsto.10h4v.s8.20dad90769f1 from=translated src=- shape=66b87d92 vocab=56215597
-/
theorem tendsto_hausdorffDist_of_tendsto_supportFunction_denseSeq_eventually
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : ℕ → Set E} {L : Set E} {R : ℝ}
    (hKcompact : ∀ n, IsCompact (K n)) (hLcompact : IsCompact L)
    (hKne : ∀ n, (K n).Nonempty) (hLne : L.Nonempty)
    (hKconv : ∀ n, Convex ℝ (K n)) (hLconv : Convex ℝ L)
    (hR : 0 ≤ R)
    (hKbound : Filter.Eventually (fun n => ∀ x ∈ K n, ‖x‖ ≤ R) atTop)
    (hLbound : ∀ x ∈ L, ‖x‖ ≤ R)
    (hsupport : ∀ k : ℕ,
      Tendsto (fun n => supportFunction (K n) (denseSeq E k)) atTop
        (nhds (supportFunction L (denseSeq E k)))) :
    Tendsto (fun n => hausdorffDist (K n) L) atTop (nhds 0) := by
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hKbound)
  let K' : ℕ → Set E := fun n => if N ≤ n then K n else L
  have hK'compact : ∀ n, IsCompact (K' n) := by
    intro n
    by_cases hn : N ≤ n
    · simpa [K', hn] using hKcompact n
    · simpa [K', hn] using hLcompact
  have hK'ne : ∀ n, (K' n).Nonempty := by
    intro n
    by_cases hn : N ≤ n
    · simpa [K', hn] using hKne n
    · simpa [K', hn] using hLne
  have hK'conv : ∀ n, Convex ℝ (K' n) := by
    intro n
    by_cases hn : N ≤ n
    · simpa [K', hn] using hKconv n
    · simpa [K', hn] using hLconv
  have hK'bound : ∀ n, ∀ x ∈ K' n, ‖x‖ ≤ R := by
    intro n
    by_cases hn : N ≤ n
    · simpa [K', hn] using hN n hn
    · simpa [K', hn] using hLbound
  have hsupport' : ∀ k : ℕ,
      Tendsto (fun n => supportFunction (K' n) (denseSeq E k)) atTop
        (nhds (supportFunction L (denseSeq E k))) := by
    intro k
    apply Tendsto.congr' _ (hsupport k)
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [K', hn]
  have hconv := tendsto_hausdorffDist_of_tendsto_supportFunction_denseSeq
    hK'compact hLcompact hK'ne hLne hK'conv hLconv hR
    hK'bound hLbound hsupport'
  apply Tendsto.congr' _ hconv
  filter_upwards [eventually_ge_atTop N] with n hn
  simp [K', hn]

/-- Strong law for compact convex random sets, reduced to the scalar strong
law for their support functions on the canonical dense sequence.  The
independence and identical-distribution hypotheses are stated directly for
those scalar processes, which is the exact interface consumed by Mathlib's
real-valued SLLN.
@isnad1 id=eventual.13h6v.s9.554f4ca165b8 from=translated src=- shape=0c066b78 vocab=a7bd231c
-/
theorem ae_tendsto_hausdorffDist_minkowskiAverage_of_scalar_slln
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {μ : Measure Ω} {S : ℕ → Ω → Set E} {L : Set E} {R : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hLconv : Convex ℝ L) (hR : 0 ≤ R)
    (hSbound : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ R)
    (hLbound : ∀ x ∈ L, ‖x‖ ≤ R)
    (hint : ∀ k : ℕ,
      Integrable (fun ω => supportFunction (S 0 ω) (denseSeq E k)) μ)
    (hindep : ∀ k : ℕ, Pairwise (fun i j =>
      IndepFun
        (fun ω => supportFunction (S i ω) (denseSeq E k))
        (fun ω => supportFunction (S j ω) (denseSeq E k)) μ))
    (hident : ∀ k i : ℕ,
      IdentDistrib
        (fun ω => supportFunction (S i ω) (denseSeq E k))
        (fun ω => supportFunction (S 0 ω) (denseSeq E k)) μ μ)
    (hLsupport : ∀ k : ℕ,
      supportFunction L (denseSeq E k) =
        ∫ ω, supportFunction (S 0 ω) (denseSeq E k) ∂μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => hausdorffDist
        (minkowskiAverage (Finset.range n) (fun i => S i ω)) L)
      atTop (𝓝 0) := by
  classical
  have hscalar : ∀ k : ℕ, ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          (∑ i ∈ Finset.range n,
            supportFunction (S i ω) (denseSeq E k)) / n)
        atTop
        (𝓝 (∫ ω, supportFunction (S 0 ω) (denseSeq E k) ∂μ)) := by
    intro k
    exact ProbabilityTheory.strong_law_ae_real
      (fun i ω => supportFunction (S i ω) (denseSeq E k))
      (hint k) (hindep k) (hident k)
  filter_upwards [ae_all_iff.mpr hscalar] with ω hω
  apply tendsto_hausdorffDist_of_tendsto_supportFunction_denseSeq
    (K := fun n => minkowskiAverage (Finset.range n) (fun i => S i ω))
    (L := L) (R := R)
  · intro n
    exact isCompact_minkowskiAverage _ _
      (fun i _ => hScompact i ω)
  · exact hLcompact
  · intro n
    exact nonempty_minkowskiAverage _ _ (fun i _ => hSne i ω)
  · exact hLne
  · intro n
    exact convex_minkowskiAverage _ _ (fun i _ => hSconv i ω)
  · exact hLconv
  · exact hR
  · intro n x hx
    exact norm_le_radius_of_mem_minkowskiAverage
      (Finset.range n) (fun i => S i ω) hR
      (fun i _ => hSbound i ω) hx
  · exact hLbound
  · intro k
    rw [hLsupport k]
    apply Tendsto.congr'
      (Filter.Eventually.of_forall fun n => ?_) (hω k)
    rw [supportFunction_minkowskiAverage]
    · simp only [Finset.card_range, div_eq_inv_mul]
    · exact fun i _ => hScompact i ω
    · exact fun i _ => hSne i ω

/-- Convexified Artstein--Vitale strong law.  No convexity is assumed of the
original compact values: each realization is replaced by its closed convex
hull.  Its support function is unchanged, so the scalar integrability,
independence and identical-distribution hypotheses remain those of the
original random sets.
@isnad1 id=eventual.12h6v.s9.642899bf51e5 from=translated src=- shape=a507d9d5 vocab=8ffdf4da
-/
theorem ae_tendsto_hausdorffDist_convexifiedAverage_of_scalar_slln
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {μ : Measure Ω} {S : ℕ → Ω → Set E} {L : Set E} {R : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hLconv : Convex ℝ L) (hR : 0 ≤ R)
    (hSbound : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ R)
    (hLbound : ∀ x ∈ L, ‖x‖ ≤ R)
    (hint : ∀ k : ℕ,
      Integrable (fun ω => supportFunction (S 0 ω) (denseSeq E k)) μ)
    (hindep : ∀ k : ℕ, Pairwise (fun i j =>
      IndepFun
        (fun ω => supportFunction (S i ω) (denseSeq E k))
        (fun ω => supportFunction (S j ω) (denseSeq E k)) μ))
    (hident : ∀ k i : ℕ,
      IdentDistrib
        (fun ω => supportFunction (S i ω) (denseSeq E k))
        (fun ω => supportFunction (S 0 ω) (denseSeq E k)) μ μ)
    (hLsupport : ∀ k : ℕ,
      supportFunction L (denseSeq E k) =
        ∫ ω, supportFunction (S 0 ω) (denseSeq E k) ∂μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => hausdorffDist
        (minkowskiAverage (Finset.range n)
          (fun i => closedConvexHull ℝ (S i ω))) L)
      atTop (𝓝 0) := by
  have hsuppHull : ∀ i ω u,
      supportFunction (closedConvexHull ℝ (S i ω)) u =
        supportFunction (S i ω) u := by
    intro i ω u
    exact supportFunction_closedConvexHull
      (hScompact i ω) (hSne i ω) u
  apply ae_tendsto_hausdorffDist_minkowskiAverage_of_scalar_slln
    (S := fun i ω => closedConvexHull ℝ (S i ω))
    (L := L) (R := R)
  · exact fun i ω => closedConvexHull_compact (hScompact i ω)
  · exact fun i ω => (hSne i ω).mono subset_closedConvexHull
  · exact fun _ _ => convex_closedConvexHull
  · exact hLcompact
  · exact hLne
  · exact hLconv
  · exact hR
  · intro i ω
    have hsub : closedConvexHull ℝ (S i ω) ⊆ closedBall (0 : E) R := by
      apply closedConvexHull_min
      · intro x hx
        simpa [mem_closedBall, dist_zero_right] using hSbound i ω x hx
      · exact convex_closedBall (0 : E) R
      · exact isClosed_closedBall
    intro x hx
    simpa [mem_closedBall, dist_zero_right] using hsub hx
  · exact hLbound
  · intro k
    simpa only [hsuppHull] using hint k
  · intro k
    simpa only [hsuppHull] using hindep k
  · intro k i
    simpa only [hsuppHull] using hident k i
  · intro k
    simpa only [hsuppHull] using hLsupport k

/-- Bounded iid-observation form of the convexified Artstein--Vitale law.
All scalar SLLN hypotheses are derived from pairwise independence and
identical distribution of the underlying observations.  The population
target is the closed convex hull of the closed Aumann expectation.
@isnad1 id=eventual.8h7v.s8.358c6a912d48 from=translated src=- shape=97503031 vocab=5f0b0a89
-/
theorem ae_tendsto_hausdorffDist_convexified_iid
    {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Z) (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise (fun i j => IndepFun (X i) (X j) μ))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z)) (hFne : ∀ z, (F z).Nonempty)
    {R : ℝ} (hR : 0 ≤ R)
    (hFbound : ∀ z, ∀ x ∈ F z, ‖x‖ ≤ R) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => hausdorffDist
        (closedConvexHull ℝ
          (minkowskiAverage (Finset.range n) (fun i => F (X i ω))))
        (closedConvexHull ℝ
          (closure (aumannExpectation μ (fun ω => F (X 0 ω))))))
      atTop (nhds 0) := by
  let S₀ : Ω → Set E := fun ω => F (X 0 ω)
  let A : Set E := closure (aumannExpectation μ S₀)
  let L : Set E := closedConvexHull ℝ A
  have hS₀Effros : RandomSet.IsEffrosMeasurable S₀ :=
    hF.comp_measurable (hX 0)
  have hS₀compact : ∀ ω, IsCompact (S₀ ω) := fun ω =>
    hFcompact (X 0 ω)
  have hS₀ne : ∀ ω, (S₀ ω).Nonempty := fun ω =>
    hFne (X 0 ω)
  have hg : Integrable (fun _ : Ω => R) μ := integrable_const R
  have hS₀dom : ∀ ω, ∀ x ∈ S₀ ω, ‖x‖ ≤ R := fun ω =>
    hFbound (X 0 ω)
  have hAcompact : IsCompact A :=
    closure_aumannExpectation_compact_of_integrable_envelope hg
      (Filter.Eventually.of_forall hS₀dom)
  have hfOne : IsIntegrableSelection μ S₀
      (supportApproximateSelection
        hS₀Effros hS₀compact hS₀ne 0 1 (by norm_num)) :=
    integrableSelection_supportApproximateSelection_of_envelope
      hS₀Effros hS₀compact hS₀ne hg hS₀dom 0 (by norm_num)
  have hAne : A.Nonempty :=
    (aumannExpectation_nonempty_of_selection hfOne).closure
  have hLcompact : IsCompact L := closedConvexHull_compact hAcompact
  have hLne : L.Nonempty := hAne.mono subset_closedConvexHull
  have hLbound : ∀ x ∈ L, ‖x‖ ≤ R := by
    have hAsub : A ⊆ Metric.closedBall (0 : E) R := by
      intro x hx
      have hxR := norm_le_integral_envelope_of_mem_closure_aumannExpectation
        hg (Filter.Eventually.of_forall hS₀dom) hx
      have hxR' : ‖x‖ ≤ R := by simpa using hxR
      simpa [Metric.mem_closedBall, dist_zero_right] using hxR'
    have hLsub : L ⊆ Metric.closedBall (0 : E) R :=
      closedConvexHull_min hAsub (convex_closedBall (0 : E) R)
        Metric.isClosed_closedBall
    intro x hx
    simpa [Metric.mem_closedBall, dist_zero_right] using hLsub hx
  have hsuppMeas : ∀ k : ℕ,
      Measurable (fun z => supportFunction (F z) (denseSeq E k)) := fun k =>
    measurable_supportFunction hF hFcompact hFne (denseSeq E k)
  have hint : ∀ k : ℕ,
      Integrable (fun ω => supportFunction (F (X 0 ω)) (denseSeq E k)) μ :=
    fun k => integrable_supportFunction_of_envelope
      hS₀Effros hS₀compact hS₀ne hg hS₀dom (denseSeq E k)
  have hindepSupport : ∀ k : ℕ, Pairwise (fun i j =>
      IndepFun
        (fun ω => supportFunction (F (X i ω)) (denseSeq E k))
        (fun ω => supportFunction (F (X j ω)) (denseSeq E k)) μ) := by
    intro k i j hij
    exact (hindep hij).comp (hsuppMeas k) (hsuppMeas k)
  have hidentSupport : ∀ k i : ℕ,
      IdentDistrib
        (fun ω => supportFunction (F (X i ω)) (denseSeq E k))
        (fun ω => supportFunction (F (X 0 ω)) (denseSeq E k)) μ μ := by
    intro k i
    exact (hident i).comp (hsuppMeas k)
  have hLsupport : ∀ k : ℕ,
      supportFunction L (denseSeq E k) =
        ∫ ω, supportFunction (F (X 0 ω)) (denseSeq E k) ∂μ := by
    intro k
    rw [supportFunction_closedConvexHull hAcompact hAne]
    exact supportFunction_closure_aumannExpectation_of_envelope
      hS₀Effros hS₀compact hS₀ne hg hS₀dom hAcompact (denseSeq E k)
  have hcore := ae_tendsto_hausdorffDist_convexifiedAverage_of_scalar_slln
    (S := fun i ω => F (X i ω)) (L := L) (R := R)
    (fun i ω => hFcompact (X i ω))
    (fun i ω => hFne (X i ω))
    hLcompact hLne convex_closedConvexHull hR
    (fun i ω => hFbound (X i ω)) hLbound
    hint hindepSupport hidentSupport hLsupport
  filter_upwards [hcore] with ω hω
  apply Tendsto.congr' _ hω
  filter_upwards [] with n
  rw [closedConvexHull_minkowskiAverage (Finset.range n)
    (fun i => F (X i ω))
    (fun i _ => hFcompact (X i ω))
    (fun i _ => hFne (X i ω))]

/-- Integrably bounded iid-observation form of the convexified
Artstein--Vitale law.  Unlike
`ae_tendsto_hausdorffDist_convexified_iid`, this theorem does not assume a
deterministic bound on every realization.  The scalar strong law applied to
the envelope supplies an eventual common radius for the empirical averages.
@isnad1 id=eventual.9h7v.s9.2d8d5c3476c4 from=translated src=- shape=5c2d5615 vocab=bdcf2031
-/
theorem ae_tendsto_hausdorffDist_convexified_iid_of_integrable_envelope
    {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Z) (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise (fun i j => IndepFun (X i) (X j) μ))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z)) (hFne : ∀ z, (F z).Nonempty)
    (g : Z → ℝ) (hg : Measurable g)
    (hgint : Integrable (fun ω => g (X 0 ω)) μ)
    (hFbound : ∀ z, ∀ x ∈ F z, ‖x‖ ≤ g z) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => hausdorffDist
        (closedConvexHull ℝ
          (minkowskiAverage (Finset.range n) (fun i => F (X i ω))))
        (closedConvexHull ℝ
          (closure (aumannExpectation μ (fun ω => F (X 0 ω))))))
      atTop (nhds 0) := by
  classical
  let S₀ : Ω → Set E := fun ω => F (X 0 ω)
  let A : Set E := closure (aumannExpectation μ S₀)
  let L : Set E := closedConvexHull ℝ A
  let m : ℝ := ∫ ω, g (X 0 ω) ∂μ
  let R : ℝ := m + 1
  have hgnonneg : ∀ z, 0 ≤ g z := by
    intro z
    obtain ⟨x, hx⟩ := hFne z
    exact (norm_nonneg x).trans (hFbound z x hx)
  have hm : 0 ≤ m := by
    dsimp [m]
    exact integral_nonneg (fun ω => hgnonneg (X 0 ω))
  have hR : 0 ≤ R := by
    dsimp [R]
    linarith
  have hS₀Effros : RandomSet.IsEffrosMeasurable S₀ :=
    hF.comp_measurable (hX 0)
  have hS₀compact : ∀ ω, IsCompact (S₀ ω) := fun ω =>
    hFcompact (X 0 ω)
  have hS₀ne : ∀ ω, (S₀ ω).Nonempty := fun ω =>
    hFne (X 0 ω)
  have hS₀dom : ∀ ω, ∀ x ∈ S₀ ω, ‖x‖ ≤ g (X 0 ω) := fun ω =>
    hFbound (X 0 ω)
  have hAcompact : IsCompact A :=
    closure_aumannExpectation_compact_of_integrable_envelope hgint
      (Filter.Eventually.of_forall hS₀dom)
  have hfOne : IsIntegrableSelection μ S₀
      (supportApproximateSelection
        hS₀Effros hS₀compact hS₀ne 0 1 (by norm_num)) :=
    integrableSelection_supportApproximateSelection_of_envelope
      hS₀Effros hS₀compact hS₀ne hgint hS₀dom 0 (by norm_num)
  have hAne : A.Nonempty :=
    (aumannExpectation_nonempty_of_selection hfOne).closure
  have hLcompact : IsCompact L := closedConvexHull_compact hAcompact
  have hLne : L.Nonempty := hAne.mono subset_closedConvexHull
  have hLbound : ∀ x ∈ L, ‖x‖ ≤ R := by
    have hAsub : A ⊆ Metric.closedBall (0 : E) R := by
      intro x hx
      have hxm := norm_le_integral_envelope_of_mem_closure_aumannExpectation
        hgint (Filter.Eventually.of_forall hS₀dom) hx
      have hxR : ‖x‖ ≤ R := hxm.trans <| by
        dsimp [m, R]
        linarith
      simpa [Metric.mem_closedBall, dist_zero_right] using hxR
    have hLsub : L ⊆ Metric.closedBall (0 : E) R :=
      closedConvexHull_min hAsub (convex_closedBall (0 : E) R)
        Metric.isClosed_closedBall
    intro x hx
    simpa [Metric.mem_closedBall, dist_zero_right] using hLsub hx
  have hsuppMeas : ∀ k : ℕ,
      Measurable (fun z => supportFunction (F z) (denseSeq E k)) := fun k =>
    measurable_supportFunction hF hFcompact hFne (denseSeq E k)
  have hint : ∀ k : ℕ,
      Integrable (fun ω => supportFunction (F (X 0 ω)) (denseSeq E k)) μ :=
    fun k => integrable_supportFunction_of_envelope
      hS₀Effros hS₀compact hS₀ne hgint hS₀dom (denseSeq E k)
  have hindepSupport : ∀ k : ℕ, Pairwise (fun i j =>
      IndepFun
        (fun ω => supportFunction (F (X i ω)) (denseSeq E k))
        (fun ω => supportFunction (F (X j ω)) (denseSeq E k)) μ) := by
    intro k i j hij
    exact (hindep hij).comp (hsuppMeas k) (hsuppMeas k)
  have hidentSupport : ∀ k i : ℕ,
      IdentDistrib
        (fun ω => supportFunction (F (X i ω)) (denseSeq E k))
        (fun ω => supportFunction (F (X 0 ω)) (denseSeq E k)) μ μ := by
    intro k i
    exact (hident i).comp (hsuppMeas k)
  have hLsupport : ∀ k : ℕ,
      supportFunction L (denseSeq E k) =
        ∫ ω, supportFunction (F (X 0 ω)) (denseSeq E k) ∂μ := by
    intro k
    rw [supportFunction_closedConvexHull hAcompact hAne]
    exact supportFunction_closure_aumannExpectation_of_envelope
      hS₀Effros hS₀compact hS₀ne hgint hS₀dom hAcompact (denseSeq E k)
  have hscalar : ∀ k : ℕ, ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          (∑ i ∈ Finset.range n,
            supportFunction (F (X i ω)) (denseSeq E k)) / n)
        atTop
        (nhds (∫ ω, supportFunction (F (X 0 ω)) (denseSeq E k) ∂μ)) := by
    intro k
    exact ProbabilityTheory.strong_law_ae_real
      (fun i ω => supportFunction (F (X i ω)) (denseSeq E k))
      (hint k) (hindepSupport k) (hidentSupport k)
  have hindepEnvelope : Pairwise (fun i j =>
      IndepFun (fun ω => g (X i ω)) (fun ω => g (X j ω)) μ) := by
    intro i j hij
    exact (hindep hij).comp hg hg
  have hidentEnvelope : ∀ i,
      IdentDistrib (fun ω => g (X i ω)) (fun ω => g (X 0 ω)) μ μ := by
    intro i
    exact (hident i).comp hg
  have henvelope : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, g (X i ω)) / n)
        atTop (nhds m) := by
    simpa [m] using ProbabilityTheory.strong_law_ae_real
      (fun i ω => g (X i ω)) hgint hindepEnvelope hidentEnvelope
  have hsuppHull : ∀ i ω u,
      supportFunction (closedConvexHull ℝ (F (X i ω))) u =
        supportFunction (F (X i ω)) u := by
    intro i ω u
    exact supportFunction_closedConvexHull
      (hFcompact (X i ω)) (hFne (X i ω)) u
  filter_upwards [ae_all_iff.mpr hscalar, henvelope] with ω hω henvω
  have henvBound : ∀ᶠ n in atTop,
      (∑ i ∈ Finset.range n, g (X i ω)) / n ≤ R := by
    exact (henvω.eventually_lt_const (by
      dsimp [R]
      linarith)).mono (fun _ hn => hn.le)
  have hKbound : ∀ᶠ n in atTop, ∀ x ∈
      minkowskiAverage (Finset.range n)
        (fun i => closedConvexHull ℝ (F (X i ω))), ‖x‖ ≤ R := by
    filter_upwards [henvBound] with n hn
    intro x hx
    have hHullBound : ∀ i ∈ Finset.range n,
        ∀ y ∈ closedConvexHull ℝ (F (X i ω)), ‖y‖ ≤ g (X i ω) := by
      intro i _ y hy
      have hsub : closedConvexHull ℝ (F (X i ω)) ⊆
          Metric.closedBall (0 : E) (g (X i ω)) := by
        apply closedConvexHull_min
        · intro z hz
          simpa [Metric.mem_closedBall, dist_zero_right] using
            hFbound (X i ω) z hz
        · exact convex_closedBall (0 : E) (g (X i ω))
        · exact Metric.isClosed_closedBall
      simpa [Metric.mem_closedBall, dist_zero_right] using hsub hy
    have hxavg := norm_le_average_radius_of_mem_minkowskiAverage
      (Finset.range n) (fun i => closedConvexHull ℝ (F (X i ω)))
      (fun i => g (X i ω)) hHullBound hx
    have hxavg' : ‖x‖ ≤ (∑ i ∈ Finset.range n, g (X i ω)) / n := by
      simpa only [Finset.card_range, div_eq_inv_mul] using hxavg
    exact hxavg'.trans hn
  have hcore : Tendsto
      (fun n => hausdorffDist
        (minkowskiAverage (Finset.range n)
          (fun i => closedConvexHull ℝ (F (X i ω)))) L)
      atTop (nhds 0) := by
    apply tendsto_hausdorffDist_of_tendsto_supportFunction_denseSeq_eventually
      (R := R)
    · intro n
      exact isCompact_minkowskiAverage _ _ (fun i _ =>
        closedConvexHull_compact (hFcompact (X i ω)))
    · exact hLcompact
    · intro n
      exact nonempty_minkowskiAverage _ _ (fun i _ =>
        (hFne (X i ω)).mono subset_closedConvexHull)
    · exact hLne
    · intro n
      exact convex_minkowskiAverage _ _ (fun _ _ => convex_closedConvexHull)
    · exact convex_closedConvexHull
    · exact hR
    · exact hKbound
    · exact hLbound
    · intro k
      rw [hLsupport k]
      apply Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) (hω k)
      rw [supportFunction_minkowskiAverage]
      · simp only [hsuppHull, Finset.card_range, div_eq_inv_mul]
      · exact fun i _ => closedConvexHull_compact (hFcompact (X i ω))
      · exact fun i _ => (hFne (X i ω)).mono subset_closedConvexHull
  apply Tendsto.congr' _ hcore
  filter_upwards [] with n
  rw [closedConvexHull_minkowskiAverage (Finset.range n)
    (fun i => F (X i ω))
    (fun i _ => hFcompact (X i ω))
    (fun i _ => hFne (X i ω))]

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
