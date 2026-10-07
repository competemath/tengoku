/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Band.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Band.Order
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Internal.Assembly

/-!
# A good sample for the band-jump decomposition

Fix `0 < c < T`. The band-jump decomposition (`Gaussian.Band.Order`) needs bounds at the
thresholds outside the band `[-c, c)` and, for every block of band edges, on the vertices
straddling `±c` plus the vertices of the block. Take the blocks to be the band clusters.

* Outside the band, a low grid on `[-T, -c]` and a high grid on `[c, T]` with `M` steps each,
  and the two tails, are controlled by second-moment deviations as for the edge-score
  decomposition. Every grid point `t` has `|t| ≥ c`, so its straddling probability is at most
  `exp (-c²/2) · frontierBound ρ₀`.
* The vertices of a block lie in one band cluster. Either that cluster has at most `K`
  vertices, or all of them lie in clusters of more than `K` vertices. If the expected number
  of the latter is at most `η h`, Markov's inequality keeps it below `2 η h` with probability
  at least `1/2`.

For large cubic graphs some sample avoids every bad event, and the bags of its band-jump
decomposition have at most `h · bandLayoutBound ρ₀ c T ε η M + K` vertices.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory
open scoped Classical

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-! ### Measurability of the cluster event -/

/-- The graph of the edges of `H` selected by a Boolean mask. -/
def maskGraph (β : Sym2 W → Bool) : SimpleGraph W where
  Adj u v := H.Adj u v ∧ β s(u, v) = true
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun u h => H.ne_of_adj h.1 rfl⟩

omit [Fintype W] [DecidableEq W] [DecidableRel H.Adj] in
theorem bandGraph_eq_maskGraph (score : Sym2 W → ℝ) (c : ℝ) :
    bandGraph H score c = maskGraph H (fun e => decide (-c ≤ score e ∧ score e < c)) := by
  ext u v
  simp [bandGraph, maskGraph]

omit [DecidableEq W] [DecidableRel H.Adj] in
/-- The cluster event depends on the sample only through the finitely many band indicators. -/
theorem measurableSet_bigBandEvent (q : ℝ) (R : ℕ) (c : ℝ) (K : ℕ) (v : W) :
    MeasurableSet (bigBandEvent H q R c K v) := by
  set f : (W → ℝ) → Sym2 W → Bool := fun ω e =>
    decide (-c ≤ edgeScore H q R ω e ∧ edgeScore H q R ω e < c) with hf
  have hmeas : Measurable f := by
    refine measurable_pi_iff.mpr fun e => measurable_to_bool ?_
    have : (fun ω => f ω e) ⁻¹' {true} =
        {ω | -c ≤ edgeScore H q R ω e} ∩ {ω | edgeScore H q R ω e < c} := by
      ext ω
      simp [hf]
    rw [this]
    exact (measurableSet_le measurable_const (measurable_edgeScore H q R e)).inter
      (measurableSet_lt (measurable_edgeScore H q R e) measurable_const)
  have : bigBandEvent H q R c K v = f ⁻¹' {β | K < (Finset.univ.filter fun u =>
      (maskGraph H β).Reachable v u).card} := by
    ext ω
    simp only [bigBandEvent, Set.mem_ofPred_eq, Set.mem_preimage, hf]
    rw [bandGraph_eq_maskGraph]
  rw [this]
  exact (Set.to_countable _).measurableSet.preimage hmeas

omit [DecidableRel H.Adj] in
theorem mem_bigBandEvent {q : ℝ} {R : ℕ} {c : ℝ} {K : ℕ} {v : W} {ω : W → ℝ} :
    ω ∈ bigBandEvent H q R c K v ↔
      K < (Finset.univ.filter fun u =>
        (bandGraph H (edgeScore H q R ω) c).Reachable v u).card := by
  simp only [bigBandEvent, Set.mem_ofPred_eq]
  convert Iff.rfl

/-! ### Blocks of band edges -/

/-- The block of an edge: the index of the band cluster of one of its endpoints. -/
noncomputable def bandBlock (score : Sym2 W → ℝ) (c : ℝ) (e : Sym2 W) : ℕ :=
  (Fintype.equivFin (bandGraph H score c).ConnectedComponent
    ((bandGraph H score c).connectedComponentMk (Quot.out e).1) : ℕ)

omit [Fintype W] [DecidableEq W] [DecidableRel H.Adj] in
/-- A band edge of `H` at `v` lies in the band cluster of `v`. -/
theorem connectedComponentMk_out_eq {score : Sym2 W → ℝ} {c : ℝ} {e : Sym2 W}
    (he : e ∈ H.edgeSet) (hband : -c ≤ score e ∧ score e < c) {v : W} (hv : v ∈ e) :
    (bandGraph H score c).connectedComponentMk (Quot.out e).1 =
      (bandGraph H score c).connectedComponentMk v := by
  have hout : s((Quot.out e).1, (Quot.out e).2) = e := Quot.out_eq e
  rw [← hout] at he hband hv
  have hadj : (bandGraph H score c).Adj (Quot.out e).1 (Quot.out e).2 :=
    ⟨(SimpleGraph.mem_edgeSet H).mp he, hband⟩
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · rfl
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj

/-- **Vertices of a block.** The vertices touching the band edges of one block lie in one
band cluster, so they number at most `K` or lie in clusters of more than `K` vertices. -/
theorem card_filter_bandBlock_le (score : Sym2 W → ℝ) (c : ℝ) (K j : ℕ) :
    ((Finset.univ.filter fun v => ∃ e ∈ H.edgeFinset, v ∈ e ∧ -c ≤ score e ∧ score e < c ∧
        bandBlock H score c e = j).card : ℝ) ≤
      K + ((Finset.univ.filter fun v => K < (Finset.univ.filter fun u =>
        (bandGraph H score c).Reachable v u).card).card : ℝ) := by
  set G := bandGraph H score c
  set S := Finset.univ.filter fun v => ∃ e ∈ H.edgeFinset, v ∈ e ∧ -c ≤ score e ∧
    score e < c ∧ bandBlock H score c e = j
  set Big := Finset.univ.filter fun v => K < (Finset.univ.filter fun u => G.Reachable v u).card
  -- Any two vertices of the block are joined in the band graph.
  have joined : ∀ v ∈ S, ∀ w ∈ S, G.Reachable v w := by
    intro v hv w hw
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_edgeFinset]
      at hv hw
    obtain ⟨e, he, hve, h₁, h₂, hej⟩ := hv
    obtain ⟨e', he', hwe', h₁', h₂', hej'⟩ := hw
    have hblock : bandBlock H score c e = bandBlock H score c e' := hej.trans hej'.symm
    unfold bandBlock at hblock
    rw [connectedComponentMk_out_eq H he ⟨h₁, h₂⟩ hve,
      connectedComponentMk_out_eq H he' ⟨h₁', h₂'⟩ hwe'] at hblock
    exact SimpleGraph.ConnectedComponent.eq.mp
      ((Fintype.equivFin _).injective (Fin.val_injective hblock))
  have hS : S.card ≤ max K Big.card := by
    rcases S.eq_empty_or_nonempty with h | ⟨v₀, hv₀⟩
    · rw [h, Finset.card_empty]
      exact Nat.zero_le _
    have hsub : S ⊆ Finset.univ.filter fun u => G.Reachable v₀ u := fun w hw =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, joined v₀ hv₀ w hw⟩
    by_cases hsmall : (Finset.univ.filter fun u => G.Reachable v₀ u).card ≤ K
    · exact ((Finset.card_le_card hsub).trans hsmall).trans (le_max_left _ _)
    · refine (Finset.card_le_card fun w hw => ?_).trans (le_max_right _ _)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hreach : (Finset.univ.filter fun u => G.Reachable w u) =
          Finset.univ.filter fun u => G.Reachable v₀ u := by
        refine Finset.filter_congr fun u _ => ?_
        have h := joined v₀ hv₀ w hw
        exact ⟨fun hwu => h.trans hwu, fun hvu => h.symm.trans hvu⟩
      rw [hreach]
      exact not_le.mp hsmall
  have : (S.card : ℝ) ≤ max (K : ℝ) Big.card := by exact_mod_cast hS
  exact this.trans (max_le (le_add_of_nonneg_right (Nat.cast_nonneg _))
    (le_add_of_nonneg_left (Nat.cast_nonneg _)))

/-! ### Markov's inequality for a count of events -/

/-- If the expected number of events is at most `m > 0`, at least `2 m` of them occur with
probability at most `1/2`. -/
theorem measureReal_two_mul_le_sum_indicator_le {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (F : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i ∈ F, MeasurableSet (A i)) {m : ℝ} (hm : 0 < m)
    (hsum : ∑ i ∈ F, μ.real (A i) ≤ m) :
    μ.real {ω | 2 * m ≤ ∑ i ∈ F, (A i).indicator (fun _ => (1 : ℝ)) ω} ≤ 1 / 2 := by
  have hint : ∀ i ∈ F, Integrable ((A i).indicator (fun _ => (1 : ℝ))) μ :=
    fun i hi => (integrable_const (1 : ℝ)).indicator (hA i hi)
  have markov := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun ω => ∑ i ∈ F, (A i).indicator (fun _ => (1 : ℝ)) ω)
    (Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun i _ =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (integrable_finsetSum _ hint) (2 * m)
  rw [integral_finsetSum _ hint] at markov
  have hmean : ∑ i ∈ F, ∫ ω, (A i).indicator (fun _ => (1 : ℝ)) ω ∂μ =
      ∑ i ∈ F, μ.real (A i) :=
    Finset.sum_congr rfl fun i hi => by
      rw [integral_indicator_const _ (hA i hi), smul_eq_mul, mul_one]
  rw [hmean] at markov
  have hP := measureReal_nonneg (μ := μ) (s := {ω | 2 * m ≤ ∑ i ∈ F,
    (A i).indicator (fun _ => (1 : ℝ)) ω})
  nlinarith

/-! ### The good sample -/

/-- The bag bound of the band-jump decomposition with the given parameters, per vertex, before
the additive cluster size `K`. -/
noncomputable def bandLayoutBound (ρ₀ c T ε η : ℝ) (M : ℕ) : ℝ :=
  max (3 / T ^ 2 + 2 * ε)
    (Real.exp (-(c ^ 2) / 2) * frontierBound ρ₀ + 3 * ((T - c) / M) / Real.sqrt (2 * Real.pi) +
      3 * ε + 2 * η)

theorem frontierBound_nonneg (ρ₀ : ℝ) : 0 ≤ frontierBound ρ₀ := by
  unfold frontierBound
  have := Real.arccos_nonneg ((1 + 3 * ρ₀) / 4)
  have := Real.pi_pos
  positivity

end Algebraic.Cutwidth.Gaussian.Internal
