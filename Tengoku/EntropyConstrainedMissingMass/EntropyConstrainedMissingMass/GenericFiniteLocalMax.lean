import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.EmbeddedPerturbation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Finite-coordinate local maximality for arbitrary summable atom statistics.
The bridge starts from actual ℓ¹ local maximality, not stationarity. -/

namespace EntropyConstrainedMissingMass
noncomputable section
open Filter Set
open scoped Topology

def finiteEntropyConstraint {n : ℕ} (a : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ (∑ i, v i = ∑ i, a i) ∧
    (∑ i, Real.negMulLog (v i)) ≤ ∑ i, Real.negMulLog (a i)}

namespace ProbabilityVector
variable {ι : Type*} {n : ℕ}

/-- Local maximality under every finite-coordinate, mass-preserving, entropy-nonincreasing change.-/
def StatisticFiniteLocalMax (f : ℝ → ℝ) (p : ProbabilityVector ι) : Prop :=
  ∀ (n : ℕ) (e : Fin n ↪ ι),
    IsLocalMaxOn (fun v : Fin n → ℝ => ∑ i, f (v i))
      (finiteEntropyConstraint (fun i => p.coord (e i))) (fun i => p.coord (e i))

/--
@isnad1 id=eq.3h6v.s7.ee464fd6e6af from=translated src=- shape=cf96f7fe vocab=f1338ddb
-/
theorem statistic_replaceEmbedded (p : ProbabilityVector ι) (e : Fin n ↪ ι)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hsum : ∑ i, v i = ∑ i, p.coord (e i))
    (f : ℝ → ℝ) (hf : Summable (fun i => f (p.coord i))) :
    (∑' i, f ((p.replaceEmbedded e v hv hsum).coord i)) = (∑' i, f (p.coord i)) +
      (∑ i, f (v i)) - ∑ i, f (p.coord (e i)) := by
  classical
  rw [replaceEmbedded, (statistic_replaceFinite _ _ _ _ _ f hf).tsum_eq, Finset.sum_map]
  simp only [e.injective.extend_apply, Finset.sum_sub_distrib]
  ring

/-- Every actual local maximum of a well-defined atom sum induces the finite-coordinate problem.
@isnad1 id=statisti.3h4v.s6.4a1eab4a1993 from=translated src=- shape=499ac525 vocab=330ea9ba
-/
theorem statisticFiniteLocalMax_of_localMax {h : ℝ} (p : ProbabilityVector ι)
    (hp : p ∈ Feasible h) (f : ℝ → ℝ) (hf : Summable (fun i => f (p.coord i)))
    (hm : IsLocalMaxOn (fun q : ProbabilityVector ι => ∑' i, f (q.coord i)) (Feasible h) p) :
    StatisticFiniteLocalMax f p := by
  intro n e
  let a := fun i => p.coord (e i)
  let S := finiteEntropyConstraint a
  have hfin := finite_entropy_of_feasible hp
  have hlim : Tendsto (fun v : Fin n → ℝ => p.perturbEmbedded e v)
      (𝓝[S] a) (𝓝 p) :=
    tendsto_perturbEmbedded p e id (fun i =>
      (continuous_apply i).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hfeas : ∀ᶠ v in 𝓝[S] a, p.perturbEmbedded e v ∈ Feasible h := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    rw [perturbEmbedded_eq p e v hv.1 hv.2.1]
    change (p.replaceEmbedded e v hv.1 hv.2.1).entropy ≤ ENNReal.ofReal h
    apply le_trans _ (show p.entropy ≤ ENNReal.ofReal h from hp)
    apply (ENNReal.toReal_le_toReal (entropy_replaceEmbedded_ne_top p e v hv.1 hv.2.1 hfin) hfin).mp
    rw [entropy_toReal_replaceEmbedded p e v hv.1 hv.2.1 hfin]
    linarith [hv.2.2]
  have ht : Tendsto (fun v : Fin n → ℝ => p.perturbEmbedded e v)
      (𝓝[S] a) (𝓝[Feasible h] p) := tendsto_nhdsWithin_iff.mpr ⟨hlim, hfeas⟩
  have hmax := ht.eventually hm
  filter_upwards [hmax, self_mem_nhdsWithin] with v hmv hv
  rw [perturbEmbedded_eq p e v hv.1 hv.2.1, statistic_replaceEmbedded p e v hv.1 hv.2.1 f hf] at hmv
  change (∑ i, f (v i)) ≤ ∑ i, f (p.coord (e i))
  linarith

end ProbabilityVector
end
end EntropyConstrainedMissingMass
