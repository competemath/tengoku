import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.EntropyTopology
import Tengoku.Seed.Topology.MetricSpace.Pseudo.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Finite-coordinate replacements and their genuine ℓ¹ topology. -/

namespace EntropyConstrainedMissingMass.ProbabilityVector
noncomputable section
open Filter
open scoped Topology
variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq ι

/-- Replacing finitely many values changes a summable statistic by its finite difference.
@isnad1 id=hassum.1h5v.s6.b6a26a18fa0c from=translated src=- shape=71ac530e vocab=9b8276bf
-/
theorem hasSum_finite_replacement (s : Finset ι) (f g : ι → ℝ) {a : ℝ}
    (hf : HasSum f a) :
    HasSum (fun i => if i ∈ s then g i else f i) (a + ∑ i ∈ s, (g i - f i)) := by
  classical
  let d := fun i => if i ∈ s then g i - f i else 0
  have hd : HasSum d (∑ i ∈ s, (g i - f i)) := by
    convert hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ι) (s := s) (f := d) (fun i hi => by simp [d, hi]) using 1
    exact Finset.sum_congr rfl (fun i hi => by simp [d, hi])
  convert hf.add hd using 1
  ext i
  by_cases hi : i ∈ s <;> simp [d, hi]

/-- An actual probability vector obtained by a finite normalized replacement.-/
def replaceFinite (p : ProbabilityVector ι) (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hsum : ∑ i ∈ s, g i = ∑ i ∈ s, p.coord i) :
    ProbabilityVector ι := by
  classical
  apply ofHasSum (fun i => if i ∈ s then g i else p.coord i)
  · intro i
    split_ifs with hi
    · exact hg i hi
    · exact p.coord_nonneg i
  · have h := hasSum_finite_replacement s p.coord g p.hasSum_coord
    simpa only [Finset.sum_sub_distrib, hsum, sub_self, add_zero] using h

/--
@isnad1 id=eq.2h5v.s6.beec0a5655ea from=translated src=- shape=22c35410 vocab=4eb58f5e
-/
@[simp] theorem coord_replaceFinite (p : ProbabilityVector ι) (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hsum : ∑ i ∈ s, g i = ∑ i ∈ s, p.coord i) (i : ι) :
    (p.replaceFinite s g hg hsum).coord i = if i ∈ s then g i else p.coord i := by
  classical
  rfl

/-- Exact finite expression for the ℓ¹ distance whenever other coordinates agree.
@isnad1 id=eq.1h4v.s6.42d9fa2905a2 from=translated src=- shape=fe979a0c vocab=1b8c1158
-/
theorem dist_eq_sum_of_eq_off (p q : ProbabilityVector ι) (s : Finset ι)
    (heq : ∀ i ∉ s, p.coord i = q.coord i) :
    dist p q = ∑ i ∈ s, |p.coord i - q.coord i| := by
  rw [dist_eq_tsum]
  exact tsum_eq_sum (fun i hi => by rw [heq i hi]; simp)

/--
@isnad1 id=eq.2h4v.s6.011701ce610c from=translated src=- shape=8c48ef51 vocab=4f025c13
-/
theorem dist_replaceFinite (p : ProbabilityVector ι) (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hsum : ∑ i ∈ s, g i = ∑ i ∈ s, p.coord i) :
    dist (p.replaceFinite s g hg hsum) p = ∑ i ∈ s, |g i - p.coord i| := by
  classical
  rw [dist_eq_sum_of_eq_off _ _ s (fun i hi => by simp [hi])]
  exact Finset.sum_congr rfl (fun i hi => by simp [hi])

/-- Coordinatewise convergence of a fixed finite perturbation implies ℓ¹ convergence.
@isnad1 id=tendsto.2h6v.s6.bc1e7d71e3db from=translated src=- shape=d39d582a vocab=3850eb78
-/
theorem tendsto_of_finite_coordinate_tendsto {α : Type*} {l : Filter α}
    (p : ProbabilityVector ι) (q : α → ProbabilityVector ι) (s : Finset ι)
    (hoff : ∀ᶠ a in l, ∀ i ∉ s, (q a).coord i = p.coord i)
    (hlim : ∀ i ∈ s, Tendsto (fun a => (q a).coord i) l (𝓝 (p.coord i))) :
    Tendsto q l (𝓝 p) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hsum : Tendsto (fun a => ∑ i ∈ s, |(q a).coord i - p.coord i|) l (𝓝 0) := by
    have h := tendsto_finsetSum s (fun i hi => ((hlim i hi).sub (tendsto_const_nhds (x := p.coord i))).abs)
    simpa using h
  apply hsum.congr'
  filter_upwards [hoff] with a ha
  exact (dist_eq_sum_of_eq_off (q a) p s ha).symm

/-- Every summable scalar statistic has the expected finite replacement formula.
@isnad1 id=hassum.3h5v.s7.565af2d0df06 from=translated src=- shape=f9217008 vocab=cea1b471
-/
theorem statistic_replaceFinite (p : ProbabilityVector ι) (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hsum : ∑ i ∈ s, g i = ∑ i ∈ s, p.coord i)
    (f : ℝ → ℝ) (hf : Summable (fun i => f (p.coord i))) :
    HasSum (fun i => f ((p.replaceFinite s g hg hsum).coord i))
      ((∑' i, f (p.coord i)) + ∑ i ∈ s, (f (g i) - f (p.coord i))) := by
  classical
  convert hasSum_finite_replacement s (fun i => f (p.coord i)) (fun i => f (g i)) hf.hasSum using 1
  ext i
  by_cases hi : i ∈ s <;> simp [hi]

/--
@isnad1 id=ne.3h4v.s6.2773c6890f18 from=translated src=- shape=c301787b vocab=f891e8f3
-/
theorem entropy_replaceFinite_ne_top (p : ProbabilityVector ι) (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hsum : ∑ i ∈ s, g i = ∑ i ∈ s, p.coord i)
    (hp : p.entropy ≠ ⊤) : (p.replaceFinite s g hg hsum).entropy ≠ ⊤ :=
  (entropy_ne_top_iff _).mpr
    ((statistic_replaceFinite p s g hg hsum Real.negMulLog (p.entropy_ne_top_iff.mp hp)).summable)

/--
@isnad1 id=eq.3h4v.s6.709f76ceeb60 from=translated src=- shape=0893ec58 vocab=429d4784
-/
theorem entropy_toReal_replaceFinite (p : ProbabilityVector ι) (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hsum : ∑ i ∈ s, g i = ∑ i ∈ s, p.coord i)
    (hp : p.entropy ≠ ⊤) :
    (p.replaceFinite s g hg hsum).entropy.toReal = p.entropy.toReal +
      ∑ i ∈ s, (Real.negMulLog (g i) - Real.negMulLog (p.coord i)) := by
  rw [entropy_toReal _ (entropy_replaceFinite_ne_top p s g hg hsum hp),
    (statistic_replaceFinite p s g hg hsum Real.negMulLog (p.entropy_ne_top_iff.mp hp)).tsum_eq,
    p.entropy_toReal hp]

/--
@isnad1 id=eq.2h5v.s6.6b5718fd6832 from=translated src=- shape=28ded6ee vocab=b5f1ecbe
-/
theorem objective_replaceFinite (p : ProbabilityVector ι) (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hsum : ∑ i ∈ s, g i = ∑ i ∈ s, p.coord i) (t : ℕ) :
    (p.replaceFinite s g hg hsum).objective t = p.objective t +
      ∑ i ∈ s, (missingMassTerm t (g i) - missingMassTerm t (p.coord i)) :=
  (statistic_replaceFinite p s g hg hsum (missingMassTerm t) (p.objective_summable t)).tsum_eq

end
end EntropyConstrainedMissingMass.ProbabilityVector
