import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.CompactLipschitz

namespace OAI

universe uM uI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.LocalizedLinearization
open Filter Set Topology LocalLipschitz
open scoped NNReal ENNReal
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

theorem cutoff_nonzero_mem (z : M) {r : ℝ≥0} (hr : 0 < r) {x : M}
    (hx : cutoff z r x ≠ 0) : x ∈ Metric.ball z r := by
  by_contra hn
  apply hx
  exact cutoff_zero z hr (le_of_not_gt hn)

omit [Fintype I] in
theorem disjoint_cutoffs (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r))) :
    ∀ x j k, cutoff (z j) r x ≠ 0 → cutoff (z k) r x ≠ 0 → j = k := by
  intro x j k hj hk
  by_contra hn
  exact Set.disjoint_left.mp (hdis hn) (cutoff_nonzero_mem _ hr hj) (cutoff_nonzero_mem _ hr hk)

theorem sum_cutoff_bounds (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r))) :
    ∀ x, (∑ j,cutoff (z j) r x) ∈ Icc (0 : ℝ) 1 := by
  classical
  intro x
  refine ⟨Finset.sum_nonneg (fun j _ => cutoff_nonneg _ _ _),?_⟩
  by_cases hx : ∃ j, cutoff (z j) r x ≠ 0
  · obtain ⟨j,hj⟩ := hx
    have heq : ∑ k,cutoff (z k) r x = cutoff (z j) r x := by
      apply Finset.sum_eq_single j
      · intro k hk hkj
        by_contra hk'
        exact hkj (disjoint_cutoffs z hr hdis x k j hk' hj)
      · simp
    rw [heq]
    exact cutoff_le_one _ _ _
  · push Not at hx
    simp [hx]

def removed (d : M → ℝ) (z : I → M) (r : ℝ≥0) (x : M) : ℝ :=
  ∑ j, (d x-d (z j))*cutoff (z j) r x

def remainder (d : M → ℝ) (z : I → M) (r : ℝ≥0) : M → ℝ :=
  weightedRemainder d z (fun j => cutoff (z j) r)

theorem removed_lipschitz (d : M → ℝ) {L : ℝ≥0} (hd : LipschitzWith L d)
    (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r))) :
    LipschitzWith (6*L) (removed d z r) := by
  have hpart (j : I) : LipschitzWith (3*L) (fun x => (d x-d (z j))*cutoff (z j) r x) :=
    cutoff_product_lipschitz _ hr _ (lipschitz_sub_const _ hd _) (sub_self _)
  have ht := disjoint_sum_lipschitz _ hpart (by
    intro x j k hj hk
    apply disjoint_cutoffs z hr hdis x j k
    · exact (mul_ne_zero_iff.mp hj).2
    · exact (mul_ne_zero_iff.mp hk).2)
  have he : 2*(3*L) = 6*L := by ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [he,removed] using ht.dist_le_mul x y

theorem remainder_lipschitz (d : M → ℝ) {L : ℝ≥0} (hd : LipschitzWith L d)
    (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r))) :
    LipschitzWith (7*L) (remainder d z r) := by
  have ht := hd.sub (removed_lipschitz d hd z hr hdis)
  have he : L+6*L = 7*L := by ring
  rw [he] at ht
  exact ht

theorem remainder_inner (d : M → ℝ) (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r)))
    (j : I) {x : M} (hx : x ∈ Metric.ball (z j) ((r : ℝ)/2)) :
    remainder d z r x = d (z j) := by
  classical
  have hj : cutoff (z j) r x = 1 := cutoff_one _ hr hx.le
  have hk (k : I) (hkj : k ≠ j) : cutoff (z k) r x = 0 := by
    by_contra hn
    exact hkj (disjoint_cutoffs z hr hdis x k j hn (by rw [hj]; norm_num))
  have heq : ∑ k, (d x-d (z k))*cutoff (z k) r x = d x-d (z j) := by
    rw [Finset.sum_eq_single j]
    · rw [hj,mul_one]
    · intro k _ hkj
      rw [hk k hkj,mul_zero]
    · simp
  change d x - _ = _
  rw [heq]
  ring

theorem remainder_tendsto_zero (d : ℕ → M → ℝ)
    (hd : ∀ x, Tendsto (fun i => d i x) atTop (𝓝 0)) (z : I → M) (r : ℝ≥0) (x : M) :
    Tendsto (fun i => remainder (d i) z r x) atTop (𝓝 0) := by
  have ht := (hd x).sub (tendsto_finsetSum Finset.univ (fun j _ =>
    ((hd x).sub (hd (z j))).mul_const (cutoff (z j) r x)))
  simpa [remainder,weightedRemainder] using ht

theorem remainder_compact_lipschitz (d : ℕ → M → ℝ) {L : ℝ≥0}
    (hd : ∀ i, LipschitzWith L (d i))
    (hpoint : ∀ x, Tendsto (fun i => d i x) atTop (𝓝 0))
    (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r)))
    {η : ℝ≥0} (hη : 0 < η)
    (hgood : ∀ p, p ∉ Set.range z → ∃ O : Set M, IsOpen O ∧ p ∈ O ∧
      ∀ᶠ i in atTop, LipschitzOnWith η (d i) O)
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ i in atTop, LipschitzOnWith (2*η) (remainder (d i) z r) K := by
  have hR := fun i => remainder_lipschitz (d i) (hd i) z hr hdis
  apply compact_eventual_lipschitz _ hK (by positivity)
  · intro ε hε
    exact uniform_zero_on_compact _ hR (remainder_tendsto_zero d hpoint z r) hK hε
  · intro p hp
    by_cases hpz : p ∈ Set.range z
    · obtain ⟨j,rfl⟩ := hpz
      refine ⟨Metric.ball (z j) ((r : ℝ)/2),Metric.isOpen_ball,
        Metric.mem_ball_self (by exact half_pos hr),?_⟩
      exact Filter.Eventually.of_forall (fun i => LipschitzOnWith.of_dist_le_mul (by
        intro x hx y hy
        rw [remainder_inner (d i) z hr hdis j hx.2,remainder_inner (d i) z hr hdis j hy.2,dist_self]
        positivity))
    · obtain ⟨O,hO,hpO,hOi⟩ := hgood p hpz
      let B : ℝ≥0 := 2/r
      let ε : ℝ≥0 := η/(2*Fintype.card I*B+1)
      have hε : 0 < ε := by dsimp [ε]; positivity
      have hsmall := uniform_zero_on_compact d hd hpoint hK (show (0 : ℝ) < ε from hε)
      have hzsmall : ∀ᶠ i in atTop, ∀ j, |d i (z j)| ≤ (ε : ℝ) := by
        apply Filter.eventually_all.mpr
        intro j
        have ht := (hpoint (z j)).abs
        simp only [abs_zero] at ht
        exact (ht.eventually (eventually_lt_nhds (show (0 : ℝ) < ε from hε))).mono (fun _ hi => hi.le)
      refine ⟨O,hO,hpO,?_⟩
      filter_upwards [hOi,hsmall,hzsmall] with i hi hsi hzi
      apply (weightedRemainder_lipschitzOn (d i) z (fun j => cutoff (z j) r) hi
        (fun j => cutoff_lipschitz _ _) (sum_cutoff_bounds z hr hdis)
        (fun x hx => (hsi x hx).le) hzi).weaken
      have herr : 2*Fintype.card I*B*ε ≤ η := by
        dsimp [ε]
        have hden : 0 < 2*(Fintype.card I : ℝ≥0)*B+1 := by positivity
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hden).mpr
        nlinarith
      dsimp [B] at herr
      nlinarith
end LipschitzCounterexample.LocalizedLinearization

namespace LipschitzCounterexample.LocalizedLinearization
open Filter Set Topology LocalLipschitz
open scoped NNReal ENNReal
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Zero M] [Fintype I]

end LipschitzCounterexample.LocalizedLinearization

namespace LipschitzCounterexample.LocalizedLinearization
open Filter Set Topology LocalLipschitz
open scoped NNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

end LipschitzCounterexample.LocalizedLinearization

end

end OAI
