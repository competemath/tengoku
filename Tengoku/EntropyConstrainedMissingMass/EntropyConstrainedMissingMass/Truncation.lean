import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.Coarsening
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.SortedCompactness
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.ObjectiveContinuity
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.FiniteSorting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Finite approximations obtained by coalescing the tail of a countable distribution. -/

set_option backward.isDefEq.respectTransparency false

namespace EntropyConstrainedMissingMass.ProbabilityVector

/-- The mass after a finite prefix is the complement of that prefix mass.
@isnad1 id=eq.0h2v.s6.6669d182ac3a from=translated src=- shape=3793235e vocab=8e07de87
-/
theorem tail_eq_one_sub_sum (p : ProbabilityVector ℕ) (N : ℕ) :
    (∑' i : {n : ℕ // N ≤ n}, p.coord i) = 1 - ∑ i ∈ Finset.range N, p.coord i := by
  have hs := p.summable_coord.sum_add_tsum_compl (s := Finset.range N)
  have hset : (↑(Finset.range N) : Set ℕ)ᶜ = {n | N ≤ n} := by ext n; simp
  rw [hset, p.tsum_coord] at hs
  change (∑ i ∈ Finset.range N, p.coord i) + (∑' i : {n : ℕ // N ≤ n}, p.coord i) = 1 at hs
  linarith

/-- Every individual probability vector has vanishing tails, without an entropy assumption.
@isnad1 id=tendsto.0h1v.s6.8a72cf3831b7 from=translated src=- shape=e3941929 vocab=4bb736d1
-/
theorem tendsto_tail_zero (p : ProbabilityVector ℕ) :
    Filter.Tendsto (fun N : ℕ => ∑' i : {n : ℕ // N ≤ n}, p.coord i) Filter.atTop (nhds 0) := by
  simp_rw [p.tail_eq_one_sub_sum]
  have hs := p.summable_coord.hasSum.tendsto_sum_nat
  rw [p.tsum_coord] at hs
  simpa using hs.const_sub 1

/-- Preserving an initial prefix costs at most twice the discarded mass in ℓ¹.
@isnad1 id=le.1h3v.s6.9bf71d068283 from=translated src=- shape=f74befd4 vocab=37461e6e
-/
theorem dist_le_two_tail_of_prefix_eq (p q : ProbabilityVector ℕ) (N : ℕ)
    (hpq : ∀ i < N, q.coord i = p.coord i) :
    dist p q ≤ 2 * (∑' i : {n : ℕ // N ≤ n}, p.coord i) := by
  have hprefix : (∑ i ∈ Finset.range N, |p.coord i - q.coord i|) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hpq i (Finset.mem_range.mp hi), sub_self, abs_zero]
  have htail : (∑' i : {n : ℕ // N ≤ n}, q.coord i) = ∑' i : {n : ℕ // N ≤ n}, p.coord i := by
    rw [q.tail_eq_one_sub_sum, p.tail_eq_one_sub_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact hpq i (Finset.mem_range.mp hi)
  have hd := dist_le_prefix_add_tails p q N
  rw [hprefix, htail] at hd
  linarith

/-- Keep the first `N` symbols and send the entire remaining tail to one last symbol.-/
def truncationMap (N : ℕ) (n : ℕ) : Fin (N + 1) :=
  ⟨min n N, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- The finite distribution retaining the first `N` atoms and merging its remaining tail.-/
noncomputable def truncate (p : ProbabilityVector ℕ) (N : ℕ) : ProbabilityVector (Fin (N + 1)) :=
  p.pushforward (truncationMap N)

/--
@isnad1 id=eq.1h2v.s6.d97f5daef458 from=translated src=- shape=8a75b162 vocab=1f2d4694
-/
theorem truncationMap_fiber_lt (N i : ℕ) (hi : i < N) :
    (truncationMap N) ⁻¹' {⟨i, Nat.lt_succ_of_lt hi⟩} = {i} := by
  ext n
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hn
    have hv := congrArg Fin.val hn
    dsimp [truncationMap] at hv
    omega
  · rintro rfl
    apply Fin.ext
    exact Nat.min_eq_left hi.le

/--
@isnad1 id=eq.1h3v.s5.c6901623b661 from=translated src=- shape=404ed045 vocab=f206019f
-/
@[simp] theorem coord_truncate_lt (p : ProbabilityVector ℕ) (N i : ℕ) (hi : i < N) :
    (p.truncate N).coord ⟨i, Nat.lt_succ_of_lt hi⟩ = p.coord i := by
  rw [truncate, coord_pushforward, truncationMap_fiber_lt N i hi]
  simp

/--
@isnad1 id=le.0h2v.s4.606f30d4ae4c from=translated src=- shape=1c4a968b vocab=77e5efdc
-/
theorem entropy_truncate_le (p : ProbabilityVector ℕ) (N : ℕ) :
    (p.truncate N).entropy ≤ p.entropy := p.entropy_pushforward_le _

/--
@isnad1 id=mem.1h3v.s6.22cc7e0b2a6a from=translated src=- shape=542c963f vocab=9e8b2669
-/
theorem feasible_truncate (p : ProbabilityVector ℕ) {h : ℝ} (hp : p ∈ Feasible h) (N : ℕ) :
    p.truncate N ∈ Feasible h := (p.entropy_truncate_le N).trans hp

/-- Regard the finite tail-coalescing approximation as a countable probability vector.-/
noncomputable def truncateNat (p : ProbabilityVector ℕ) (N : ℕ) : ProbabilityVector ℕ :=
  zeroExtend ⟨Fin.val, Fin.val_injective⟩ (p.truncate N)

/--
@isnad1 id=eq.1h3v.s4.528a37ed7a77 from=translated src=- shape=a6974ed7 vocab=27c51f57
-/
@[simp] theorem coord_truncateNat_lt (p : ProbabilityVector ℕ) (N i : ℕ) (hi : i < N) :
    (p.truncateNat N).coord i = p.coord i := by
  have hc := coord_zeroExtend_apply (⟨Fin.val, Fin.val_injective⟩ : Fin (N + 1) ↪ ℕ)
    (p.truncate N) ⟨i, Nat.lt_succ_of_lt hi⟩
  exact hc.trans (p.coord_truncate_lt N i hi)

/-- The unsorted finite approximations converge in the manuscript's ℓ¹ metric.
@isnad1 id=tendsto.0h1v.s4.e561b7fb18be from=translated src=- shape=0b9404f4 vocab=60781321
-/
theorem tendsto_truncateNat (p : ProbabilityVector ℕ) :
    Filter.Tendsto p.truncateNat Filter.atTop (nhds p) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (g := fun N => 2 * (∑' i : {n : ℕ // N ≤ n}, p.coord i)) (fun _ => dist_nonneg)
  · intro N
    rw [dist_comm]
    exact dist_le_two_tail_of_prefix_eq p (p.truncateNat N) N (p.coord_truncateNat_lt N)
  · simpa using p.tendsto_tail_zero.const_mul 2

/-- Exact one-sided objective error estimate for the finite coarsening.
@isnad1 id=le.0h3v.s6.fcff2f254ed1 from=translated src=- shape=92608eca vocab=762d287e
-/
theorem objective_sub_truncate_le_tail (p : ProbabilityVector ℕ) (N t : ℕ) :
    p.objective t - (p.truncate N).objective t ≤ ∑' i : {n : ℕ // N ≤ n}, p.coord i := by
  have hs := (p.objective_summable t).sum_add_tsum_compl (s := Finset.range N)
  have hset : (↑(Finset.range N) : Set ℕ)ᶜ = {n | N ≤ n} := by ext n; simp
  rw [hset] at hs
  change (∑ i ∈ Finset.range N, missingMassTerm t (p.coord i)) +
    (∑' i : {n : ℕ // N ≤ n}, missingMassTerm t (p.coord i)) = p.objective t at hs
  have hprefix : (∑ i ∈ Finset.range N, missingMassTerm t (p.coord i)) ≤
      (p.truncateNat N).objective t := by
    have heq : (∑ i ∈ Finset.range N, missingMassTerm t (p.coord i)) =
        ∑ i ∈ Finset.range N, missingMassTerm t ((p.truncateNat N).coord i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [p.coord_truncateNat_lt N i (Finset.mem_range.mp hi)]
    rw [heq]
    exact (p.truncateNat N).objective_summable t |>.sum_le_tsum _
      (fun i _ => missingMassTerm_nonneg _ ((p.truncateNat N).coord_nonneg i)
        ((p.truncateNat N).coord_le_one i))
  have ht : (∑' i : {n : ℕ // N ≤ n}, missingMassTerm t (p.coord i)) ≤
      ∑' i : {n : ℕ // N ≤ n}, p.coord i :=
    ((p.objective_summable t).subtype (N ≤ ·)).tsum_le_tsum
      (fun i => missingMassTerm_le _ (p.coord_nonneg i) (p.coord_le_one i))
      (p.summable_coord.subtype (N ≤ ·))
  simp only [truncateNat, objective_zeroExtend] at hprefix
  linarith

/-- The absolute objective error is at most the original tail mass.
@isnad1 id=le.0h3v.s6.0b1d0668717c from=translated src=- shape=b7588d6c vocab=97b8abd0
-/
theorem abs_objective_truncate_sub_le_tail (p : ProbabilityVector ℕ) (N t : ℕ) :
    |(p.truncate N).objective t - p.objective t| ≤ ∑' i : {n : ℕ // N ≤ n}, p.coord i := by
  have hle : (p.truncate N).objective t ≤ p.objective t := p.objective_pushforward_le (truncationMap N) t
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
  exact p.objective_sub_truncate_le_tail N t

/-- Missing mass of finite coarsenings converges to missing mass of the original distribution.
@isnad1 id=tendsto.0h2v.s5.749f4092da3f from=translated src=- shape=9446be77 vocab=7b9b839f
-/
theorem tendsto_objective_truncate (p : ProbabilityVector ℕ) (t : ℕ) :
    Filter.Tendsto (fun N => (p.truncate N).objective t) Filter.atTop (nhds (p.objective t)) := by
  have ht := (continuous_objective t).tendsto p |>.comp p.tendsto_truncateNat
  simpa only [Function.comp_def, truncateNat, objective_zeroExtend] using ht

end EntropyConstrainedMissingMass.ProbabilityVector
