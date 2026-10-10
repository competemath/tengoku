import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.WeakSums

namespace OAI

universe uH uA uB

noncomputable section
namespace LipschitzCounterexample

namespace GraphObstruction
open Filter Topology
open WeakSequences
open scoped ENNReal NNReal
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]
abbrev unitVector (i : ℕ) : RealL2 := lp.single 2 i 1

@[simp] theorem unitVector_coord (i j : ℕ) : unitVector i j = if j = i then 1 else 0 := by
  simp [unitVector, lp.single_apply, Pi.single_apply]

@[simp] theorem norm_unitVector (i : ℕ) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem unitVector_weakNull : WeakNull unitVector := by
  intro f
  let x := (InnerProductSpace.toDual ℝ RealL2).symm f
  have hx (i : ℕ) : f (unitVector i) = x i := by
    rw [← InnerProductSpace.toDual_symm_apply]
    change inner ℝ x (lp.single 2 i (1 : ℝ)) = x i
    simp [lp.inner_single_right]
  simp_rw [hx]
  have hs : Summable (fun i => ‖x i‖ ^ 2) := by
    simpa using (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x).summable
  have ht := hs.tendsto_atTop_zero
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht (ε^2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [dist_zero_right, Real.norm_of_nonneg (sq_nonneg _)] at h
  rw [dist_zero_right]
  nlinarith [norm_nonneg (x n)]

open NullSequences

omit [NormedSpace ℝ H] in
theorem eventually_trunc_small (y : ℕ → C0 (H := H))
    (hy : ∀ i, Tendsto (fun k => y k i) atTop (𝓝 0)) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ‖NullSequences.trunc N (y k)‖ < ε := by
  have h : ∀ᶠ k in atTop, ∀ i ∈ Finset.range N, ‖y k i‖ < ε/2 := by
    apply (Finset.eventually_all _).2
    intro i hi
    simpa only [dist_zero_right] using (hy i).eventually (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [h] with k hk
  apply lt_of_le_of_lt ((NullSequences.norm_le (half_pos hε).le).2 ?_) (half_lt_self hε)
  intro i
  simp only [NullSequences.trunc_apply]
  split_ifs with hi
  · exact (hk i (Finset.mem_range.2 hi)).le
  · simpa using (half_pos hε).le

omit [NormedSpace ℝ H] in
theorem norm_c0_block_le (y : C0 (H := H)) (N M : ℕ) (hNM : N ≤ M) :
    ‖NullSequences.trunc M y - NullSequences.trunc N y‖ ≤ ‖y‖ := by
  apply (NullSequences.norm_le (norm_nonneg _)).2
  intro i
  change ‖NullSequences.trunc M y i - NullSequences.trunc N y i‖ ≤ _
  simp only [NullSequences.trunc_apply]
  by_cases hi : i < N
  · simp [hi, hi.trans_le hNM]
  · by_cases hj : i < M
    · simpa [hi, hj] using norm_apply_le y i
    · simp [hi, hj]

omit [NormedSpace ℝ H] in

theorem norm_sum_blocks_le (y : ℕ → C0 (H := H)) (n : ℕ → ℕ) (hn : StrictMono n)
    (C : ℝ) (hC : 0 ≤ C) (hy : ∀ j, ‖y j‖ ≤ C) (J : ℕ) :
    ‖∑ j ∈ Finset.range J, (NullSequences.trunc (n (j+1)) (y j) -
      NullSequences.trunc (n j) (y j))‖ ≤ C := by
  classical
  apply (NullSequences.norm_le hC).2
  intro i
  rw [NullSequences.sum_apply]
  let z := fun j => NullSequences.trunc (n (j+1)) (y j) - NullSequences.trunc (n j) (y j)
  have hi (j : ℕ) : z j i = if n j ≤ i ∧ i < n (j+1) then y j i else 0 := by
    change NullSequences.trunc (n (j+1)) (y j) i - NullSequences.trunc (n j) (y j) i = _
    simp only [NullSequences.trunc_apply]
    have h := hn (Nat.lt_succ_self j)
    split_ifs <;> simp_all
    all_goals omega
  change ‖∑ j ∈ Finset.range J, z j i‖ ≤ C
  by_cases hex : ∃ j ∈ Finset.range J, n j ≤ i ∧ i < n (j+1)
  · obtain ⟨j, hj, hij⟩ := hex
    rw [Finset.sum_eq_single j]
    · rw [hi, ite_eq_left hij]
      exact (norm_apply_le (y j) i).trans (hy j)
    · intro k hk hkj
      rw [hi, ite_eq_right]
      intro hik
      rcases lt_or_gt_of_ne hkj with hkj | hjk
      · have h := hn.monotone (Nat.succ_le_of_lt hkj)
        change n (k+1) ≤ n j at h
        omega
      · have h := hn.monotone (Nat.succ_le_of_lt hjk)
        change n (j+1) ≤ n k at h
        omega
    · exact fun h => (h hj).elim
  · have hz : ∀ j ∈ Finset.range J, z j i = 0 := by
      intro j hj
      rw [hi, ite_eq_right (fun h => hex ⟨j, hj, h⟩)]
    simpa only [Finset.sum_eq_zero hz, norm_zero] using hC

variable {A : Type uA} {B : Type uB} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem exists_small_unit (T : A →L[ℝ] B) (ε : ℝ)
    (hT : ¬ ∀ x, ε * ‖x‖ ≤ ‖T x‖) : ∃ x, ‖x‖ = 1 ∧ ‖T x‖ < ε := by
  push Not at hT
  obtain ⟨x, hx⟩ := hT
  have hn : 0 < ‖x‖ := norm_pos_iff.2 (by intro h; simp [h] at hx)
  refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  · rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
    apply (inv_mul_lt_iff₀ hn).2
    nlinarith

def c0singleLI (n : ℕ) : RealL2 →ₗᵢ[ℝ] C0 (H := RealL2) where
  toFun := NullSequences.single n
  map_add' := by
    intro x y
    ext i
    by_cases hi : i = n <;> simp [hi]
  map_smul' := by
    intro c x
    ext i
    by_cases hi : i = n <;> simp [hi]
  norm_map' := NullSequences.norm_single n

def diagonalFun (t : ℕ → RealL2) (ht : ∀ n, ‖t n‖ = 1) (a : ScalarC0) : C0 (H := RealL2) :=
  ofTendsto (fun n => a n • t n) (by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    simpa only [norm_smul, ht, mul_one, norm_zero] using (NullSequences.tendsto_zero a).norm)

def diagonal (t : ℕ → RealL2) (ht : ∀ n, ‖t n‖ = 1) : ScalarC0 →ₗᵢ[ℝ] C0 (H := RealL2) where
  toFun := diagonalFun t ht
  map_add' := by
    intro a b
    apply ZeroAtInftyContinuousMap.ext
    intro n
    exact add_smul (a n) (b n) (t n)
  map_smul' := by
    intro c a
    apply ZeroAtInftyContinuousMap.ext
    intro n
    exact mul_smul c (a n) (t n)
  norm_map' := by
    intro a
    apply le_antisymm
    · apply (NullSequences.norm_le (norm_nonneg a)).2
      intro n
      change ‖a n • t n‖ ≤ ‖a‖
      rw [norm_smul, ht, mul_one]
      exact norm_apply_le a n
    · apply (NullSequences.norm_le (norm_nonneg _)).2
      intro n
      calc
        ‖a n‖ = ‖a n • t n‖ := by rw [norm_smul, ht, mul_one]
        _ ≤ _ := norm_apply_le (diagonalFun t ht a) n

@[simp] theorem diagonal_apply (t : ℕ → RealL2) (ht : ∀ n, ‖t n‖ = 1) (a : ScalarC0) (n : ℕ) :
    diagonal t ht a n = a n • t n := rfl

variable [CompleteSpace A] [CompleteSpace H]

def first (Q : A →L[ℝ] H) : WeightedGraph.Space Q →L[ℝ] WeightedGraph.L1 A :=
  (ContinuousLinearMap.fst ℝ (WeightedGraph.L1 A) (WeightedGraph.C0 H)).comp
    (WeightedGraph.inclusion Q).toContinuousLinearMap

end GraphObstruction

end LipschitzCounterexample
end

end OAI
