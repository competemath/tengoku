import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.FiniteMultipliers

namespace OAI

universe uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped Topology
open Filter Set
variable {M : Type uM} [MetricSpace M]

theorem near_isClosed (A : Finset M) (δ : ℝ) : IsClosed (Near A δ) := by
  have he : Near A δ = ⋃ a ∈ A, Metric.closedBall a δ := by
    ext x
    simp only [Near,Set.mem_ofPred_eq,Set.mem_iUnion,Metric.mem_closedBall]
    constructor <;> rintro ⟨a,ha,h⟩ <;> exact ⟨a,ha,h⟩
  rw [he]
  exact isClosed_biUnion_finset (fun _ _ => Metric.isClosed_closedBall)

theorem nested_finite_cover_compact [CompleteSpace M] (K : ℕ → Set M)
    (hc : ∀ n, IsClosed (K n)) (A : ℕ → Finset M) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) (hcover : ∀ n, K (n+1) ⊆ Near (A n) (r n)) :
    IsCompact (⋂ n, K n) := by
  apply isCompact_iff_totallyBounded_isComplete.mpr
  refine ⟨?_,(isClosed_iInter hc).isComplete⟩
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hr ε hε
  have hrN : r N < ε := (le_abs_self _).trans_lt (by simpa only [dist_zero_right,Real.norm_eq_abs] using hN N le_rfl)
  refine ⟨(A N : Set M),(A N).finite_toSet,?_⟩
  intro x hx
  obtain ⟨a,ha,hxa⟩ := hcover N (Set.mem_iInter.mp hx (N+1))
  exact Set.mem_iUnion₂.mpr ⟨a,ha,hxa.trans_lt hrN⟩

theorem nested_finite_cover_range (K : ℕ → Set M) (hanti : Antitone K)
    (A : ℕ → Finset M) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hcover : ∀ n, K (n+1) ⊆ Near (A n) (r n))
    (x : ℕ → M) (hx : ∀ n, x n ∈ K n) : TotallyBounded (Set.range x) := by
  classical
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hr ε hε
  have hrN : r N < ε := (le_abs_self _).trans_lt (by simpa only [dist_zero_right,Real.norm_eq_abs] using hN N le_rfl)
  let F : Finset M := A N ∪ (Finset.range (N+1)).image x
  refine ⟨(F : Set M),F.finite_toSet,?_⟩
  rintro _ ⟨n,rfl⟩
  by_cases hn : n < N+1
  · apply Set.mem_iUnion₂.mpr
    refine ⟨x n,?_,?_⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr hn,rfl⟩)
    · simpa only [Metric.mem_ball,dist_self] using hε
  · obtain ⟨a,ha,hxa⟩ := hcover N (hanti (le_of_not_gt hn) (hx n))
    exact Set.mem_iUnion₂.mpr ⟨a,Finset.mem_union_left _ ha,hxa.trans_lt hrN⟩

theorem nested_finite_cover_uniform [CompleteSpace M] (K : ℕ → Set M)
    (hc : ∀ n, IsClosed (K n)) (hanti : Antitone K)
    (A : ℕ → Finset M) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hcover : ∀ n, K (n+1) ⊆ Near (A n) (r n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ x ∈ K N, ∃ y ∈ ⋂ n, K n, dist x y < ε := by
  classical
  by_contra! h
  choose x hx hfar using h
  have hb := nested_finite_cover_range K hanti A r hr hcover x hx
  have hcompact : IsCompact (closure (Set.range x)) :=
    isCompact_iff_totallyBounded_isComplete.mpr ⟨hb.closure,isClosed_closure.isComplete⟩
  obtain ⟨y,_hy,a,ha,hlim⟩ := hcompact.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  have hy : y ∈ ⋂ n, K n := by
    apply Set.mem_iInter.mpr
    intro n
    apply (hc n).mem_of_tendsto hlim
    filter_upwards [(tendsto_atTop.mp ha.tendsto_atTop) n] with i hi
    exact hanti hi (hx (a i))
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
  exact (not_lt_of_ge (hfar (a N) y hy)) (hN N le_rfl)

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

def clip (ε t : ℝ) : ℝ := max (t-ε) 0 + min (t+ε) 0

end LipschitzCounterexample.FreeSpace

end

end OAI
