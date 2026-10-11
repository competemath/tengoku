import Tengoku.OpenaiMath.OAI.Geometry.PolarProducts.MomentumBounds

namespace OAI

universe u74 u75 u76 u77

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real
open Set
open scoped ContDiff ENNReal

namespace SymmetricPolar
open Set Filter ComplexCoordinates ComplexPotential PolarStrips
open scoped Topology ContDiff
noncomputable section
variable {n : ℕ} {κ : Type u74} [Fintype κ]

theorem exists_positive_slack {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    ∃ η : ℝ, 0 < η ∧ (1+η)*c < d := by
  let η := (d-c)/(2*c)
  have hη : 0 < η := div_pos (sub_pos.mpr hcd) (mul_pos (by norm_num) hc)
  have he : η*c = (d-c)/2 := by dsimp [η]; field_simp
  exact ⟨η, hη, by nlinarith⟩

end
end SymmetricPolar

namespace ConvexPolar
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type u75} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem zero_mem_interior_of_symmetric {K : Set E} (hK : Convex ℝ K)
    (hi : (interior K).Nonempty) (hs : ∀ x, x ∈ K ↔ -x ∈ K) : (0 : E) ∈ interior K := by
  obtain ⟨x, hx⟩ := hi
  have hn : -x ∈ interior K := by
    apply mem_interior_iff_mem_nhds.mpr
    have hh : K ∈ 𝓝 (-(-x)) := by simpa using mem_interior_iff_mem_nhds.mp hx
    have hh' := continuous_neg.continuousAt.preimage_mem_nhds hh
    have he : (fun y : E => -y) ⁻¹' K = K := by ext y; exact (hs y).symm
    rwa [he] at hh'
  have hm := hK.interior hx hn (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ)+1/2 = 1)
  simpa using hm

theorem isClosed_polar (K : Set E) : IsClosed (polar K) := by
  have he : polar K = ⋂ q ∈ K, {p : E | inner (𝕜 := ℝ) q p ≤ 1} := by ext p; simp [polar]
  rw [he]
  exact isClosed_biInter (fun q _ => isClosed_le (by fun_prop) continuous_const)

theorem polar_abs_pairing {K : Set E} (hs : ∀ x, x ∈ K ↔ -x ∈ K)
    {p : E} (hp : p ∈ polar K) {x : E} (hx : x ∈ K) : |inner (𝕜 := ℝ) p x| ≤ 1 := by
  apply abs_le.mpr
  have hn := hp (-x) ((hs x).mp hx)
  rw [inner_neg_left, real_inner_comm] at hn
  exact ⟨by linarith, by rw [real_inner_comm]; exact hp x hx⟩

theorem norm_smul_normalized {x : E} (hx : x ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    ‖(r/‖x‖) • x‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr (norm_nonneg _)), div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]

theorem normalized_inner {x : E} (hx : x ≠ 0) (r : ℝ) :
    inner (𝕜 := ℝ) ((r/‖x‖) • x) x = r*‖x‖ := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

theorem norm_le_of_mem_polar {K : Set E} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (0 : E) r ⊆ K) {p : E} (hp : p ∈ polar K) : ‖p‖ ≤ r⁻¹ := by
  by_cases hp0 : p = 0
  · simp [hp0, hr.le]
  have hq : (r/‖p‖) • p ∈ K := hball (by simpa using (norm_smul_normalized hp0 hr.le).le)
  have hh := hp _ hq
  rw [normalized_inner hp0] at hh
  have hh' : ‖p‖ ≤ r⁻¹ * (1 : ℝ) := (le_inv_mul_iff₀ hr).mpr hh
  simpa only [mul_one] using hh'

theorem isCompact_polar [FiniteDimensional ℝ E] {K : Set E} (h0 : (0 : E) ∈ interior K) : IsCompact (polar K) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  have hr2 : 0 < r/2 := half_pos hr
  have hclosed : Metric.closedBall (0 : E) (r/2) ⊆ K := by
    intro x hx
    apply hball
    exact (Metric.mem_closedBall.mp hx).trans_lt (half_lt_self hr)
  apply (isCompact_closedBall (0 : E) ((r/2)⁻¹)).of_isClosed_subset (isClosed_polar K)
  intro p hp
  simpa using norm_le_of_mem_polar hr2 hclosed hp

theorem mem_polar_polar_iff [FiniteDimensional ℝ E] {K : Set E} (hK : Convex ℝ K) (hc : IsClosed K)
    (h0 : (0 : E) ∈ K) (x : E) : x ∈ polar (polar K) ↔ x ∈ K := by
  constructor
  · intro hx
    by_contra hn
    obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hK hc hn
    have hu : 0 < u := by simpa using hfu 0 h0
    let v : E := (InnerProductSpace.toDual ℝ E).symm f
    have hv (y : E) : inner (𝕜 := ℝ) y v = f y := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have hp : u⁻¹ • v ∈ polar K := by
      intro y hy
      rw [real_inner_smul_right, hv, ← div_eq_inv_mul]
      exact (div_le_one hu).mpr (hfu y hy).le
    have hh := hx _ hp
    rw [real_inner_smul_left, real_inner_comm, hv, ← div_eq_inv_mul] at hh
    exact (not_le_of_gt hux) ((div_le_one hu).mp hh)
  · intro hx p hp
    rw [real_inner_comm]
    exact hp x hx

theorem closedBall_subset_polar_of_norm_bound {K : Set E} {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ K, ‖x‖ ≤ B) : Metric.closedBall (0 : E) ((B+1)⁻¹) ⊆ polar K := by
  intro p hp x hx
  have hp' : ‖p‖ ≤ (B+1)⁻¹ := by simpa using hp
  have hi := real_inner_le_norm x p
  have hm := mul_le_mul (hbound x hx) hp' (norm_nonneg _) hB
  have hr : 0 < B+1 := by linarith
  have hb : B*(B+1)⁻¹ ≤ 1 := (div_le_one hr).mpr (by linarith)
  exact hi.trans (hm.trans hb)

end
end ConvexPolar

namespace ConvexPolar
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type u76} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {κ : Type u77}

theorem pairing_le_of_net {P : Set E} {b : κ → E} {δ M : ℝ}
    (hnet : ∀ p ∈ P, ∃ j, ‖p-b j‖ ≤ δ) {x : E}
    (hx : ∀ j, inner (𝕜 := ℝ) (b j) x ≤ M) {p : E} (hp : p ∈ P) :
    inner (𝕜 := ℝ) p x ≤ M+δ*‖x‖ := by
  obtain ⟨j, hj⟩ := hnet p hp
  have hh := real_inner_le_norm (p-b j) x
  rw [inner_sub_left] at hh
  have hm := mul_le_mul_of_nonneg_right hj (norm_nonneg x)
  linarith [hx j]

theorem net_norm_bound {P : Set E} {b : κ → E} {δ M r : ℝ}
    (hr : 0 ≤ r) (hM : 0 ≤ M) (hball : Metric.closedBall (0 : E) r ⊆ P)
    (hnet : ∀ p ∈ P, ∃ j, ‖p-b j‖ ≤ δ) {x : E}
    (hx : ∀ j, inner (𝕜 := ℝ) (b j) x ≤ M) : (r-δ)*‖x‖ ≤ M := by
  by_cases hx0 : x = 0
  · simpa [hx0] using hM
  have hp : (r/‖x‖) • x ∈ P := hball (by simpa using (norm_smul_normalized hx0 hr).le)
  have hh := pairing_le_of_net hnet hx hp
  rw [normalized_inner hx0] at hh
  nlinarith

theorem finite_polar_approximation [FiniteDimensional ℝ E] {K : Set E}
    (hc : IsCompact K) (hK : Convex ℝ K) (hi : (interior K).Nonempty)
    (hs : ∀ x, x ∈ K ↔ -x ∈ K) {α : ℝ} (hα : 0 < α) :
    ∃ t : Finset E,
      Function.Injective (fun x : E => fun j : t => inner (𝕜 := ℝ) (j : E) x) ∧
      K ⊆ stripBody (fun j : t => (j : E)) ∧
      (∀ x ∈ stripBody (fun j : t => (j : E)), (1+α)⁻¹ • x ∈ K) ∧
      polar (stripBody (fun j : t => (j : E))) ⊆ polar K := by
  classical
  have h0 := zero_mem_interior_of_symmetric hK hi hs
  obtain ⟨B, hB, hbound⟩ := hc.isBounded.exists_pos_norm_le
  let r := (B+1)⁻¹
  have hr : 0 < r := inv_pos.mpr (by linarith)
  let δ := α*r/(1+α)
  have hlam : 0 < 1+α := by linarith
  have hδ : 0 < δ := div_pos (mul_pos hα hr) hlam
  have hrδ : 0 < r-δ := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ hlam).mpr
    nlinarith
  have hδeq : δ = α*(r-δ) := by dsimp [δ]; field_simp; ring
  have hball : Metric.closedBall (0 : E) r ⊆ polar K :=
    closedBall_subset_polar_of_norm_bound hB.le hbound
  obtain ⟨t, htK, ht, hcover⟩ := (isCompact_polar h0).finite_cover_balls hδ
  let b : ht.toFinset → E := fun j => j
  have hb (j : ht.toFinset) : b j ∈ polar K := htK (by simpa only [b, Set.Finite.mem_toFinset] using j.2)
  have hnet (p : E) (hp : p ∈ polar K) : ∃ j : ht.toFinset, ‖p-b j‖ ≤ δ := by
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcover hp)
    obtain ⟨hqmem, hdist⟩ := mem_iUnion.mp hq
    refine ⟨⟨q, by simpa using hqmem⟩, ?_⟩
    simpa only [dist_eq_norm, b] using (Metric.mem_ball.mp hdist).le
  have hKK' : K ⊆ stripBody b := by
    intro x hx j
    exact polar_abs_pairing hs (hb j) hx
  have hspans : Function.Injective (fun x : E => fun j => inner (𝕜 := ℝ) (b j) x) := by
    intro x y hxy
    have hz (j) : inner (𝕜 := ℝ) (b j) (x-y) ≤ 0 := by
      rw [inner_sub_right]
      have hh : inner (𝕜 := ℝ) (b j) x = inner (𝕜 := ℝ) (b j) y := congrFun hxy j
      rw [hh, sub_self]
    have hh := net_norm_bound hr.le le_rfl hball hnet hz
    have he : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp he)
  refine ⟨ht.toFinset, hspans, hKK', ?_, polar_antitone hKK'⟩
  intro x hx
  apply (mem_polar_polar_iff hK hc.isClosed (interior_subset h0) _).mp
  have hx' (j) : inner (𝕜 := ℝ) (b j) x ≤ 1 := (le_abs_self _).trans (hx j)
  have hh := net_norm_bound hr.le (by norm_num : (0 : ℝ) ≤ 1) hball hnet hx'
  have hd : δ*‖x‖ ≤ α := by nlinarith
  intro p hp
  rw [real_inner_smul_right, ← div_eq_inv_mul]
  apply (div_le_one hlam).mpr
  have hh' := pairing_le_of_net hnet hx' hp
  linarith

end
end ConvexPolar

namespace SymmetricPolar
open Set Filter
open scoped Topology ContDiff Pointwise
noncomputable section
variable {n : ℕ}

end
end SymmetricPolar

end LowerBoundInline

end OAI
