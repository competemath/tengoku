import Tengoku.OpenaiMath.OAI.Analysis.LiebThirring.InitialOrbit

namespace OAI

universe u116 u117 u118 u119 u120 u121 u122 u123 u124 u125 u126 u127 u128 u129 u130 u131 u132 u133 u134 u135

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
section
open Set Finset Filter
open Set Finset

end

section

/-! Analytic compactness and free-locus facts for the PL continuation proof. -/

open Set Finset
namespace SharpLiebThirring.PLParity

section Compactness
variable {E : Type u116} {V : Type u117} [TopologicalSpace E] [NormedAddCommGroup V]

/-- On a compact domain, sufficiently small values lie in any open neighborhood
of the zero set. This is not an existence assumption about zeros. -/
lemma small_norm_near_zeros {C U : Set E} (hC : IsCompact C) (hU : IsOpen U)
    (f : E → V) (hf : ContinuousOn f C) (hzero : ∀ x ∈ C, f x = 0 → x ∈ U) :
    ∃ ε > 0, ∀ x ∈ C, ‖f x‖ < ε → x ∈ U := by
  by_cases hn : (C \ U).Nonempty
  · obtain ⟨x, hx, hmin⟩ := (hC.diff hU).exists_isMinOn hn (hf.norm.mono sdiff_subset)
    have hp : 0 < ‖f x‖ := norm_pos_iff.mpr (fun h ↦ hx.2 (hzero x hx.1 h))
    refine ⟨‖f x‖, hp, ?_⟩
    intro y hy hfy
    by_contra hu
    exact (not_lt_of_ge (hmin ⟨hy, hu⟩)) hfy
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx _
    by_contra hu
    exact hn ⟨x, hx, hu⟩
end Compactness

section ConvexError
variable {ι : Type u118} {V : Type u119} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma norm_of_convex_zero (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (a : ι → V) (ha : ∑ i, w i • a i = 0) (z : V) (ε : ℝ)
    (he : ∀ i, ‖a i - z‖ ≤ ε) : ‖z‖ ≤ ε := by
  have hid : ∑ i, w i • (a i - z) = -z := by
    simp only [smul_sub, Finset.sum_sub_distrib, ha, ← Finset.sum_smul, hs, one_smul, zero_sub]
  calc
    ‖z‖ = ‖∑ i, w i • (a i - z)‖ := by rw [hid, norm_neg]
    _ ≤ ∑ i, ‖w i • (a i - z)‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i * ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left (he i) (hw i)
    _ = ε := by rw [← Finset.sum_mul, hs, one_mul]

lemma norm_of_approximate_convex_zero (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (a b : ι → V) (ha : ∑ i, w i • a i = 0)
    (z : V) (ε δ : ℝ) (he : ∀ i, dist (a i) (b i) ≤ ε)
    (hd : ∀ i, dist (b i) z ≤ δ) : ‖z‖ ≤ ε + δ := by
  apply norm_of_convex_zero w hw hs a ha z (ε + δ)
  intro i
  rw [← dist_eq_norm]
  exact (dist_triangle _ _ _).trans (add_le_add (he i) (hd i))
end ConvexError

section FreeLocus
variable {G : Type u120} {E : Type u121} [Group G] [MulAction G E]

def freeLocus : Set E := {x | ∀ g : G, g • x = x → g = 1}

lemma freeLocus_smul (g : G) {x : E} (hx : x ∈ freeLocus (G := G)) :
    g • x ∈ freeLocus (G := G) := by
  intro s hs
  have hfix : (g⁻¹ * s * g) • x = x := by
    rw [mul_smul, mul_smul, hs, inv_smul_smul]
  have he := hx _ hfix
  have hh := congrArg (fun a : G ↦ g * a * g⁻¹) he
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hh

def freeSubMulAction : SubMulAction G E where
  carrier := freeLocus (G := G)
  smul_mem' g _ hx := freeLocus_smul g hx

variable [TopologicalSpace E] [T2Space E] [ContinuousConstSMul G E] [Finite G]

lemma isOpen_freeLocus : IsOpen (freeLocus (G := G) (E := E)) := by
  classical
  have hset : freeLocus (G := G) (E := E) = ⋂ g : {g : G // g ≠ 1}, {x | g.val • x ≠ x} := by
    ext x
    simp only [freeLocus, mem_ofPred_eq, mem_iInter]
    constructor
    · intro h ⟨g, hg⟩ he
      exact hg (h g he)
    · intro h g hg
      by_contra hn
      exact h ⟨g, hn⟩ hg
  rw [hset]
  apply isOpen_iInter_of_finite
  intro g
  exact (isClosed_eq (continuous_const_smul g.val) continuous_id).isOpen_compl

end FreeLocus
section FreeTube
variable {G : Type u122} {E : Type u123} [Group G] [MulAction G E] [MetricSpace E]
  [ContinuousConstSMul G E] [Finite G]

lemma compact_free_tube {K : Set E}
    (hK : IsCompact K) (hfree : K ⊆ freeLocus (G := G)) :
    ∃ r > 0, Metric.cthickening r K ⊆ freeLocus (G := G) :=
  hK.exists_cthickening_subset_open isOpen_freeLocus hfree

end FreeTube
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

def Flag.combination {n : ℕ} (h : ℝ) (F : Flag n) (w : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  h • ∑ k, w k • F.point k

lemma Flag.combination_neighbor {n : ℕ} [NeZero n] (h : ℝ) (F : Flag n)
    (w : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (hj : w j = 0) :
    (F.neighbor j).combination h w = F.combination h w := by
  unfold combination
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = j
  · simp only [hk, hj, zero_smul]
  · have he : (F.neighbor j).point k = F.point k := by
      ext i
      simp only [point, congrFun (F.neighbor_vertex j k hk) i]
    rw [he]

lemma Flag.dist_combination_scaled_center {n : ℕ} (h : ℝ) (hh : 0 ≤ h) (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) :
    dist (F.combination h w) (h • F.center) ≤ h / 2 := by
  rw [combination, dist_scale h hh]
  nlinarith [F.dist_combination_center w hw hs]

lemma Flag.dist_combination_gridPoint {n : ℕ} (h : ℝ) (hh : 0 ≤ h) (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (k : Fin (n + 1)) :
    dist (F.combination h w) (gridPoint h (F.vertex k)) ≤ h := by
  rw [gridPoint_vertex, combination, dist_scale h hh]
  nlinarith [F.dist_combination_point w hw hs k]

lemma nearCylinder_combination_cthickening {n : ℕ} (K : Set (Fin n → ℝ)) (h r : ℝ)
    (hh : 0 ≤ h) (t : Fin n) (m : ℕ) {F : Flag n} (hF : F ∈ nearCylinder K h r t m)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) :
    F.combination h w ∈ Metric.cthickening (r + h / 2) K := by
  obtain ⟨x, hx, hd⟩ := hF.1
  apply Metric.mem_cthickening_of_dist_le _ x _ K hx
  calc
    _ ≤ dist (F.combination h w) (h • F.center) + dist (h • F.center) x := dist_triangle _ _ _
    _ ≤ h / 2 + r := add_le_add (F.dist_combination_scaled_center h hh w hw hs) hd.le
    _ = r + h / 2 := add_comm _ _

end SharpLiebThirring.CubeFlags
end

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

end SharpLiebThirring.CubeFlags

end
end
end

end OAI
