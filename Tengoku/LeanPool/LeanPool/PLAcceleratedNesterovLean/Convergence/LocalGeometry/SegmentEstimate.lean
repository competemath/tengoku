/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import Tengoku.LeanPool.LeanPool.PLAcceleratedNesterovLean.Core.NesterovScheme
import Tengoku.LeanPool.LeanPool.PLAcceleratedNesterovLean.Convergence.LocalGeometry.Step2
public import Tengoku

/-!
# Segment Estimate Helpers

Helper lemmas for the segment estimate used by `motion_bounds_curvature_error`.
Provides a generalized strong aiming lemma (no φ'(0) = 0 requirement)
and the fiber-path Hessian-to-second-derivative connection.
-/

@[expose] public section

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal

/-! ## Generalized segment estimate -/

/-- General segment estimate: if φ is C² and φ''(t) ≥ c for t ∈ [0,1],
then φ'(1) ≥ (φ(1) - φ(0)) + c/2.

Applies to C² functions with arbitrary φ'(0).
The proof uses ψ(t) = t·φ'(t) - φ(t) + φ(0) - (c/2)t², which satisfies
ψ(0) = 0 regardless of φ'(0) (since 0·φ'(0) = 0), and ψ'(t) = t·(φ''(t) - c) ≥ 0.
@isnad1 id=le.5h2v.s8.dbf7a59ddad7 from=translated src=- shape=fdfd74ff vocab=19269c34
-/
theorem segment_estimate_from_hessian (φ : ℝ → ℝ) (c : ℝ)
    (hφ_cont : ContinuousOn φ (Set.Icc 0 1))
    (hφ_diff : DifferentiableOn ℝ φ (Set.Ioo 0 1))
    (hφ'_cont : ContinuousOn (deriv φ) (Set.Icc 0 1))
    (hφ'_diff : DifferentiableOn ℝ (deriv φ) (Set.Ioo 0 1))
    (hφ''_lower : ∀ t, 0 ≤ t → t ≤ 1 →
      deriv (deriv φ) t ≥ c) :
    deriv φ 1 ≥ (φ 1 - φ 0) + c / 2 := by
  -- Define ψ(t) = t * φ'(t) - φ(t) + φ(0) - c/2 * t²
  set ψ : ℝ → ℝ := fun t => t * deriv φ t - φ t + φ 0 - c / 2 * t ^ 2
  -- Key: ψ(0) = 0 without needing φ'(0) = 0 (since 0 * φ'(0) = 0)
  have hψ0 : ψ 0 = 0 := by
    change 0 * deriv φ 0 - φ 0 + φ 0 - c / 2 * 0 ^ 2 = 0
    ring
  have hψ_cont : ContinuousOn ψ (Set.Icc 0 1) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.add
      · apply ContinuousOn.sub
        · exact continuous_id.continuousOn.mul hφ'_cont
        · exact hφ_cont
      · exact continuous_const.continuousOn
    · exact (continuous_const.mul continuous_sq).continuousOn
  have hψ_diff : DifferentiableOn ℝ ψ (interior (Set.Icc 0 1)) := by
    rw [interior_Icc]
    apply DifferentiableOn.sub
    · apply DifferentiableOn.add
      · apply DifferentiableOn.sub
        · exact differentiableOn_id.mul hφ'_diff
        · exact hφ_diff
      · exact differentiableOn_const _
    · exact ((differentiable_const (c/2)).mul differentiable_sq).differentiableOn.mono
        Set.Ioo_subset_Icc_self
  have hψ'_nonneg : ∀ x ∈ interior (Set.Icc (0:ℝ) 1), 0 ≤ deriv ψ x := by
    intro x hx
    rw [interior_Icc] at hx
    -- ψ'(x) = x * (φ''(x) - c)
    have hda_prod : HasDerivAt (fun t => t * deriv φ t)
      (1 * deriv φ x + x * deriv (deriv φ) x) x :=
      (hasDerivAt_id x).mul (hφ'_diff.differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
    have hda_φ : HasDerivAt φ (deriv φ x) x :=
      (hφ_diff.differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
    have hda_const : HasDerivAt (fun _ => φ 0) 0 x := hasDerivAt_const x (φ 0)
    have hda : HasDerivAt ψ
      ((1 * deriv φ x + x * deriv (deriv φ) x) - deriv φ x + 0 - c * x) x :=
      ((hda_prod.sub hda_φ).add hda_const).sub (hasDerivAt_quad c x)
    rw [hda.deriv]
    have : (1 * deriv φ x + x * deriv (deriv φ) x) - deriv φ x + 0 - c * x =
           x * (deriv (deriv φ) x - c) := by ring
    rw [this]
    exact mul_nonneg (le_of_lt hx.1)
      (sub_nonneg.mpr (hφ''_lower x (le_of_lt hx.1) (le_of_lt hx.2)))
  have hψ_mono : MonotoneOn ψ (Set.Icc 0 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hψ_cont hψ_diff hψ'_nonneg
  have h := hψ_mono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  simp only [ψ] at h
  linarith [hψ0]

/-! ## Fiber path second derivative = Hessian quadratic form -/

/-- The fiber path φ(t) = f(m + t·v) is C² when f is C² on an open set
containing the entire line through m in direction v.
@isnad1 id=contdiff.3h5v.s8.7f476e3ad81d from=translated src=- shape=e13d3438 vocab=0499e81e
-/
theorem fiber_path_contDiff2 {d : ℕ} (f : E d → ℝ) (m v : E d)
    {V : Set (E d)} (hV : IsOpen V) (hf_C2 : ContDiffOn ℝ 2 f V)
    (hseg : ∀ t : ℝ, m + t • v ∈ V) :
    ContDiff ℝ 2 (fun t : ℝ => f (m + t • v)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hψ : ContDiff ℝ 2 (fun s : ℝ => m + s • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  exact (hf_C2.contDiffAt (hV.mem_nhds (hseg t))).comp t hψ.contDiffAt

/-- The fiber path φ(t) = f(m + t·v) is C² at every point t ∈ [0,1] when f is C²
on an open set containing the segment {m + t·v | t ∈ [0,1]}.
@isnad1 id=contdiff.4h6v.s8.68a4464f9b4c from=translated src=- shape=18ee83b6 vocab=79d09bac
-/
theorem fiber_path_C2at_on_segment {d : ℕ} (f : E d → ℝ) (m v : E d)
    {V : Set (E d)} (hV : IsOpen V) (hf_C2 : ContDiffOn ℝ 2 f V)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc 0 1 → m + t • v ∈ V) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ 2 (fun t : ℝ => f (m + t • v)) t := by
  intro t ht
  have hψ : ContDiff ℝ 2 (fun s : ℝ => m + s • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  exact (hf_C2.contDiffAt (hV.mem_nhds (hseg t ht))).comp t hψ.contDiffAt

end PLAcceleratedNesterovLean
