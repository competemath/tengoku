/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpConvolution
public import Tengoku
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.SupportThickening

/-!
# Global and local `Lᵖ` approximation by mollification

The three results below separate translation continuity, the normalized-kernel
estimate, and the compact-localization step used for interior convergence.
-/

@[expose] public section

open Function Set Filter MeasureTheory Topology
open scoped ENNReal Convolution Pointwise

namespace CKN

noncomputable section

theorem mollify_eq_on_compact_of_eq_on_thickening
    {d : ℕ} {K : Set (Vec d)} {u g : Vec d → ℝ} {ε₀ ε : ℝ}
    (hε : 0 < ε) (hεlt : ε ≤ ε₀)
    (h_eq : ∀ y ∈ K + Metric.closedBall 0 ε₀, u y = g y) {x : Vec d} (hx : x ∈ K) :
    mollify u ε hε x = mollify g ε hε x := by
  rw [mollify, mollify]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Metric.closedBall 0 ε
  · have hty : x - t ∈ K + Metric.closedBall 0 ε₀ := by
      refine ⟨x, hx, -t, ?_, by abel_nf⟩
      have ht' : ‖t‖ ≤ ε := by
        simpa [Metric.mem_closedBall, dist_zero_right, dist_eq_norm] using ht
      simpa [norm_neg] using le_trans ht' hεlt
    rw [h_eq (x - t) hty]
  · have hzero : mollifier (d := d) ε hε t = 0 := by
      apply notMem_support.mp
      intro ht_support
      exact ht (CKN.mollifier_tsupp_eq_closedBall hε ▸ subset_tsupport _ ht_support)
    simp [hzero]

end

end CKN
