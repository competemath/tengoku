/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Analysis.Normed.Operator.Banach
import Tengoku.Seed.Analysis.Normed.Operator.Compact.Basic
import Tengoku.LanaOka.Oka.Topology.Algebra.Module.Schwartz.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Schwartz's finiteness theorem for Banach spaces

Let `E`, `F` be Banach spaces over a complete nontrivially normed field, `u : E →L[𝕜] F`
surjective and `v : E →L[𝕜] F` compact. Then the range of `u + v` is closed and of finite
codimension.

## Main results

* `IsCompactOperator.exists_range_add_sup_eq_top`: there is a finite dimensional `G ⊆ F` with
  `range (u + v) ⊔ G = ⊤`.
* `IsCompactOperator.finiteDimensional_quotient_range_add`: `F ⧸ range (u + v)` is finite
  dimensional.
* `IsCompactOperator.isClosed_range_add`: `range (u + v)` is closed.

## Proof

By the open mapping theorem there is `C` such that every `y` has a preimage of norm `≤ C ‖y‖`.
The image under `v` of the ball of radius `C` is relatively compact, hence covered by finitely
many balls `B(yⱼ, ‖c‖)` with `0 < ‖c‖ < 1`; let `G` be the span of the `yⱼ`. The iteration
`ContinuousLinearMap.range_add_sup_eq_top_of_step` with `K` the closed unit ball of `F` and `L`
the closed ball of radius `C` in `E` then gives `range (u + v) ⊔ G = ⊤`.
-/

open Filter Topology Metric

namespace IsCompactOperator

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Schwartz's theorem** (Banach spaces): for `u` surjective and `v` compact there is a finite
dimensional subspace `G` with `range (u + v) ⊔ G = ⊤`. -/
theorem exists_range_add_sup_eq_top [CompleteSpace 𝕜] {u v : E →L[𝕜] F}
    (hu : Function.Surjective u) (hv : IsCompactOperator v) :
    ∃ G : Submodule 𝕜 F, FiniteDimensional 𝕜 G ∧
      LinearMap.range (u + v).toLinearMap ⊔ G = ⊤ := by
  obtain ⟨C, hC0, hC⟩ := u.exists_preimage_norm_le hu
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one 𝕜
  obtain ⟨t, -, htf, ht⟩ := (hv.isCompact_closure_image_closedBall C).finite_cover_balls hc0
  let G := Submodule.span 𝕜 t
  haveI : FiniteDimensional 𝕜 G := FiniteDimensional.span_of_finite 𝕜 htf
  refine ⟨G, this, ?_⟩
  refine ContinuousLinearMap.range_add_sup_eq_top_of_step (K := closedBall 0 1)
    (L := closedBall 0 C) G.closed_of_finiteDimensional hc1
    (NormedSpace.isVonNBounded_closedBall _ _ _) ?_ ?_ hu ?_
  · intro ℓ hℓ
    refine ⟨_, (Summable.of_norm_bounded (g := fun n ↦ C * ‖c‖ ^ n)
      ((summable_geometric_of_lt_one (norm_nonneg _) hc1).mul_left C) fun n ↦ ?_).hasSum⟩
    rw [norm_smul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (by simpa using hℓ n) (by positivity)
  · intro k hk
    obtain ⟨x, hxk, hx⟩ := hC k
    have hk1 : ‖k‖ ≤ 1 := by simpa using hk
    have hxC : x ∈ closedBall 0 C := by
      simpa using hx.trans (by simpa using mul_le_mul_of_nonneg_left hk1 hC0.le)
    have hvx : v x ∈ closure (v '' closedBall 0 C) := subset_closure ⟨x, hxC, rfl⟩
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.1 (ht hvx)
    refine ⟨x, hxC, c⁻¹ • (y - v x), ?_, hxk, ?_⟩
    · have hc : c ≠ 0 := norm_pos_iff.1 hc0
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, ← div_eq_inv_mul, div_le_one hc0,
        ← dist_eq_norm']
      exact (mem_ball.1 hy).le
    · have hc : c ≠ 0 := norm_pos_iff.1 hc0
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
      exact Submodule.subset_span hyt
  · intro x
    obtain ⟨s, hs⟩ := NormedField.exists_lt_norm 𝕜 ‖v x‖
    have hs0 : s ≠ 0 := norm_pos_iff.1 ((norm_nonneg _).trans_lt hs)
    refine ⟨s, s⁻¹ • v x, ?_, by rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]⟩
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, ← div_eq_inv_mul,
      div_le_one (norm_pos_iff.2 hs0)]
    exact hs.le

/-- **Schwartz's theorem** (Banach spaces): for `u` surjective and `v` compact, the cokernel
`F ⧸ range (u + v)` is finite dimensional. -/
theorem finiteDimensional_quotient_range_add [CompleteSpace 𝕜] {u v : E →L[𝕜] F}
    (hu : Function.Surjective u) (hv : IsCompactOperator v) :
    FiniteDimensional 𝕜 (F ⧸ LinearMap.range (u + v).toLinearMap) := by
  obtain ⟨G, hG, h⟩ := hv.exists_range_add_sup_eq_top hu
  exact Submodule.finiteDimensional_quotient_of_sup_eq_top h

/-- **Schwartz's theorem** (Banach spaces): for `u` surjective and `v` compact, the range of
`u + v` is closed. -/
theorem isClosed_range_add [CompleteSpace 𝕜] {u v : E →L[𝕜] F}
    (hu : Function.Surjective u) (hv : IsCompactOperator v) :
    IsClosed (LinearMap.range (u + v).toLinearMap : Set F) := by
  obtain ⟨G, hG, h⟩ := hv.exists_range_add_sup_eq_top hu
  haveI : CompleteSpace G := FiniteDimensional.complete 𝕜 G
  refine ContinuousLinearMap.isClosed_range_of_isOpenMap_coprod h
    (ContinuousLinearMap.isOpenMap _ fun y ↦ ?_)
  obtain ⟨r, ⟨x, rfl⟩, g, hg, rfl⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top : y ∈ _)
  exact ⟨(x, ⟨g, hg⟩), rfl⟩

end IsCompactOperator
