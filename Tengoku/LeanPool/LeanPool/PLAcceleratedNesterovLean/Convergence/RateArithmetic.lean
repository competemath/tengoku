/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import Tengoku.LeanPool.LeanPool.PLAcceleratedNesterovLean.Core.Defs
import Tengoku.LeanPool.LeanPool.PLAcceleratedNesterovLean.Convergence.PhaseSchedule

/-!
# Multi-Phase Rate Arithmetic

Pure arithmetic lemmas for the multi-phase Nesterov convergence proof.
These establish that:
1. The product ∏(1 + C·4⁻ᵏ) converges (finite jump overhead)
2. The geometric contraction (1-r)ⁿ ≤ exp(-n·r)
3. The total rate deficit Σ Nₖ·deficitₖ is bounded (summable)

All lemmas are independent of the Lean formalization of the algorithm.
-/

@[expose] public section

noncomputable section

namespace PLAcceleratedNesterovLean

open Real Finset

/-! ## Exponential bounds for geometric contraction -/

/-- (1 - r)^n ≤ exp(-n·r) for 0 ≤ r ≤ 1.
@isnad1 id=le.2h2v.s6.7fd38989f022 from=translated src=- shape=e253d262 vocab=2b8c9761
-/
theorem one_sub_pow_le_exp_neg {r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    (1 - r) ^ n ≤ Real.exp (-(↑n * r)) := by
  have h1r : 0 ≤ 1 - r := by linarith
  calc (1 - r) ^ n
      ≤ (Real.exp (-r)) ^ n :=
        pow_le_pow_left₀ h1r (Real.one_sub_le_exp_neg r) n
    _ = Real.exp (↑n * (-r)) := (Real.exp_nat_mul (-r) n).symm
    _ = Real.exp (-(↑n * r)) := by ring_nf

/-! ## Product bounds for jump factors -/

/-! ## Rate deficit bounds -/

/-- 2^k · 4^{-k} = (1/2)^k
@isnad1 id=eq.0h1v.s6.432e295dd718 from=translated src=- shape=71b5ced9 vocab=3c915705
-/
theorem two_pow_mul_four_inv_pow (k : ℕ) :
    (2 : ℝ) ^ k * ((4 : ℝ)⁻¹ ^ k) = ((1 : ℝ) / 2) ^ k := by
  rw [show (4 : ℝ)⁻¹ = (1 : ℝ) / 4 from by norm_num, ← mul_pow]
  congr 1; norm_num

/-- Σ_{k=0}^{K-1} 2^k · 4^{-k} = Σ (1/2)^k ≤ 2.
@isnad1 id=le.0h1v.s6.911ce2cdd687 from=translated src=- shape=febfd610 vocab=ee37801b
-/
theorem rate_deficit_sum_le (K : ℕ) :
    ∑ k ∈ range K, (2 : ℝ) ^ k * ((4 : ℝ)⁻¹ ^ k) ≤ 2 := by
  simp_rw [two_pow_mul_four_inv_pow]
  -- ∑_{k=0}^{K-1} (1/2)^k = 1 + ∑_{k=0}^{K-2} (1/2)^{k+1} ≤ 1 + 1 = 2
  rcases K with _ | K
  · simp
  · rw [Finset.sum_range_succ']
    simp only [pow_zero]
    have : ∑ i ∈ range K, ((1 : ℝ) / 2) ^ (i + 1) ≤ 1 :=
      partial_geometric_half_le K
    linarith

/-- Σ_{k=0}^{K-1} 2^k · C · 4^{-k} ≤ 2·C for C ≥ 0.
@isnad1 id=le.1h2v.s6.f54b41776286 from=translated src=- shape=7c46c3b1 vocab=ee37801b
-/
theorem weighted_deficit_sum_le {C : ℝ} (hC : 0 ≤ C) (K : ℕ) :
    ∑ k ∈ range K, (2 : ℝ) ^ k * (C * (4 : ℝ)⁻¹ ^ k) ≤ 2 * C := by
  have hfact : ∀ k : ℕ, (2 : ℝ) ^ k * (C * (4 : ℝ)⁻¹ ^ k) =
      C * ((2 : ℝ) ^ k * (4 : ℝ)⁻¹ ^ k) := by intro k; ring
  simp_rw [hfact, ← Finset.mul_sum]
  calc C * ∑ k ∈ range K, (2 : ℝ) ^ k * (4 : ℝ)⁻¹ ^ k
      ≤ C * 2 := mul_le_mul_of_nonneg_left (rate_deficit_sum_le K) hC
    _ = 2 * C := by ring

/-! ## HasAcceleratedRate from geometric decay -/

/-- If f(xₖ) - f⋆ ≤ L₀ · rᵏ for r ∈ (0,1) where r ≤ exp(-1/√(L/μ)),
    then HasAcceleratedRate holds.
@isnad1 id=hasaccel.5h7v.s7.db73b8b7eacc from=translated src=- shape=9dec0967 vocab=0352441b
-/
theorem hasAcceleratedRate_of_geometric_decay
    (f : E d → ℝ) (iterates : ℕ → E d) (L μ L₀ r : ℝ)
    (hL₀ : 0 < L₀) (hr : 0 < r) (_hr1 : r < 1)
    (hrate : r ≤ Real.exp (-(1 / Real.sqrt (L / μ))))
    (hbound : ∀ k : ℕ, f (iterates k) - fStar f ≤ L₀ * r ^ k) :
    HasAcceleratedRate f iterates L μ := by
  refine ⟨L₀, hL₀, fun k => ?_⟩
  calc f (iterates k) - fStar f
      ≤ L₀ * r ^ k := hbound k
    _ ≤ L₀ * (Real.exp (-(1 / Real.sqrt (L / μ)))) ^ k := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hL₀)
        exact pow_le_pow_left₀ (le_of_lt hr) hrate k
    _ = L₀ * Real.exp (-(↑k / Real.sqrt (L / μ))) := by
        rw [← Real.exp_nat_mul]; congr 1; ring_nf

end PLAcceleratedNesterovLean
