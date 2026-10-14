/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.MorreyScaling
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial

/-! # Quantitative cutoff multiplication for Morrey sources

A bounded multiplier supported in a prescribed set only uses the Morrey norm
of the source restricted to that set. Lowering the integrability exponent
then supplies the differentiated heat-source norm, including after truncation
to nonpositive times.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Endgame

/-- A bounded supported multiplier is controlled by the indicated source
norm. No measurability assumption is needed for this upper-integral bound.
@isnad1 id=le.4h6v.s6.8ac5ff4fabad from=translated src=- shape=6c236259 vocab=d81a65ea
-/
theorem morrey_norm_mul_le_indicator (P τ C : ℝ) (hP : 0 < P) (hC : 0 ≤ C)
    (S : Set ParabolicPoint) (a f : ParabolicPoint → ℝ)
    (ha : ∀ z, |a z| ≤ C) (hsupp : ∀ z ∉ S, a z = 0) :
    morreyNorm P τ (fun z => a z * f z) ≤
      ENNReal.ofReal C * morreyNorm P τ (S.indicator f) := by
  have hmono : morreyNorm P τ (fun z => a z * f z) ≤
      morreyNorm P τ (fun z => C * S.indicator f z) := by
    apply morreyNorm_mono hP.le
    intro z
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz, abs_mul, abs_mul, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha z) (abs_nonneg _)
    · rw [hsupp z hz, indicator_of_notMem hz, zero_mul, mul_zero]
  exact hmono.trans (by
    simpa only [abs_of_nonneg hC] using morreyNorm_const_mul_le hP C (S.indicator f))

end CKN.Core.Endgame
