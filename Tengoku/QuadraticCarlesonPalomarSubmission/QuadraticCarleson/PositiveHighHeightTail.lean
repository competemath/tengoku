/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.PositiveHighHeightEstimate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The paper's strict high-height tail

The height parametrization `B + n + 1` is exactly `r > B`. The maximal tail
is bounded by a measurable sum of the actual fixed-height maximal functions,
whose L² norms form a geometric series with ratio `2^(-1/10)`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveHighHeightEstimate

/--
@isnad1 id=iff.0h2v.s5.38c43b27ec3d from=translated src=- shape=4539bffd vocab=13a96747
-/
theorem highHeight_iff_exists (B r : ℕ) : B < r ↔ ∃ n : ℕ, r = B + n + 1 := by
  constructor
  · intro h
    exact ⟨r - B - 1, by omega⟩
  · rintro ⟨n, rfl⟩
    omega

/--
@isnad1 id=eq.1h3v.s6.0a43c115458b from=translated src=- shape=e16a24d0 vocab=59e99064
-/
theorem highHeight_oscillatoryScaleIndex_eq (lam : ℝ) (hlam : lam ≠ 0) (B n : ℕ) :
    oscillatoryScaleIndex lam (B + n + 1) hlam =
      oscillatoryScaleIndex lam 0 hlam + (B : ℤ) + (n : ℤ) + 1 := by
  rw [oscillatoryScaleIndex_eq_add]
  push_cast
  ring

/-- Countable Minkowski in L² for measurable extended nonnegative functions.
No summability assumption is needed: an infinite right side remains valid.
@isnad1 id=le.1h2v.s6.c802168cfaf1 from=translated src=- shape=e7535c7e vocab=705abd1c
-/
theorem eLpNorm_tsum_two_le {ι : Type*} [Countable ι]
    (F : ι → ℝ → ℝ≥0∞) (hF : ∀ i, Measurable (F i)) :
    eLpNorm (fun x ↦ ∑' i, F i x) 2 ≤ ∑' i, eLpNorm (F i) 2 := by
  classical
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  rw [ENNReal.rpow_two, ENNReal.rpow_two, eLpNorm_two_sq_lintegral]
  simp only [enorm_eq_self]
  simp_rw [ENNReal.tsum_eq_iSup_sum, ENNReal.iSup_pow]
  rw [lintegral_iSup_directed_of_measurable]
  · apply iSup_le
    intro s
    apply le_iSup_of_le s
    have hs := eLpNorm_sum_le (μ := volume) (s := s) (f := F)
      (fun i _ ↦ (hF i).aestronglyMeasurable) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hp := pow_le_pow_left₀ bot_le hs 2
    rw [eLpNorm_two_sq_lintegral] at hp
    simpa only [Finset.sum_apply, enorm_eq_self] using hp
  · intro s
    exact (Finset.measurable_fun_sum s (fun i _ ↦ hF i)).pow_const 2
  · intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · intro x
      exact pow_le_pow_left₀ bot_le
        (Finset.sum_le_sum_of_subset (f := fun i ↦ F i x) Finset.subset_union_left) 2
    · intro x
      exact pow_le_pow_left₀ bot_le
        (Finset.sum_le_sum_of_subset (f := fun i ↦ F i x) Finset.subset_union_right) 2

noncomputable def highHeightDecayRatio : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (-(1 : ℝ) / 10))

/--
@isnad1 id=lt.0h0v.s3.3394e0f4d090 from=translated src=- shape=ffdda526 vocab=6a453b8b
-/
theorem highHeightDecayRatio_lt_one : highHeightDecayRatio < 1 := by
  rw [highHeightDecayRatio, ENNReal.ofReal_lt_one]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

noncomputable def highHeightTailConstant : ℝ≥0∞ :=
  ENNReal.ofReal fixedHeightL2DecayConstant * highHeightDecayRatio *
    (1 - highHeightDecayRatio)⁻¹

/--
@isnad1 id=lt.0h0v.s3.47bd60af5d31 from=translated src=- shape=f463f024 vocab=187cbb9f
-/
theorem highHeightTailConstant_lt_top : highHeightTailConstant < ∞ := by
  unfold highHeightTailConstant
  apply ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (by finiteness) (highHeightDecayRatio_lt_one.trans (by simp)))
  exact ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr highHeightDecayRatio_lt_one)

/--
@isnad1 id=eq.0h2v.s7.1a46f63ce5bf from=translated src=- shape=ca6cfb1f vocab=5edc12eb
-/
theorem fixedHeightDecay_highHeight_factor (B n : ℕ) :
    ENNReal.ofReal (fixedHeightL2DecayConstant * (2 : ℝ) ^ (-((B + n + 1 : ℕ) : ℝ) / 10)) =
      ENNReal.ofReal fixedHeightL2DecayConstant *
        ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 10)) * highHeightDecayRatio ^ (n + 1) := by
  have hp : (2 : ℝ) ^ (-((B + n + 1 : ℕ) : ℝ) / 10) =
      (2 : ℝ) ^ (-(B : ℝ) / 10) * ((2 : ℝ) ^ (-(1 : ℝ) / 10)) ^ (n + 1) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  rw [hp, ENNReal.ofReal_mul fixedHeightL2DecayConstant_pos.le,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
  simp only [highHeightDecayRatio, mul_assoc]

/--
@isnad1 id=eq.0h1v.s7.01758721bbdb from=translated src=- shape=46cca3ab vocab=98702f5d
-/
theorem tsum_fixedHeightDecay_highHeight (B : ℕ) :
    (∑' n : ℕ, ENNReal.ofReal (fixedHeightL2DecayConstant *
      (2 : ℝ) ^ (-((B + n + 1 : ℕ) : ℝ) / 10))) =
      highHeightTailConstant * ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 10)) := by
  simp_rw [fixedHeightDecay_highHeight_factor]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
  unfold highHeightTailConstant
  ring

noncomputable def highHeightMajorant (B : ℕ) (b : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, paperFixedHeightQuadraticMaximal (B + n + 1) b x

/--
@isnad1 id=measurab.1h2v.s6.d788eee87fa0 from=translated src=- shape=3f6cf7fe vocab=8988a8b9
-/
theorem measurable_highHeightMajorant (B : ℕ) {b : ℝ → ℂ} (hb : MemLp b 2) :
    Measurable (highHeightMajorant B b) :=
  Measurable.tsum (fun _ ↦ measurable_paperFixedHeightQuadraticMaximal _ hb)

set_option maxHeartbeats 800000 in
-- Elaborating the countable Minkowski specialization unfolds the concrete
-- real-modulation supremum and its height-dependent kernel several times.
/--
@isnad1 id=le.1h2v.s7.2a22d86a6ee7 from=translated src=- shape=000aaf53 vocab=8ab73987
-/
theorem highHeightMajorant_eLpNorm_le (B : ℕ) {b : ℝ → ℂ} (hb : MemLp b 2) :
    eLpNorm (highHeightMajorant B b) 2 ≤ highHeightTailConstant *
      ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 10)) * eLpNorm b 2 := by
  have hp (n : ℕ) : eLpNorm (paperFixedHeightQuadraticMaximal (B + n + 1) b) 2 ≤
      ENNReal.ofReal (fixedHeightL2DecayConstant *
        (2 : ℝ) ^ (-((B + n + 1 : ℕ) : ℝ) / 10)) * eLpNorm b 2 :=
    paperFixedHeightQuadraticMaximal_eLpNorm_decay (B + n + 1) hb
  have hs := ENNReal.tsum_le_tsum hp
  rw [ENNReal.tsum_mul_right, tsum_fixedHeightDecay_highHeight] at hs
  exact (eLpNorm_tsum_two_le
    (fun n : ℕ ↦ paperFixedHeightQuadraticMaximal (B + n + 1) b)
    (fun n ↦ measurable_paperFixedHeightQuadraticMaximal (B + n + 1) hb)).trans hs

/-- The actual maximal complex tail, not the sum of the separate maximal
operators. Its heights are exactly the strict high range.-/
noncomputable def paperHighHeightTail (B : ℕ) (b : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ lam : {lam : ℝ // lam ≠ 0}, ‖∑' n : ℕ,
    ∫ t, b (x - t) *
      (dyadicPsi (oscillatoryScaleIndex lam.val (B + n + 1) lam.property) t : ℂ) *
        phase (lam.val * t ^ 2)‖ₑ

/--
@isnad1 id=le.0h3v.s4.5c12ca43a737 from=translated src=- shape=64964b48 vocab=de10542a
-/
theorem paperHighHeightTail_le_majorant (B : ℕ) (b : ℝ → ℂ) (x : ℝ) :
    paperHighHeightTail B b x ≤ highHeightMajorant B b x := by
  apply iSup_le
  intro lam
  apply enorm_tsum_le_tsum_enorm.trans
  apply ENNReal.tsum_le_tsum
  intro n
  exact le_iSup (fun μ : {μ : ℝ // μ ≠ 0} ↦ ‖∫ t, b (x - t) *
    (dyadicPsi (oscillatoryScaleIndex μ.val (B + n + 1) μ.property) t : ℂ) *
      phase (μ.val * t ^ 2)‖ₑ) lam

/--
@isnad1 id=le.1h2v.s7.48a4bedbf5f1 from=translated src=- shape=000aaf53 vocab=61ff70fa
-/
theorem paperHighHeightTail_eLpNorm_le (B : ℕ) {b : ℝ → ℂ} (hb : MemLp b 2) :
    eLpNorm (paperHighHeightTail B b) 2 ≤ highHeightTailConstant *
      ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 10)) * eLpNorm b 2 := by
  apply (eLpNorm_mono_enorm (f := paperHighHeightTail B b) (g := highHeightMajorant B b)
    (fun x ↦ by simpa only [enorm_eq_self] using paperHighHeightTail_le_majorant B b x)).trans
  exact highHeightMajorant_eLpNorm_le B hb

end PositiveHighHeightEstimate
end QuadraticCarleson
