/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.Definitions
import Tengoku.Seed.Analysis.Calculus.BumpFunction.Normed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The normalized wave packet used in the negative endpoint construction

Section 3 fixes an even, nonnegative, smooth function supported in
`[-1/4, 1/4]` and having integral one. Mathlib's normalized smooth bump
provides this function directly.
-/

open Function MeasureTheory Metric Set
open scoped ContDiff

namespace QuadraticCarleson

/-- The underlying smooth bump, with inner radius `1/8` and outer radius
`1/4`.-/
noncomputable def baseBumpData : ContDiffBump (0 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The fixed normalized bump `φ` from the beginning of Section 3.-/
noncomputable def baseBump : ℝ → ℝ :=
  baseBumpData.normed volume

/--
@isnad1 id=le.0h1v.s3.509189822aad from=translated src=- shape=8a62b088 vocab=51ba4984
-/
theorem baseBump_nonneg (x : ℝ) : 0 ≤ baseBump x := by
  exact baseBumpData.nonneg_normed x

/--
@isnad1 id=even.0h0v.s2.3d3ce02295bf from=translated src=- shape=e3d48bcb vocab=134f52e7
-/
theorem baseBump_even : Function.Even baseBump := by
  intro x
  exact baseBumpData.normed_neg x

/--
@isnad1 id=contdiff.0h0v.s5.d3f0166e8832 from=translated src=- shape=3cea26be vocab=29e6c736
-/
theorem baseBump_smooth : ContDiff ℝ ∞ baseBump := by
  exact baseBumpData.contDiff_normed (μ := volume) (n := (⊤ : ℕ∞))

/--
@isnad1 id=eq.0h0v.s5.e1ec05a7a054 from=translated src=- shape=f0e61117 vocab=a3df1ce3
-/
theorem baseBump_integral : ∫ x : ℝ, baseBump x = 1 := by
  exact baseBumpData.integral_normed

/--
@isnad1 id=hascompa.0h0v.s3.4fa671d14ea1 from=translated src=- shape=e3d48bcb vocab=b73d7e39
-/
theorem baseBump_hasCompactSupport : HasCompactSupport baseBump := by
  exact baseBumpData.hasCompactSupport_normed

/--
@isnad1 id=ex.0h0v.s4.395776cb263d from=translated src=- shape=817e9a37 vocab=92ddcb8e
-/
theorem exists_baseBump_bound : ∃ C : ℝ, 0 < C ∧ ∀ x, baseBump x ≤ C := by
  obtain ⟨C, hC⟩ := baseBump_smooth.continuous.bounded_above_of_compact_support
    baseBump_hasCompactSupport
  refine ⟨max C 1, lt_max_of_lt_right zero_lt_one, fun x => ?_⟩
  exact (le_trans (le_abs_self (baseBump x)) (hC x)).trans (le_max_left C 1)

/--
@isnad1 id=le.0h0v.s5.9711f4975c19 from=translated src=- shape=8a2e394f vocab=706bed86
-/
theorem baseBump_support :
    Function.support baseBump ⊆ Icc (-1 / 4 : ℝ) (1 / 4 : ℝ) := by
  rw [baseBump, baseBumpData.support_normed_eq]
  intro x hx
  rw [mem_ball, Real.dist_eq] at hx
  have hx' : |x| < (1 / 4 : ℝ) := by
    simpa [baseBumpData] using hx
  constructor <;> linarith [abs_lt.mp hx']

/-- The rescaled packet `φ_(s,t)(x) = t⁻¹ φ((x-s)/t)` used in Section 3.-/
noncomputable def wavePacket (s t x : ℝ) : ℝ :=
  t⁻¹ * baseBump ((x - s) / t)

/--
@isnad1 id=continuo.0h2v.s4.1cf5e7dc8409 from=translated src=- shape=443e0365 vocab=0c22bc40
-/
theorem continuous_wavePacket (s t : ℝ) : Continuous (wavePacket s t) := by
  exact continuous_const.mul <|
    baseBump_smooth.continuous.comp ((continuous_id.sub continuous_const).div_const t)

/--
@isnad1 id=le.1h3v.s4.2ec2f874abeb from=translated src=- shape=f5f27b65 vocab=d4f6493a
-/
theorem wavePacket_nonneg (s x : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ wavePacket s t x := by
  exact mul_nonneg (inv_nonneg.mpr ht.le) (baseBump_nonneg _)

/--
@isnad1 id=le.2h4v.s5.240567dc7e22 from=translated src=- shape=a95c90ba vocab=7327f709
-/
theorem wavePacket_le_of_baseBump_bound {C : ℝ}
    (hC : ∀ x, baseBump x ≤ C) (s x : ℝ) {t : ℝ} (ht : 0 < t) :
    wavePacket s t x ≤ t⁻¹ * C := by
  exact mul_le_mul_of_nonneg_left (hC _) (inv_nonneg.mpr ht.le)

/--
@isnad1 id=eq.1h2v.s5.5419ec5ef673 from=translated src=- shape=855333e4 vocab=05507739
-/
theorem wavePacket_integral (s : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, wavePacket s t x = 1 := by
  simp_rw [wavePacket]
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self (fun x : ℝ => baseBump (x / t)) s]
  rw [Measure.integral_comp_div, baseBump_integral, abs_of_pos ht]
  simp [ht.ne']

/--
@isnad1 id=le.1h2v.s6.4e58ec0f257c from=translated src=- shape=c925bac8 vocab=d20344e2
-/
theorem wavePacket_support {s t : ℝ} (ht : 0 < t) :
    Function.support (wavePacket s t) ⊆
      Icc (s - t / 4) (s + t / 4) := by
  intro x hx
  have hbase : baseBump ((x - s) / t) ≠ 0 := by
    intro hzero
    apply hx
    simp [wavePacket, hzero]
  have hmem := baseBump_support hbase
  constructor
  · have hscaled := (le_div_iff₀ ht).mp hmem.1
    linarith
  · have hscaled := (div_le_iff₀ ht).mp hmem.2
    linarith

/--
@isnad1 id=hascompa.1h2v.s4.70611a9534af from=translated src=- shape=a3c7cfeb vocab=70fd476c
-/
theorem wavePacket_hasCompactSupport (s : ℝ) {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (wavePacket s t) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact wavePacket_support ht

/--
@isnad1 id=integrab.1h2v.s5.d6f8f90f2070 from=translated src=- shape=09749f8b vocab=9e6bd302
-/
theorem wavePacket_integrable (s : ℝ) {t : ℝ} (ht : 0 < t) :
    Integrable (wavePacket s t) :=
  (continuous_wavePacket s t).integrable_of_hasCompactSupport
    (wavePacket_hasCompactSupport s ht)

/--
@isnad1 id=le.1h2v.s6.4d1945239168 from=translated src=- shape=9961bfcf vocab=61c68d51
-/
theorem wavePacket_firstMoment_le (s : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, wavePacket s t x * |x - s| ≤ t / 4 := by
  have hmomentContinuous : Continuous (fun x : ℝ => wavePacket s t x * |x - s|) :=
    (continuous_wavePacket s t).mul ((continuous_id.sub continuous_const).abs)
  have hmomentCompact : HasCompactSupport (fun x : ℝ => wavePacket s t x * |x - s|) := by
    change HasCompactSupport (wavePacket s t * fun x : ℝ => |x - s|)
    exact (wavePacket_hasCompactSupport s ht).mul_right
  have hmomentIntegrable : Integrable (fun x : ℝ => wavePacket s t x * |x - s|) :=
    hmomentContinuous.integrable_of_hasCompactSupport hmomentCompact
  have hmajorantIntegrable : Integrable (fun x : ℝ => wavePacket s t x * (t / 4)) :=
    (wavePacket_integrable s ht).mul_const (t / 4)
  calc
    ∫ x : ℝ, wavePacket s t x * |x - s| ≤
        ∫ x : ℝ, wavePacket s t x * (t / 4) := by
      apply integral_mono hmomentIntegrable hmajorantIntegrable
      intro x
      by_cases hx : wavePacket s t x = 0
      · simp [hx]
      · have hsupp := wavePacket_support ht hx
        have habs : |x - s| ≤ t / 4 := by
          rw [abs_le]
          constructor <;> linarith [hsupp.1, hsupp.2]
        exact mul_le_mul_of_nonneg_left habs (wavePacket_nonneg s x ht)
    _ = t / 4 := by
      rw [integral_mul_const, wavePacket_integral s ht, one_mul]

end QuadraticCarleson
