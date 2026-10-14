/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.SingletonNull

/-!
# Parabolic Riesz kernels

The definitions in this module use the parabolic gauge appearing in the
potential estimates and expose the dyadic shell geometry used by later
integral estimates.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The parabolic gauge used by the order-`β` Riesz kernel. -/
def parabolicRho₂ (z w : ParabolicPoint) : ℝ :=
  Real.sqrt |z.2 - w.2| + vec3EuclideanNorm (z.1 - w.1)

/-- The order-`β` parabolic Riesz kernel as an extended nonnegative function. -/
def parabolicRieszKernel (β : ℝ) (z w : ParabolicPoint) : ℝ≥0∞ :=
  (ENNReal.ofReal (parabolicRho₂ z w)) ^ (-(5 - β))

/-- The nonnegative parabolic Riesz potential. -/
def parabolicRieszPotential (β : ℝ) (f : ParabolicPoint → ℝ)
    (z : ParabolicPoint) : ℝ≥0∞ :=
  ∫⁻ w, parabolicRieszKernel β z w * ENNReal.ofReal |f w|

/-- The shell with inner radius `2^k R` and outer radius `2^(k+1) R`. -/
def parabolicRieszShell (R : ℝ) (k : ℤ) (z : ParabolicPoint) : Set ParabolicPoint :=
  {w | (2 : ℝ) ^ (k : ℝ) * R ≤ parabolicRho₂ z w ∧
    parabolicRho₂ z w < (2 : ℝ) ^ ((k : ℝ) + 1) * R}

/--
@isnad1 id=measurab.0h1v.s3.8d30a1e36ef4 from=translated src=- shape=4827ab61 vocab=99bc61ee
-/
theorem measurable_parabolicRho₂ (z : ParabolicPoint) :
    Measurable (fun w : ParabolicPoint => parabolicRho₂ z w) := by
  have hnorm : Measurable (fun v : Vec3 => vec3EuclideanNorm v) := by
    rw [show (fun v : Vec3 => vec3EuclideanNorm v) =
        fun v => ‖WithLp.toLp 2 v‖ by
          funext v
          exact vec3EuclideanNorm_eq_l2 _]
    exact (continuous_norm.comp (PiLp.continuous_toLp 2 _)).measurable
  have hspace : Measurable (fun w : ParabolicPoint => z.1 - w.1) := by
    exact measurable_const.sub measurable_fst
  have htime : Measurable (fun w : ParabolicPoint => z.2 - w.2) := by
    exact measurable_const.sub measurable_snd
  have habs : Measurable (fun x : ℝ => |x|) := continuous_abs.measurable
  have hsqrt : Measurable (fun x : ℝ => Real.sqrt |x|) :=
    Real.continuous_sqrt.measurable.comp habs
  unfold parabolicRho₂
  have hsum := (hnorm.comp hspace).add (hsqrt.comp htime)
  change Measurable (fun w : ParabolicPoint =>
    vec3EuclideanNorm (z.1 - w.1) + Real.sqrt |z.2 - w.2|) at hsum
  have hsum' : Measurable (fun w : ParabolicPoint =>
      vec3EuclideanNorm (z.1 - w.1) + Real.sqrt |z.2 - w.2|) := hsum
  simpa only [add_comm] using hsum'

/--
@isnad1 id=measurab.0h3v.s3.fc44b81017d6 from=translated src=- shape=29d48da2 vocab=1c8ae570
-/
theorem measurableSet_parabolicRieszShell (R : ℝ) (k : ℤ) (z : ParabolicPoint) :
    MeasurableSet (parabolicRieszShell R k z) := by
  have hρ := measurable_parabolicRho₂ z
  unfold parabolicRieszShell
  exact (hρ measurableSet_Ici).inter (hρ measurableSet_Iio)

/--
@isnad1 id=le.0h2v.s4.a2906a4d7332 from=translated src=- shape=5ffe46ab vocab=43afcaa9
-/
theorem parabolicRho₂_nonneg (z w : ParabolicPoint) : 0 ≤ parabolicRho₂ z w := by
  unfold parabolicRho₂
  exact add_nonneg (Real.sqrt_nonneg _) (vec3EuclideanNorm_nonneg _)

/--
@isnad1 id=le.0h2v.s3.82ed5d632dca from=translated src=- shape=e4af5fdd vocab=0daa054a
-/
theorem parabolicDist_le_parabolicRho₂ (z w : ParabolicPoint) :
    parabolicDist z w ≤ parabolicRho₂ z w := by
  unfold parabolicDist parabolicRho₂
  exact max_le (le_add_of_nonneg_left (Real.sqrt_nonneg _))
    (le_add_of_nonneg_right (vec3EuclideanNorm_nonneg _))

/--
@isnad1 id=le.0h2v.s4.18e07da3bb3e from=translated src=- shape=66d59583 vocab=64eb2878
-/
theorem parabolicRho₂_lt_subset_metricBall {z : ParabolicPoint} {R : ℝ} :
    {w | parabolicRho₂ z w < R} ⊆
      @Metric.ball ParabolicPoint parabolicPseudoMetricSpace z R := by
  intro w hw
  change dist w z < R
  rw [dist_comm, dist_eq_parabolicDist]
  exact (parabolicDist_le_parabolicRho₂ z w).trans_lt hw

/--
@isnad1 id=le.0h3v.s4.80c066d86063 from=translated src=- shape=b7159f71 vocab=875644ba
-/
theorem parabolicRieszKernel_nonneg (β : ℝ) (z w : ParabolicPoint) :
    0 ≤ parabolicRieszKernel β z w := by
  exact bot_le

/--
@isnad1 id=mem.2h4v.s6.48978f989dc7 from=translated src=- shape=489650cc vocab=7668fefc
-/
theorem mem_parabolicRieszShell {R : ℝ} {k : ℤ} {z w : ParabolicPoint}
    (hinner : (2 : ℝ) ^ (k : ℝ) * R ≤ parabolicRho₂ z w)
    (houter : parabolicRho₂ z w < (2 : ℝ) ^ ((k : ℝ) + 1) * R) :
    w ∈ parabolicRieszShell R k z := by
  exact ⟨hinner, houter⟩

/--
@isnad1 id=le.2h3v.s5.1473f0156a94 from=translated src=- shape=6ffde6e5 vocab=131a0798
-/
theorem parabolicRieszShell_subset_tail {R : ℝ} {k : ℤ} {z : ParabolicPoint}
    (hR : 0 < R) (hk : 0 ≤ k) :
    parabolicRieszShell R k z ⊆ {w | R ≤ parabolicRho₂ z w} := by
  intro w hw
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
    apply Real.one_le_rpow (by norm_num)
    exact_mod_cast hk
  calc
    R = 1 * R := by ring
    _ ≤ (2 : ℝ) ^ (k : ℝ) * R := mul_le_mul_of_nonneg_right hpow hR.le
    _ ≤ parabolicRho₂ z w := hw.1

/-- A positive point below a radius belongs to a negative dyadic shell.
@isnad1 id=ex.3h3v.s5.e05ccb131dbf from=translated src=- shape=30f93ff9 vocab=01cb6df9
-/
theorem exists_shell_of_pos_lt {z w : ParabolicPoint} {R : ℝ}
    (hR : 0 < R) (hρ : 0 < parabolicRho₂ z w)
    (hρR : parabolicRho₂ z w < R) :
    ∃ k : ℤ, k < 0 ∧ w ∈ parabolicRieszShell R k z := by
  let x : ℝ := parabolicRho₂ z w / R
  let L : ℝ := Real.log 2
  let k : ℤ := ⌊Real.log x / L⌋
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hx : 0 < x := div_pos hρ hR
  have hx1 : x < 1 := by
    dsimp [x]
    exact (div_lt_one hR).2 hρR
  have hkneg : k < 0 := by
    apply (Int.floor_lt).2
    have hlogx : Real.log x < 0 := Real.log_neg hx hx1
    simpa using (div_neg_of_neg_of_pos hlogx hL)
  have hklo : (k : ℝ) ≤ Real.log x / L := Int.floor_le _
  have hkhi : Real.log x / L < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hpowlo : (2 : ℝ) ^ (k : ℝ) ≤ x := by
    apply (Real.strictMonoOn_log.le_iff_le
      (Real.rpow_pos_of_pos (by norm_num) _) hx).mp
    rw [Real.log_rpow (by norm_num)]
    calc
      (k : ℝ) * Real.log 2 ≤ (Real.log x / L) * L := by
        exact mul_le_mul_of_nonneg_right hklo hL.le
      _ = Real.log x := by field_simp [hL.ne']
  have hpowhi : x < (2 : ℝ) ^ ((k : ℝ) + 1) := by
    apply (Real.strictMonoOn_log.lt_iff_lt
      hx (Real.rpow_pos_of_pos (by norm_num) _)).mp
    rw [Real.log_rpow (by norm_num)]
    calc
      Real.log x = (Real.log x / L) * L := by field_simp [hL.ne']
      _ < ((k : ℝ) + 1) * L := mul_lt_mul_of_pos_right hkhi hL
  have hinner : (2 : ℝ) ^ (k : ℝ) * R ≤ parabolicRho₂ z w := by
    simpa [x] using (le_div_iff₀ hR).mp hpowlo
  have houter : parabolicRho₂ z w < (2 : ℝ) ^ ((k : ℝ) + 1) * R := by
    simpa [x] using (div_lt_iff₀ hR).mp hpowhi
  exact ⟨k, hkneg, mem_parabolicRieszShell hinner houter⟩

/-- The zero set of the gauge is contained in its center.
@isnad1 id=le.0h1v.s4.c77be373bc8a from=translated src=- shape=2ad92163 vocab=8a5a6bdc
-/
theorem parabolicRho₂_zero_subset_singleton (z : ParabolicPoint) :
    {w | parabolicRho₂ z w = 0} ⊆ ({z} : Set ParabolicPoint) := by
  intro w hw
  change parabolicRho₂ z w = 0 at hw
  have hspace_nonneg : 0 ≤ vec3EuclideanNorm (z.1 - w.1) :=
    vec3EuclideanNorm_nonneg _
  have htime_nonneg : 0 ≤ Real.sqrt |z.2 - w.2| := Real.sqrt_nonneg _
  have hspace : vec3EuclideanNorm (z.1 - w.1) = 0 := by
    unfold parabolicRho₂ at hw
    nlinarith only [hw, hspace_nonneg, htime_nonneg]
  have htime : Real.sqrt |z.2 - w.2| = 0 := by
    unfold parabolicRho₂ at hw
    nlinarith only [hw, hspace_nonneg, htime_nonneg]
  have hspace_zero : z.1 - w.1 = 0 := by
    rw [vec3EuclideanNorm_eq_l2] at hspace
    exact (WithLp.toLp_eq_zero 2).mp (norm_eq_zero.mp hspace)
  have htime_zero : z.2 - w.2 = 0 := by
    have habs : |z.2 - w.2| = 0 :=
      le_antisymm (Real.sqrt_eq_zero'.mp htime) (abs_nonneg _)
    simpa using abs_eq_zero.mp habs
  have hEq : w = z := Prod.ext (sub_eq_zero.mp hspace_zero).symm
    (sub_eq_zero.mp htime_zero).symm
  exact hEq ▸ mem_singleton z

/-- The kernel-volume scaling identity on a dyadic shell.
@isnad1 id=eq.3h2v.s7.bb1965fe5f40 from=translated src=- shape=4fc86939 vocab=8647af9c
-/
theorem shell_power_identity {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β)
    (_ : β ≤ 5) :
    (ENNReal.ofReal a) ^ (-(5 - β)) * ENNReal.ofReal ((2 * a) ^ 5) =
      ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (a ^ β) := by
  have hx0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
  have hxtop : ENNReal.ofReal a ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    (ENNReal.ofReal a) ^ (-(5 - β)) * ENNReal.ofReal ((2 * a) ^ 5) =
        (ENNReal.ofReal a) ^ (-(5 - β)) *
          (ENNReal.ofReal 2 * ENNReal.ofReal a) ^ 5 := by
      rw [ENNReal.ofReal_pow (by positivity) 5,
        ENNReal.ofReal_mul (by positivity)]
    _ = (ENNReal.ofReal 2) ^ 5 *
          ((ENNReal.ofReal a) ^ (-(5 - β)) * (ENNReal.ofReal a) ^ 5) := by
      rw [mul_pow]
      ac_rfl
    _ = (ENNReal.ofReal 2) ^ 5 * (ENNReal.ofReal a) ^ β := by
      have hcombine :
          (ENNReal.ofReal a) ^ (-(5 - β)) *
              (ENNReal.ofReal a) ^ (5 : ℝ) =
            (ENNReal.ofReal a) ^ β := by
        rw [← ENNReal.rpow_add _ _ hx0 hxtop]
        congr 1
        ring
      have hnat : (ENNReal.ofReal a) ^ (5 : ℕ) =
          (ENNReal.ofReal a) ^ (5 : ℝ) := ENNReal.rpow_natCast _ _ |>.symm
      rw [hnat, hcombine]
    _ = ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (a ^ β) := by
      rw [← ENNReal.ofReal_pow (by positivity) 5,
        ENNReal.ofReal_rpow_of_nonneg ha.le hβ]

/-- Dyadic parabolic shell strictly below the reference scale. -/
def negativeShell (R : ℝ) (n : ℕ) (z : ParabolicPoint) : Set ParabolicPoint :=
  parabolicRieszShell R (Int.negSucc n) z

/-- The geometric constant used by the local kernel estimate. -/
def parabolicLocalKernelConstant (β : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (2 ^ 5) *
      (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
    ∑' n : ℕ, ENNReal.ofReal
      (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)

/--
@isnad1 id=le.1h4v.s5.9195461f0022 from=translated src=- shape=ba95dadd vocab=d5928b64
-/
theorem parabolicRieszPotential_mono {β : ℝ} {f g : ParabolicPoint → ℝ}
    (hfg : ∀ w, |f w| ≤ |g w|) (z : ParabolicPoint) :
    parabolicRieszPotential β f z ≤ parabolicRieszPotential β g z := by
  unfold parabolicRieszPotential
  apply lintegral_mono
  intro w
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hfg w)) _

end CKN.Foundation.Parabolic.Morrey
