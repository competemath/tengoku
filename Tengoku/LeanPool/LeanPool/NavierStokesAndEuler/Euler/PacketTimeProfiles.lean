/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Tengoku
meta import Lean.Meta.Tactic.NormCast

/-! The actual continuous time weights for the high and mean packet grades. -/

section

/-! Exact time-profile bookkeeping for the high, mean, and previous-corrector terms. -/

@[expose] public section

namespace EulerPacketTimeProfile

/-- Mean scale, given by `H^(2*p-2)`. -/
def meanScale (H : ℝ) (p : ℕ) : ℝ := H^(2*p-2)
/-- High scale, given by `γ*meanScale H p`. -/
def highScale (γ H : ℝ) (p : ℕ) : ℝ := γ*meanScale H p

/--
@isnad1 id=lt.1h2v.s4.08f3f189751d from=translated src=- shape=9141f3a7 vocab=a92b6d3f
-/
theorem meanScale_pos (H : ℝ) (hH : 0 < H) (p : ℕ) : 0 < meanScale H p := pow_pos hH _
/--
@isnad1 id=lt.2h3v.s5.c36368df8405 from=translated src=- shape=b4e35a70 vocab=79dac1c7
-/
theorem highScale_pos (γ H : ℝ) (hγ : 0 < γ) (hH : 0 < H) (p : ℕ) :
    0 < highScale γ H p := mul_pos hγ (meanScale_pos H hH p)

/--
@isnad1 id=le.2h3v.s5.9b055eeaacb0 from=translated src=- shape=ae7cab87 vocab=6c621c88
-/
theorem meanScale_mono (H : ℝ) (hH : 1 ≤ H) {i j : ℕ} (hij : i ≤ j) :
    meanScale H i ≤ meanScale H j :=
  pow_le_pow_right₀ hH (by omega : 2*i-2 ≤ 2*j-2)

/--
@isnad1 id=le.3h4v.s5.78603db22f3a from=translated src=- shape=f230b30b vocab=8efe744c
-/
theorem highScale_mono (γ H : ℝ) (hγ : 0 ≤ γ) (hH : 1 ≤ H) {i j : ℕ} (hij : i ≤ j) :
    highScale γ H i ≤ highScale γ H j :=
  mul_le_mul_of_nonneg_left (meanScale_mono H hH hij) hγ

/--
@isnad1 id=eq.3h4v.s6.aa77f6bd40a6 from=translated src=- shape=d1b126b8 vocab=3d854c95
-/
theorem meanScale_slow_identity (H : ℝ) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    meanScale H i*meanScale H j*H^2 = meanScale H p := by
  simp only [meanScale,← pow_add]
  congr 1
  omega

/--
@isnad1 id=le.4h4v.s6.98dee9e444dc from=translated src=- shape=d81bb46c vocab=ec28dcef
-/
theorem slow_mean_mean (H : ℝ) (hH : 1 ≤ H) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    meanScale H i*meanScale H j ≤ meanScale H p := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hs : (1 : ℝ) ≤ H^2 := by nlinarith
  calc
    _ ≤ (meanScale H i*meanScale H j)*H^2 :=
      le_mul_of_one_le_right (mul_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _)) hs
    _ = _ := meanScale_slow_identity H i j p hi hj hp

/--
@isnad1 id=le.6h5v.s6.5c0431f2d533 from=translated src=- shape=c96b3ccd vocab=47952b05
-/
theorem slow_high_high_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    highScale γ H i*highScale γ H j ≤ meanScale H p := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  calc
    _ = γ^2*(meanScale H i*meanScale H j) := by unfold highScale; ring
    _ ≤ H^2*(meanScale H i*meanScale H j) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hγ hγH 2)
        (mul_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _))
    _ = meanScale H i*meanScale H j*H^2 := by ring
    _ = _ := meanScale_slow_identity H i j p hi hj hp

/--
@isnad1 id=le.6h5v.s6.ecf9b2b4f73f from=translated src=- shape=8af56122 vocab=5eb5944d
-/
theorem slow_high_high_high (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    highScale γ H i*highScale γ H j ≤ highScale γ H p := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hh : H ≤ H^2 := by nlinarith
  have hγ2 : γ^2 ≤ γ*H^2 := by nlinarith [mul_nonneg hγ (sub_nonneg.mpr (hγH.trans hh))]
  calc
    _ = γ^2*(meanScale H i*meanScale H j) := by unfold highScale; ring
    _ ≤ (γ*H^2)*(meanScale H i*meanScale H j) :=
      mul_le_mul_of_nonneg_right hγ2 (mul_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _))
    _ = γ*(meanScale H i*meanScale H j*H^2) := by ring
    _ = _ := congrArg (γ * ·) (meanScale_slow_identity H i j p hi hj hp)

/--
@isnad1 id=le.5h5v.s6.265cfb976302 from=translated src=- shape=3653e956 vocab=47952b05
-/
theorem slow_mean_high_high (γ H : ℝ) (hγ : 0 ≤ γ) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    meanScale H i*highScale γ H j ≤ highScale γ H p := by
  have h := mul_le_mul_of_nonneg_left (slow_mean_mean H hH i j p hi hj hp) hγ
  simpa only [highScale,mul_left_comm] using h

/--
@isnad1 id=le.6h5v.s6.e8810451bd1f from=translated src=- shape=4486af7d vocab=47952b05
-/
theorem slow_mean_high_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    meanScale H i*highScale γ H j ≤ meanScale H p := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hh : γ ≤ H^2 := by nlinarith
  calc
    _ = γ*(meanScale H i*meanScale H j) := by unfold highScale; ring
    _ ≤ H^2*(meanScale H i*meanScale H j) :=
      mul_le_mul_of_nonneg_right hh (mul_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _))
    _ = meanScale H i*meanScale H j*H^2 := by ring
    _ = _ := meanScale_slow_identity H i j p hi hj hp

/--
@isnad1 id=eq.3h5v.s6.c292f4318819 from=translated src=- shape=6e02872d vocab=47952b05
-/
theorem fast_mean_high (γ H : ℝ) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p + 1) :
    meanScale H i*highScale γ H j = highScale γ H p := by
  unfold highScale meanScale
  rw [mul_left_comm,← pow_add]
  congr 1
  congr 1
  omega

/--
@isnad1 id=le.6h5v.s6.bbcd0b97e3b8 from=translated src=- shape=7c713691 vocab=fb15a795
-/
theorem fast_corrector_high_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i + j = p + 1) :
    highScale γ H (i-1)*highScale γ H j ≤ meanScale H p :=
  slow_high_high_mean γ H hγ hγH hH (i-1) j p (by omega) hj (by omega)

/--
@isnad1 id=le.6h5v.s6.ce8430e989b5 from=translated src=- shape=6146e96d vocab=a03deb3e
-/
theorem fast_corrector_high_high (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i + j = p + 1) :
    highScale γ H (i-1)*highScale γ H j ≤ highScale γ H p :=
  slow_high_high_high γ H hγ hγH hH (i-1) j p (by omega) hj (by omega)

/--
@isnad1 id=le.6h5v.s7.172850478338 from=translated src=- shape=9fbceed5 vocab=fb15a795
-/
theorem fast_corrector_corrector_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j) (hp : i + j = p + 1) :
    highScale γ H (i-1)*highScale γ H (j-1) ≤ meanScale H p :=
  (slow_high_high_mean γ H hγ hγH hH (i-1) (j-1) (p-1) (by omega) (by omega) (by omega)).trans
    (meanScale_mono H hH (Nat.sub_le p 1))

/--
@isnad1 id=le.6h5v.s7.2dcbc113245b from=translated src=- shape=98777b74 vocab=a03deb3e
-/
theorem fast_corrector_corrector_high (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j) (hp : i + j = p + 1) :
    highScale γ H (i-1)*highScale γ H (j-1) ≤ highScale γ H p :=
  (slow_high_high_high γ H hγ hγH hH (i-1) (j-1) (p-1) (by omega) (by omega) (by omega)).trans
    (highScale_mono γ H hγ hH (Nat.sub_le p 1))

/--
@isnad1 id=le.4h3v.s6.a9c24ba833a1 from=translated src=- shape=97d86d2c vocab=0206e320
-/
theorem previous_linear_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (p : ℕ) (hp : 2 ≤ p) : highScale γ H (p-1) ≤ meanScale H p := by
  have h := slow_mean_high_mean γ H hγ hγH hH 1 (p-1) p (by omega) (by omega) (by omega)
  simpa only [meanScale,show 2*1-2=0 by omega,pow_zero,one_mul] using h

end EulerPacketTimeProfile

end

end

@[expose] public section

noncomputable section

namespace EulerPacketTimeProfile

open Set

variable (K : Type*) [TopologicalSpace K]

/-- Scales data, collecting `growth`, `growth_pos`, `H0`, `H0_one_le`, `growth_le`. -/
structure Scales where
  /-- Growth of `Scales`, of type `C(K,ℝ)`. -/
  growth : C(K,ℝ)
  growth_pos : ∀ t, 0 < growth t
  /-- H0 of `Scales`, of type `ℝ`. -/
  H0 : ℝ
  H0_one_le : 1 ≤ H0
  growth_le : ∀ t, growth t ≤ H0

namespace Scales

variable {K}

/-- Compactness supplies the single grade-independent upper scale. -/
def ofGrowth [CompactSpace K] (g : C(K, ℝ)) (hg : ∀ t, 0 < g t) : Scales K where
  growth := g
  growth_pos := hg
  H0 := max 1 ‖g‖
  H0_one_le := le_max_left _ _
  growth_le t := (le_trans (le_abs_self (g t))
    (by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm t)).trans (le_max_right _ _)

variable (S : Scales K)

/-- Mean, given by `ContinuousMap.const K (meanScale S.H0 p)`. -/
def mean (p : ℕ) : C(K,ℝ) := ContinuousMap.const K (meanScale S.H0 p)
/-- High, given by `S.growth*S.mean p`. -/
def high (p : ℕ) : C(K,ℝ) := S.growth*S.mean p

/--
@isnad1 id=eq.0h4v.s5.ab38c0f1da9e from=translated src=- shape=1a98c4bc vocab=91710bcb
-/
@[simp] theorem mean_apply (p : ℕ) (t : K) : S.mean p t = meanScale S.H0 p := rfl
/--
@isnad1 id=eq.0h4v.s6.af71bd536860 from=translated src=- shape=88f64757 vocab=dee85d51
-/
@[simp] theorem high_apply (p : ℕ) (t : K) : S.high p t = highScale (S.growth t) S.H0 p := rfl

/--
@isnad1 id=lt.0h2v.s4.4f650f65e376 from=translated src=- shape=38fc717e vocab=08e491d3
-/
theorem H0_pos : 0 < S.H0 := zero_lt_one.trans_le S.H0_one_le
/--
@isnad1 id=lt.0h4v.s5.bbdffd81604b from=translated src=- shape=8d1423b9 vocab=683cfd21
-/
theorem mean_pos (p : ℕ) (t : K) : 0 < S.mean p t := meanScale_pos S.H0 S.H0_pos p
/--
@isnad1 id=lt.0h4v.s5.246cb4238ce8 from=translated src=- shape=8d1423b9 vocab=e896bbf8
-/
theorem high_pos (p : ℕ) (t : K) : 0 < S.high p t :=
  highScale_pos (S.growth t) S.H0 (S.growth_pos t) S.H0_pos p

/--
@isnad1 id=le.1h5v.s6.0073ed9a6e29 from=translated src=- shape=99df6965 vocab=d4554c10
-/
theorem mean_mono {i j : ℕ} (hij : i ≤ j) (t : K) : S.mean i t ≤ S.mean j t :=
  meanScale_mono S.H0 S.H0_one_le hij

/--
@isnad1 id=le.1h5v.s6.b39b40b387c7 from=translated src=- shape=99df6965 vocab=a13076d4
-/
theorem high_mono {i j : ℕ} (hij : i ≤ j) (t : K) : S.high i t ≤ S.high j t :=
  highScale_mono (S.growth t) S.H0 (S.growth_pos t).le S.H0_one_le hij

/--
@isnad1 id=eq.0h3v.s6.1eec697304fa from=translated src=- shape=9c07000d vocab=af1bb8ae
-/
theorem high_one (t : K) : S.high 1 t = S.growth t := by
  simp only [high_apply,highScale,meanScale,show 2*1-2=0 by omega,pow_zero,mul_one]

/--
@isnad1 id=le.3h6v.s7.ecc21dc6ee9c from=translated src=- shape=5bb05adc vocab=f3bbc8bc
-/
theorem slow_mean_mean_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.mean i t*S.mean j t ≤ S.mean p t := slow_mean_mean S.H0 S.H0_one_le i j p hi hj hp

/--
@isnad1 id=le.3h6v.s7.d7c734974cd7 from=translated src=- shape=5bb05adc vocab=3f059547
-/
theorem slow_high_high_mean_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.high i t*S.high j t ≤ S.mean p t :=
  slow_high_high_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t) S.H0_one_le i j p hi hj
      hp

/--
@isnad1 id=le.3h6v.s7.ff62d008a23a from=translated src=- shape=5bb05adc vocab=c7201805
-/
theorem slow_high_high_high_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.high i t*S.high j t ≤ S.high p t :=
  slow_high_high_high (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t) S.H0_one_le i j p hi hj
      hp

/--
@isnad1 id=le.3h6v.s7.14b91ae6acd3 from=translated src=- shape=5bb05adc vocab=3f059547
-/
theorem slow_mean_high_mean_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.mean i t*S.high j t ≤ S.mean p t :=
  slow_mean_high_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t) S.H0_one_le i j p hi hj
      hp

/--
@isnad1 id=le.3h6v.s7.2434538348e8 from=translated src=- shape=2495d6ec vocab=3f059547
-/
theorem slow_mean_high_high_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.mean i t*S.high j t ≤ S.high p t :=
  slow_mean_high_high (S.growth t) S.H0 (S.growth_pos t).le S.H0_one_le i j p hi hj hp

/--
@isnad1 id=eq.3h6v.s7.27c37b66d1a3 from=translated src=- shape=ddd5f4c4 vocab=3f059547
-/
theorem fast_mean_high_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p + 1) (t : K) :
    S.mean i t*S.high j t = S.high p t :=
  fast_mean_high (S.growth t) S.H0 i j p hi hj hp

/--
@isnad1 id=le.3h6v.s7.dba6e9c19d9f from=translated src=- shape=f04b67e3 vocab=5135081d
-/
theorem fast_corrector_high_mean_bound (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j)
    (hp : i + j = p + 1) (t : K) : S.high (i-1) t*S.high j t ≤ S.mean p t :=
  fast_corrector_high_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t)
    S.H0_one_le i j p hi hj hp

/--
@isnad1 id=le.3h6v.s7.ce9491cc5a53 from=translated src=- shape=ec55d28d vocab=573d8ff7
-/
theorem fast_corrector_high_high_bound (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j)
    (hp : i + j = p + 1) (t : K) : S.high (i-1) t*S.high j t ≤ S.high p t :=
  fast_corrector_high_high (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t)
    S.H0_one_le i j p hi hj hp

/--
@isnad1 id=le.3h6v.s7.504ca5dbd75f from=translated src=- shape=5056b82e vocab=5135081d
-/
theorem fast_corrector_corrector_mean_bound (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hp : i + j = p + 1) (t : K) : S.high (i-1) t*S.high (j-1) t ≤ S.mean p t :=
  fast_corrector_corrector_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t)
    S.H0_one_le i j p hi hj hp

/--
@isnad1 id=le.3h6v.s7.14bf3d4d7966 from=translated src=- shape=963fc03d vocab=573d8ff7
-/
theorem fast_corrector_corrector_high_bound (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hp : i + j = p + 1) (t : K) : S.high (i-1) t*S.high (j-1) t ≤ S.high p t :=
  fast_corrector_corrector_high (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t)
    S.H0_one_le i j p hi hj hp

/--
@isnad1 id=le.1h4v.s6.df2adb092e84 from=translated src=- shape=95236b22 vocab=39241745
-/
theorem previous_linear_mean_bound (p : ℕ) (hp : 2 ≤ p) (t : K) : S.high (p-1) t ≤ S.mean p t :=
  previous_linear_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t) S.H0_one_le p hp

end Scales
end EulerPacketTimeProfile
