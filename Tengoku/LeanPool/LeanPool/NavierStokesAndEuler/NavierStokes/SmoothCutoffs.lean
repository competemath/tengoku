/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Tengoku.Seed.Analysis.Calculus.BumpFunction.Basic
public import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Defs
import Tengoku.Seed.Analysis.Calculus.BumpFunction.InnerProduct

namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Constructed smooth cutoffs for the diagonal sum and time switch

The fixed cutoff is an actual Mathlib `ContDiffBump`, centered at zero, with
inner radius `1/2` and outer radius `1`. Smoothness below is `C^∞`, written `∞`;
no analyticity assertion is made. The scaled cutoff and time switch are explicit
functions obtained from that bump. No convergence or PDE claim is encoded here.
-/

@[expose] public section

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace NavierStokes.SmoothCutoffs

/-- Cutoff bump, bundling `rIn`, `rOut`, `rIn_pos`, `rIn_lt_rOut`. -/
def cutoffBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Cutoff, given by `cutoffBump`. -/
def cutoff : ℝ → ℝ :=
  letI : HasContDiffBump ℝ := by infer_instance
  cutoffBump

/--
@isnad1 id=contdiff.0h0v.s4.d5c9266db4d4 from=translated src=- shape=3cea26be vocab=7a1b01d4
-/
theorem cutoff_contDiff : ContDiff ℝ ∞ cutoff := cutoffBump.contDiff

/--
@isnad1 id=mem.0h1v.s4.1bc934434e1e from=translated src=- shape=828ff9db vocab=bf93529c
-/
theorem cutoff_mem_Icc (x : ℝ) : cutoff x ∈ Icc (0 : ℝ) 1 :=
  ⟨cutoffBump.nonneg, cutoffBump.le_one⟩

/--
@isnad1 id=eq.1h1v.s5.de4de58778ad from=translated src=- shape=7f1c967e vocab=4dc6c12f
-/
theorem cutoff_one_of_abs_le {x : ℝ} (hx : |x| ≤ 1 / 2) : cutoff x = 1 := by
  apply cutoffBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, cutoffBump] using hx

/--
@isnad1 id=eq.1h1v.s4.95a1b09695ee from=translated src=- shape=7a8068be vocab=52df52e5
-/
theorem cutoff_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : cutoff x = 0 := by
  apply cutoffBump.zero_of_le_dist
  simpa [Real.dist_eq, cutoffBump] using hx

/--
@isnad1 id=eq.1h1v.s4.d106bbdd7a8c from=translated src=- shape=97c35add vocab=3b07a18f
-/
theorem cutoff_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) : cutoff x = 0 :=
  cutoff_zero_of_one_le_abs (hx.trans (le_abs_self x))

/--
@isnad1 id=eq.0h0v.s4.9bd28ae4d22a from=translated src=- shape=66c352d6 vocab=5f238460
-/
theorem cutoff_support : support cutoff = Ioo (-1 : ℝ) 1 := by
  change support (cutoffBump : ℝ → ℝ) = _
  rw [cutoffBump.support_eq]
  ext x
  simp [Metric.mem_ball, cutoffBump, abs_lt]

/--
@isnad1 id=eq.0h0v.s4.db2bf3c00072 from=translated src=- shape=66c352d6 vocab=35085167
-/
theorem cutoff_tsupport : tsupport cutoff = Icc (-1 : ℝ) 1 := by
  change tsupport (cutoffBump : ℝ → ℝ) = _
  rw [cutoffBump.tsupport_eq]
  ext x
  simp [Metric.mem_closedBall, cutoffBump, abs_le]

/--
@isnad1 id=hascompa.0h0v.s3.78519d55f16d from=translated src=- shape=e3d48bcb vocab=870ccfd3
-/
theorem cutoff_hasCompactSupport : HasCompactSupport cutoff :=
  cutoffBump.hasCompactSupport

/--
@isnad1 id=eventual.1h1v.s5.5b6141d9da16 from=translated src=- shape=20e10d12 vocab=5ff29fb0
-/
theorem cutoff_eventually_one {x : ℝ} (hx : |x| < 1 / 2) :
    cutoff =ᶠ[𝓝 x] (fun _ => 1) := by
  apply cutoffBump.eventuallyEq_one_of_mem_ball
  simpa [Metric.mem_ball, cutoffBump] using hx

/--
@isnad1 id=eventual.1h1v.s5.5b6af1fb24aa from=translated src=- shape=e6e6a811 vocab=eb1036d0
-/
theorem cutoff_eventually_zero {x : ℝ} (hx : 1 < |x|) :
    cutoff =ᶠ[𝓝 x] (fun _ => 0) := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  rw [cutoff_tsupport]
  intro hmem
  exact (not_le_of_gt hx) (abs_le.mpr hmem)

/--
@isnad1 id=eventual.0h0v.s4.0d5556a7011d from=translated src=- shape=a5833db6 vocab=9491f33e
-/
theorem cutoff_eventually_one_at_zero : cutoff =ᶠ[𝓝 0] (fun _ => 1) :=
  cutoff_eventually_one (by norm_num)

/--
@isnad1 id=eq.0h2v.s5.115379be19a1 from=translated src=- shape=f47bc39f vocab=53fd09fe
-/
theorem iteratedDeriv_const_succ (n : ℕ) (c : ℝ) :
    iteratedDeriv (n + 1) (fun _ : ℝ => c) = (fun _ => 0) := by
  induction n with
  | zero =>
      ext x
      simp [iteratedDeriv_succ]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      ext x
      simp

/--
@isnad1 id=eq.1h2v.s6.ee1efc871dd2 from=translated src=- shape=0dd28721 vocab=8f10ba9f
-/
theorem cutoff_iteratedDeriv_zero_inside (n : ℕ) {x : ℝ} (hx : |x| < 1 / 2) :
    iteratedDeriv (n + 1) cutoff x = 0 := by
  rw [(cutoff_eventually_one hx).iteratedDeriv_eq (n + 1), iteratedDeriv_const_succ]

/--
@isnad1 id=eq.1h2v.s5.9fa8d6c30e07 from=translated src=- shape=089f3301 vocab=881f1de5
-/
theorem cutoff_iteratedDeriv_zero_outside (n : ℕ) {x : ℝ} (hx : 1 < |x|) :
    iteratedDeriv (n + 1) cutoff x = 0 := by
  rw [(cutoff_eventually_zero hx).iteratedDeriv_eq (n + 1), iteratedDeriv_const_succ]

/-- Every positive-order derivative is supported in a fixed collar away from zero.
@isnad1 id=le.0h1v.s6.21365930ba11 from=translated src=- shape=d09b876f vocab=be41166e
-/
theorem cutoff_iteratedDeriv_support (n : ℕ) :
    support (iteratedDeriv (n + 1) cutoff) ⊆ {x : ℝ | 1 / 2 ≤ |x| ∧ |x| ≤ 1} := by
  intro x hx
  change iteratedDeriv (n + 1) cutoff x ≠ 0 at hx
  constructor
  · by_contra h
    exact hx (cutoff_iteratedDeriv_zero_inside n (lt_of_not_ge h))
  · by_contra h
    exact hx (cutoff_iteratedDeriv_zero_outside n (lt_of_not_ge h))

/--
@isnad1 id=le.0h1v.s6.ea8de88314e4 from=translated src=- shape=d09b876f vocab=e49a1c87
-/
theorem cutoff_iteratedDeriv_tsupport (n : ℕ) :
    tsupport (iteratedDeriv (n + 1) cutoff) ⊆ {x : ℝ | 1 / 2 ≤ |x| ∧ |x| ≤ 1} := by
  apply closure_minimal (cutoff_iteratedDeriv_support n)
  exact (isClosed_le continuous_const continuous_abs).inter
    (isClosed_le continuous_abs continuous_const)

/--
@isnad1 id=hascompa.0h1v.s4.710b0ebbb0bf from=translated src=- shape=d6a36d95 vocab=3daed0b8
-/
theorem cutoff_iteratedDeriv_hasCompactSupport (n : ℕ) :
    HasCompactSupport (iteratedDeriv n cutoff) := by
  induction n with
  | zero => simpa using cutoff_hasCompactSupport
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/--
@isnad1 id=ex.0h1v.s5.a1433c1bcbf4 from=translated src=- shape=7b9199a9 vocab=52fff2f7
-/
theorem cutoff_iteratedDeriv_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |iteratedDeriv n cutoff x| ≤ C := by
  obtain ⟨C, hC⟩ := (cutoff_iteratedDeriv_hasCompactSupport n).exists_bound_of_continuous
    (cutoff_contDiff.continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx : |iteratedDeriv n cutoff x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x
  exact hx.trans (le_max_left _ _)

/-- Scaled cutoff, defined pointwise by `cutoff (a * q)`. -/
def scaledCutoff (a : ℝ) : ℝ → ℝ := fun q => cutoff (a * q)

/--
@isnad1 id=contdiff.0h1v.s5.5e5a1c389a2e from=translated src=- shape=0fc4d29f vocab=38a68173
-/
theorem scaledCutoff_contDiff (a : ℝ) : ContDiff ℝ ∞ (scaledCutoff a) :=
  cutoff_contDiff.comp (contDiff_const.mul contDiff_id)

/--
@isnad1 id=mem.0h2v.s4.57c436892dcb from=translated src=- shape=2e184271 vocab=7aacafcf
-/
theorem scaledCutoff_mem_Icc (a q : ℝ) : scaledCutoff a q ∈ Icc (0 : ℝ) 1 :=
  cutoff_mem_Icc (a * q)

/--
@isnad1 id=eq.1h2v.s5.3aa3d6d85631 from=translated src=- shape=c4838bad vocab=aa7f1400
-/
theorem scaledCutoff_one_of_abs_le {a q : ℝ} (hq : |a * q| ≤ 1 / 2) :
    scaledCutoff a q = 1 := cutoff_one_of_abs_le hq

/--
@isnad1 id=eq.1h2v.s5.5141192032e9 from=translated src=- shape=f3e0d1f6 vocab=7f2dee79
-/
theorem scaledCutoff_zero_of_one_le_abs {a q : ℝ} (hq : 1 ≤ |a * q|) :
    scaledCutoff a q = 0 := cutoff_zero_of_one_le_abs hq

/--
@isnad1 id=eq.2h2v.s5.8b056db59381 from=translated src=- shape=566e0c6a vocab=9cf4c1fc
-/
theorem scaledCutoff_zero_of_inv_le {a q : ℝ} (ha : 0 < a) (hq : 1 / a ≤ q) :
    scaledCutoff a q = 0 := by
  apply cutoff_zero_of_one_le
  have hprod := (div_le_iff₀ ha).mp hq
  nlinarith

/--
@isnad1 id=hascompa.1h1v.s4.9a795108286b from=translated src=- shape=aa37abb2 vocab=1be0fff5
-/
theorem scaledCutoff_hasCompactSupport {a : ℝ} (ha : a ≠ 0) :
    HasCompactSupport (scaledCutoff a) := by
  change HasCompactSupport (fun x => cutoff (a * x))
  have hc : HasCompactSupport (fun x : ℝ => cutoff (a • x)) :=
    cutoff_hasCompactSupport.comp_smul (G₀ := ℝ) (c := a) ha
  simpa only [smul_eq_mul] using hc

/--
@isnad1 id=eventual.1h2v.s6.e7740f362219 from=translated src=- shape=5d7cf6fa vocab=40ca0d07
-/
theorem scaledCutoff_eventually_one {a q : ℝ} (hq : |a * q| < 1 / 2) :
    scaledCutoff a =ᶠ[𝓝 q] (fun _ => 1) :=
  (cutoff_eventually_one hq).comp_tendsto
    (continuous_const.mul continuous_id).continuousAt

/--
@isnad1 id=eventual.1h2v.s5.78f88567000f from=translated src=- shape=b143308c vocab=8ccba8d7
-/
theorem scaledCutoff_eventually_zero {a q : ℝ} (hq : 1 < |a * q|) :
    scaledCutoff a =ᶠ[𝓝 q] (fun _ => 0) :=
  (cutoff_eventually_zero hq).comp_tendsto
    (continuous_const.mul continuous_id).continuousAt

/--
@isnad1 id=eventual.0h1v.s4.5c43cec57c43 from=translated src=- shape=988e3350 vocab=627ca552
-/
theorem scaledCutoff_eventually_one_at_zero (a : ℝ) :
    scaledCutoff a =ᶠ[𝓝 0] (fun _ => 1) :=
  scaledCutoff_eventually_one (by simp)

/-- Every finite list of stage cutoffs has a common plateau around zero.
@isnad1 id=eventual.0h3v.s5.548a9c8db72d from=translated src=- shape=d16db290 vocab=dcde9345
-/
theorem finite_scaledCutoffs_eventually_one {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ∀ᶠ q in 𝓝 0, ∀ i ∈ s, scaledCutoff (a i) q = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      filter_upwards [ih, scaledCutoff_eventually_one_at_zero (a i)] with q hq hqi
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hqi
      · exact hq j hj

/-- If the scales diverge, a common neighborhood of each positive `q₀` meets
only finitely many stage cutoffs. The neighborhood is explicitly `q > q₀/2`.
@isnad1 id=ex.2h2v.s6.0e23df190b11 from=translated src=- shape=6e399a7b vocab=17110c0e
-/
theorem scaledCutoffs_zero_on_common_neighborhood (a : ℕ → ℝ)
    (ha : Tendsto a atTop atTop) {q₀ : ℝ} (hq₀ : 0 < q₀) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℝ, q₀ / 2 < q → scaledCutoff (a n) q = 0 := by
  have htail : ∀ᶠ n in atTop, (2 / q₀ : ℝ) ≤ a n :=
    ha.eventually (eventually_ge_atTop (2 / q₀))
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  refine ⟨N, fun n hn q hq => ?_⟩
  have ha' : 0 < a n := lt_of_lt_of_le (div_pos (by norm_num) hq₀) (hN n hn)
  apply cutoff_zero_of_one_le
  calc
    (1 : ℝ) = (2 / q₀) * (q₀ / 2) := by field_simp
    _ ≤ a n * q := mul_le_mul (hN n hn) hq.le (half_pos hq₀).le ha'.le

/-- The exact all-order chain rule for the scale used in Sections 7 and 11.
@isnad1 id=eq.0h2v.s6.85272f7a897c from=translated src=- shape=0e02b9ed vocab=3a9c5f78
-/
theorem scaledCutoff_iteratedDeriv (a : ℝ) (n : ℕ) :
    iteratedDeriv n (scaledCutoff a) =
      fun q => a ^ n * iteratedDeriv n cutoff (a * q) :=
  iteratedDeriv_comp_const_mul
    (cutoff_contDiff.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) a

/--
@isnad1 id=le.0h2v.s6.d02dff2ed87a from=translated src=- shape=f7eb1106 vocab=d0d1a265
-/
theorem scaledCutoff_iteratedDeriv_support (a : ℝ) (n : ℕ) :
    support (iteratedDeriv (n + 1) (scaledCutoff a)) ⊆
      {q : ℝ | 1 / 2 ≤ |a * q| ∧ |a * q| ≤ 1} := by
  intro q hq
  change iteratedDeriv (n + 1) (scaledCutoff a) q ≠ 0 at hq
  rw [scaledCutoff_iteratedDeriv] at hq
  apply cutoff_iteratedDeriv_support n
  change iteratedDeriv (n + 1) cutoff (a * q) ≠ 0
  intro hz
  exact hq (by simp [hz])

/-- Powers of the scale on derivative support are bounded by powers of `q⁻¹`.
@isnad1 id=le.3h4v.s6.23fe33edf9a7 from=translated src=- shape=dfd62981 vocab=596d7b35
-/
theorem scale_power_bound {a q : ℝ} (ha : 0 ≤ a) (hq : 0 < q) (n b : ℕ)
    (hs : iteratedDeriv (n + 1) (scaledCutoff a) q ≠ 0) :
    a ^ b ≤ (1 / q) ^ b := by
  have hup := (scaledCutoff_iteratedDeriv_support a n hs).2
  rw [abs_of_nonneg (mul_nonneg ha hq.le)] at hup
  exact pow_le_pow_left₀ ha ((le_div_iff₀ hq).mpr hup) b

/-- Uniform scale-independent derivative loss used by the diagonal cutoff argument.
@isnad1 id=ex.0h1v.s7.b14b2543f913 from=translated src=- shape=08aed08d vocab=c59ca314
-/
theorem scaledCutoff_iteratedDeriv_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a q : ℝ, 0 ≤ a → 0 < q →
      |iteratedDeriv (n + 1) (scaledCutoff a) q| ≤ C * (1 / q) ^ (n + 1) := by
  obtain ⟨C, hC, hbound⟩ := cutoff_iteratedDeriv_bounded (n + 1)
  refine ⟨C, hC, fun a q ha hq => ?_⟩
  by_cases hz : iteratedDeriv (n + 1) (scaledCutoff a) q = 0
  · rw [hz, abs_zero]
    positivity
  · have hpow := scale_power_bound ha hq n (n + 1) hz
    rw [scaledCutoff_iteratedDeriv, abs_mul, abs_of_nonneg (pow_nonneg ha _)]
    calc
      _ ≤ a ^ (n + 1) * C := mul_le_mul_of_nonneg_left (hbound (a * q)) (pow_nonneg ha _)
      _ ≤ (1 / q) ^ (n + 1) * C := mul_le_mul_of_nonneg_right hpow hC
      _ = _ := mul_comm _ _

/-- Zero near time zero, and one for every time at least `3/4`. -/
def timeSwitch (t : ℝ) : ℝ := 1 - scaledCutoff (4 / 3) t

/--
@isnad1 id=contdiff.0h0v.s4.f76252fa54a1 from=translated src=- shape=3cea26be vocab=6f8ce3a4
-/
theorem timeSwitch_contDiff : ContDiff ℝ ∞ timeSwitch :=
  contDiff_const.sub (scaledCutoff_contDiff (4 / 3))

/--
@isnad1 id=mem.0h1v.s4.c021df1bdcc3 from=translated src=- shape=828ff9db vocab=67c1695c
-/
theorem timeSwitch_mem_Icc (t : ℝ) : timeSwitch t ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hlo, hhi⟩ := scaledCutoff_mem_Icc (4 / 3) t
  unfold timeSwitch
  constructor <;> linarith

/--
@isnad1 id=eq.1h1v.s5.626e075e5990 from=translated src=- shape=7f1c967e vocab=85a49abc
-/
theorem timeSwitch_zero_of_abs_le {t : ℝ} (ht : |t| ≤ 3 / 8) : timeSwitch t = 0 := by
  have hs : |(4 / 3 : ℝ) * t| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
    linarith
  simp [timeSwitch, scaledCutoff_one_of_abs_le hs]

/--
@isnad1 id=eq.1h1v.s5.486f43aac351 from=translated src=- shape=c1676f1c vocab=e23664ab
-/
theorem timeSwitch_one_of_three_quarters_le {t : ℝ} (ht : 3 / 4 ≤ t) :
    timeSwitch t = 1 := by
  have hs : (1 : ℝ) ≤ (4 / 3) * t := by linarith
  simp [timeSwitch, scaledCutoff, cutoff_zero_of_one_le hs]

/--
@isnad1 id=eventual.0h0v.s4.a1dcc32a835e from=translated src=- shape=a5833db6 vocab=8d28ff86
-/
theorem timeSwitch_eventually_zero : timeSwitch =ᶠ[𝓝 0] (fun _ => 0) := by
  filter_upwards [scaledCutoff_eventually_one_at_zero (4 / 3)] with t ht
  simp [timeSwitch, ht]

/--
@isnad1 id=eventual.1h1v.s5.1268eeaf380a from=translated src=- shape=b525f8ea vocab=45ed7126
-/
theorem timeSwitch_eventually_one {t : ℝ} (ht : 3 / 4 < t) :
    timeSwitch =ᶠ[𝓝 t] (fun _ => 1) := by
  have hs : (1 : ℝ) < |(4 / 3) * t| := by
    have hprod : (1 : ℝ) < (4 / 3) * t := by linarith
    exact hprod.trans_le (le_abs_self _)
  filter_upwards [scaledCutoff_eventually_zero hs] with s hs
  simp [timeSwitch, hs]

/--
@isnad1 id=eq.0h1v.s5.61cbba6fa34e from=translated src=- shape=8acbed18 vocab=9243c224
-/
theorem timeSwitch_iteratedDeriv_at_zero (n : ℕ) :
    iteratedDeriv (n + 1) timeSwitch 0 = 0 := by
  rw [timeSwitch_eventually_zero.iteratedDeriv_eq (n + 1), iteratedDeriv_const_succ]

/--
@isnad1 id=eq.1h2v.s6.16435014e30a from=translated src=- shape=774b9f51 vocab=3129549e
-/
theorem timeSwitch_iteratedDeriv_late (n : ℕ) {t : ℝ} (ht : 3 / 4 < t) :
    iteratedDeriv (n + 1) timeSwitch t = 0 := by
  rw [(timeSwitch_eventually_one ht).iteratedDeriv_eq (n + 1), iteratedDeriv_const_succ]

/--
@isnad1 id=eq.0h2v.s7.02e3bdc14e30 from=translated src=- shape=e65e3e8e vocab=116c2274
-/
theorem timeSwitch_iteratedDeriv_formula (n : ℕ) (t : ℝ) :
    iteratedDeriv (n + 1) timeSwitch t =
      -((4 / 3 : ℝ) ^ (n + 1) * iteratedDeriv (n + 1) cutoff ((4 / 3) * t)) := by
  unfold timeSwitch
  rw [iteratedDeriv_const_sub (Nat.succ_pos n) (1 : ℝ)]
  change iteratedDeriv (n + 1) (fun s => -(scaledCutoff (4 / 3) s)) t = _
  rw [iteratedDeriv_fun_neg, scaledCutoff_iteratedDeriv]

/-- On the physical half-line, all nonzero positive derivatives lie in `[3/8,3/4]`.
@isnad1 id=and.2h2v.s6.b31de609bbc8 from=translated src=- shape=ae8ce1a3 vocab=ee230788
-/
theorem timeSwitch_iteratedDeriv_support_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hs : iteratedDeriv (n + 1) timeSwitch t ≠ 0) :
    3 / 8 ≤ t ∧ t ≤ 3 / 4 := by
  have hcut : iteratedDeriv (n + 1) cutoff ((4 / 3) * t) ≠ 0 := by
    intro hz
    apply hs
    rw [timeSwitch_iteratedDeriv_formula, hz]
    simp
  have hb := cutoff_iteratedDeriv_support n hcut
  change 1 / 2 ≤ |(4 / 3 : ℝ) * t| ∧ |(4 / 3 : ℝ) * t| ≤ 1 at hb
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 / 3) * t)] at hb
  constructor <;> linarith [hb.1, hb.2]

end NavierStokes.SmoothCutoffs
