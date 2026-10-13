/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Assembly
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Grid
public import Tengoku

/-!
# Choosing the layout parameters

For fixed parameters, a good sample exists once the graph is large enough. As the decay
rate `q` increases to `1/√2`, the kernel correlation `2q/(1+q²)` increases to `2√2/3`,
where `√(1-ρ)/√(1+ρ) = 3 - 2√2`; the truncation error `3 (2q²)^R` vanishes as `R` grows.
A fine threshold grid with small deviations then brings the prefix-cut coefficient within
any positive slack of `(3/π)(3 - 2√2)`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

/-- The crossing ratio `√(1-ρ)/√(1+ρ)`. -/
noncomputable def crossRatio (ρ : ℝ) : ℝ :=
  Real.sqrt (1 - ρ) / Real.sqrt (1 + ρ)

/--
@isnad1 id=eq.0h1v.s5.819a1fe97476 from=translated src=- shape=aa4b156b vocab=b331090a
-/
theorem crossBound_eq (ρ : ℝ) : crossBound ρ = 2 / Real.pi * crossRatio ρ := rfl

/--
@isnad1 id=eq.0h0v.s6.a42a8d64d055 from=translated src=- shape=5ff03794 vocab=627c33a4
-/
theorem crossRatio_limit : crossRatio (2 * Real.sqrt 2 / 3) = 3 - 2 * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hge : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hminus : 1 - 2 * Real.sqrt 2 / 3 = (Real.sqrt 2 - 1) ^ 2 / 3 := by
    ring_nf; rw [h2]; ring
  have hplus : 1 + 2 * Real.sqrt 2 / 3 = (Real.sqrt 2 + 1) ^ 2 / 3 := by
    ring_nf; rw [h2]; ring
  unfold crossRatio
  rw [hminus, hplus, Real.sqrt_div' _ (by norm_num), Real.sqrt_div' _ (by norm_num),
    Real.sqrt_sq (by linarith), Real.sqrt_sq (by linarith),
    div_div_div_cancel_right₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']
  rw [div_eq_iff (by linarith)]
  ring_nf
  rw [h2]
  ring

/--
@isnad1 id=continuo.1h1v.s4.f4939c55856f from=translated src=- shape=4ef24b1f vocab=966ba81e
-/
theorem continuousAt_crossRatio {ρ : ℝ} (hρ : -1 < ρ) : ContinuousAt crossRatio ρ := by
  unfold crossRatio
  refine ContinuousAt.div ?_ ?_ (Real.sqrt_pos.mpr (by linarith)).ne'
  · exact (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousAt
  · exact (Real.continuous_sqrt.comp (continuous_const.add continuous_id)).continuousAt

/--
@isnad1 id=continuo.0h0v.s6.391357240604 from=translated src=- shape=c5de756f vocab=1100e3b6
-/
theorem continuous_correlation : Continuous fun q : ℝ => 2 * q / (1 + q ^ 2) :=
  (continuous_const.mul continuous_id).div (continuous_const.add (continuous_pow 2))
    fun q => by positivity

/--
@isnad1 id=eq.0h0v.s7.2c875de5e170 from=translated src=- shape=dbbb0a43 vocab=ed31e169
-/
theorem correlation_limit :
    2 * (Real.sqrt 2 / 2) / (1 + (Real.sqrt 2 / 2) ^ 2) = 2 * Real.sqrt 2 / 3 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [div_pow, h2]
  field_simp
  ring

/--
@isnad1 id=le.0h0v.s4.5fe2ba83e81f from=translated src=- shape=5ccaf027 vocab=1e7d5487
-/
theorem cutwidthCoefficient_ge : 3 / 40 ≤ cutwidthCoefficient := by
  have hsqrt : Real.sqrt 2 < 29 / 20 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  unfold cutwidthCoefficient
  rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
  nlinarith [Real.pi_le_four]

/--
@isnad1 id=lt.0h0v.s3.93cda0b775f6 from=translated src=- shape=ff3a10fc vocab=3adc338e
-/
theorem cutwidthCoefficient_pos : 0 < cutwidthCoefficient :=
  lt_of_lt_of_le (by norm_num) cutwidthCoefficient_ge

/-- The circuit coefficient of the Gaussian ordering coefficient `2c`.
@isnad1 id=eq.0h0v.s6.85229a4cdb93 from=translated src=- shape=753141f4 vocab=216d614a
-/
theorem one_add_inv_two_mul_cutwidthCoefficient :
    1 + 1 / (2 * cutwidthCoefficient) = 1 + Real.pi * (3 + 2 * Real.sqrt 2) / 6 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hne : 3 - 2 * Real.sqrt 2 ≠ 0 := by linarith
  unfold cutwidthCoefficient
  congr 1
  field_simp
  nlinarith [h2]

/-- The Gaussian ordering coefficient is at most `20/61`.
@isnad1 id=le.0h0v.s5.8124cb9b807d from=translated src=- shape=b9c36195 vocab=464f05e0
-/
theorem two_mul_cutwidthCoefficient_le : 2 * cutwidthCoefficient ≤ 20 / 61 := by
  have hsqrt : (141421 : ℝ) / 100000 < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hpi := Real.pi_gt_d4
  unfold cutwidthCoefficient
  have : 2 * (3 / Real.pi * (3 - 2 * Real.sqrt 2)) = 6 * (3 - 2 * Real.sqrt 2) / Real.pi := by
    field_simp
    ring
  rw [this, div_le_div_iff₀ Real.pi_pos (by norm_num)]
  nlinarith

/-- **Decay rate and radius.** Every correlation target below `2√2/3` is met by the
truncated kernel for some decay rate `q < 1/√2` and some radius.
@isnad1 id=ex.1h1v.s7.2407cd86c41e from=translated src=- shape=468aa073 vocab=e7d2045c
-/
theorem exists_decay_radius {ρ₀ : ℝ} (hρ₀g : ρ₀ < 2 * Real.sqrt 2 / 3) :
    ∃ (q : ℝ) (R : ℕ), 0 ≤ q ∧ ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R := by
  set g : ℝ := 2 * Real.sqrt 2 / 3 with hg
  -- A decay rate `q < 1/√2` whose correlation exceeds the target.
  set q₀ : ℝ := Real.sqrt 2 / 2 with hq₀
  have hq₀pos : 0 < q₀ := by positivity
  obtain ⟨δ, hδ, hκ⟩ := Metric.continuousAt_iff.mp continuous_correlation.continuousAt
    ((g - ρ₀) / 2) (by linarith)
  set q := q₀ - min δ q₀ / 2 with hq
  have hminq : 0 < min δ q₀ := lt_min hδ hq₀pos
  have hq0 : 0 ≤ q := by rw [hq]; linarith [min_le_right δ q₀]
  have hqq₀ : q < q₀ := by rw [hq]; linarith
  have hκq : g - (g - ρ₀) / 2 < 2 * q / (1 + q ^ 2) := by
    have hdist : dist q q₀ < δ := by
      rw [Real.dist_eq, hq, abs_of_neg (by linarith)]
      linarith [min_le_left δ q₀]
    have := hκ hdist
    rw [Real.dist_eq, hq₀, correlation_limit, ← hg] at this
    linarith [neg_abs_le (2 * q / (1 + q ^ 2) - g)]
  -- A truncation radius with small boundary error.
  have hdecay : 2 * q ^ 2 < 1 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have : q ^ 2 < q₀ ^ 2 := by gcongr
    rw [hq₀, div_pow, h2] at this
    linarith
  obtain ⟨R, hR⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < (g - ρ₀) / 6) hdecay
  have hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R := by linarith
  exact ⟨q, R, hq0, hρ⟩

/-- **Parameters.** For every positive slack some admissible parameters bring the layout
bound within that slack of `(3/π)(3 - 2√2)`.
@isnad1 id=ex.1h1v.s7.7f78367467fe from=translated src=- shape=8745a9af vocab=51cbc11b
-/
theorem exists_parameters {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ (q : ℝ) (R : ℕ) (ρ₀ T ε : ℝ) (M : ℕ), 0 ≤ q ∧ -1 < ρ₀ ∧
      ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧ 0 < T ∧ 0 < ε ∧ 0 < M ∧
      layoutBound ρ₀ T ε M ≤ cutwidthCoefficient + ξ := by
  set g : ℝ := 2 * Real.sqrt 2 / 3 with hg
  have hsqrt_lt : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hg1 : 0 < g := by positivity
  -- A correlation target `ρ₀ < g` with nearly optimal crossing ratio.
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    (continuousAt_crossRatio (by linarith : -1 < g)) (Real.pi * ξ / 6) (by positivity)
  set ρ₀ := g - min η (1 / 2) / 2 with hρ₀
  have hmin : 0 < min η (1 / 2) := lt_min hη (by norm_num)
  have hρ₀g : ρ₀ < g := by rw [hρ₀]; linarith
  have hρ₀low : -1 < ρ₀ := by
    rw [hρ₀]; linarith [min_le_right η (1 / 2)]
  have hratio : crossRatio ρ₀ ≤ 3 - 2 * Real.sqrt 2 + Real.pi * ξ / 6 := by
    have hdist : dist ρ₀ g < η := by
      rw [Real.dist_eq, hρ₀, abs_of_neg (by linarith)]
      linarith [min_le_left η (1 / 2)]
    have := hcont hdist
    rw [Real.dist_eq, crossRatio_limit] at this
    linarith [le_abs_self (crossRatio ρ₀ - (3 - 2 * Real.sqrt 2))]
  obtain ⟨q, R, hq0, hρ⟩ := exists_decay_radius hρ₀g
  -- The grid and the deviation slack.
  set ε := min (ξ / 16) (1 / 100) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by norm_num)
  set M : ℕ := ⌈120 / ξ⌉₊ + 1 with hM
  have hMpos : 0 < M := Nat.succ_pos _
  have hMR : 120 / ξ ≤ M := by
    rw [hM]; push_cast; linarith [Nat.le_ceil (120 / ξ)]
  refine ⟨q, R, ρ₀, 10, ε, M, hq0, hρ₀low, hρ, by norm_num, hεpos, hMpos, ?_⟩
  have hcoef := cutwidthCoefficient_ge
  have hMpos' : (0 : ℝ) < M := by exact_mod_cast hMpos
  unfold layoutBound
  refine max_le ?_ ?_
  · have : ε ≤ 1 / 100 := min_le_right _ _
    linarith
  · have hεξ : ε ≤ ξ / 16 := min_le_left _ _
    have hcross : 3 / 2 * crossBound ρ₀ ≤ cutwidthCoefficient + ξ / 2 := by
      rw [crossBound_eq, cutwidthCoefficient]
      have : 3 / 2 * (2 / Real.pi * crossRatio ρ₀) = 3 / Real.pi * crossRatio ρ₀ := by ring
      rw [this]
      calc 3 / Real.pi * crossRatio ρ₀ ≤
            3 / Real.pi * (3 - 2 * Real.sqrt 2 + Real.pi * ξ / 6) := by
            gcongr
        _ = 3 / Real.pi * (3 - 2 * Real.sqrt 2) + ξ / 2 := by
            field_simp
            ring
    have hsqrtpi : 2 ≤ Real.sqrt (2 * Real.pi) :=
      (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Real.two_le_pi])
    have hgrid : 3 * (2 * 10 / M) / Real.sqrt (2 * Real.pi) ≤ ξ / 4 := by
      rw [div_le_iff₀ (by positivity)]
      calc 3 * (2 * 10 / (M : ℝ)) = 60 / M := by ring
        _ ≤ ξ / 2 := by
            rw [div_le_iff₀ hMpos']
            have := mul_le_mul_of_nonneg_left hMR hξ.le
            rw [mul_div_cancel₀ _ hξ.ne'] at this
            linarith
        _ ≤ ξ / 4 * Real.sqrt (2 * Real.pi) := by nlinarith
    linarith

end Algebraic.Cutwidth.Gaussian.Internal
