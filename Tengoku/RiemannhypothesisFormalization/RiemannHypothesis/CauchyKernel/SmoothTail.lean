/-
Copyright (c) 2025 ...
-/

import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ComplexAnalysis.LogDerivative
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ZeroCounting.SmoothMainTerm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OverflowResidueRH

open Filter Topology

/-- **Positive smooth kernel** — the absolute-value form of the paired
Cauchy kernel's imaginary part. Manifestly nonneg for `y > 0`.-/
noncomputable def positiveSmoothKernel (x y u : ℝ) : ℝ :=
  y * (1 / ((x - u)^2 + y^2) + 1 / ((x + u)^2 + y^2))

/-- **Normalized `smoothTailRationalLowerBoundAbs`** — divide out the
leading `y` factor:
`ρ(T) · ((T − |x|)/((T − |x|)² + y²) + (T + |x|)/((T + |x|)² + y²))`.-/
noncomputable def smoothTailRationalLowerBoundAbsNorm (x y T : ℝ) : ℝ :=
  zeroDensityRho T *
    ((T - |x|) / ((T - |x|) ^ 2 + y ^ 2)
      + (T + |x|) / ((T + |x|) ^ 2 + y ^ 2))

/-- **Helper def**: `tailK_10_12 T` = the slab-local tail-LB coefficient.-/
noncomputable def tailK_10_12 (T : ℝ) : ℝ :=
  (22 / 15 : ℝ) * ((9 / 25 : ℝ) / (2 * Real.pi)) / T

/-- **Helper def**: `tailK10_const := 33 / 4750`.
Equals `(22/15)·(9/25)·(3/19)·(1/12)`.-/
noncomputable def tailK10_const : ℝ := 33 / 4750

/-- **Helper 7 def**: `tailK_12_13 T` = the slab-local tail-LB coefficient.-/
noncomputable def tailK_12_13 (T : ℝ) : ℝ :=
  (22 / 15 : ℝ) *
    (((2 / 5 : ℝ) + (T - 12) / 10) / (2 * Real.pi)) / T

/-- **Helper 8b def**: a safe rational lower bound for `tailK_12_13`.-/
noncomputable def tailK12_const : ℝ := 7 / 1000

/-- **Helper def**: `tailK_13_14 T`.-/
noncomputable def tailK_13_14 (T : ℝ) : ℝ :=
  (22 / 15 : ℝ) * ((1 / 2 : ℝ) / (2 * Real.pi)) / T

/-- **Helper def**: `tailK13_const := 1/120`.-/
noncomputable def tailK13_const : ℝ := 1 / 120

/-- **Helper def**: `tailK_14_19 T`.-/
noncomputable def tailK_14_19 (T : ℝ) : ℝ :=
  (22 / 15 : ℝ) * ((3 / 4 : ℝ) / (2 * Real.pi)) / T

/-- **Helper def**: `tailK14_const := 7/760`.-/
noncomputable def tailK14_const : ℝ := 7 / 760

/-- **Helper def**: `tailK_32_36 T = (22/15)·((8/5)/(2π))/T`.-/
noncomputable def tailK_32_36 (T : ℝ) : ℝ :=
  (22 / 15 : ℝ) * ((8 / 5 : ℝ) / (2 * Real.pi)) / T

/-- **Helper def**: rational tail using `1/(2π) ≥ 7/44`.
Equals `(22/15)·(8/5)·(7/44)/T = 28/(75·T)`.-/
noncomputable def tailK32_rat (T : ℝ) : ℝ :=
  (22 / 15 : ℝ) * (8 / 5 : ℝ) * (7 / 44) / T

/-- **Helper def**: `tailK_36_48 T = (22/15)·((5/3)/(2π))/T`.-/
noncomputable def tailK_36_48 (T : ℝ) : ℝ :=
  (22 / 15 : ℝ) * ((5 / 3 : ℝ) / (2 * Real.pi)) / T

/-- **Helper def**: `tailK_80_140 T`.-/
noncomputable def tailK_80_140 (T : ℝ) : ℝ :=
  (22 / 15 : ℝ) * ((2 : ℝ) / (2 * Real.pi)) / T

/-- **Helper def**: `tailK80_const := 1/300`.-/
noncomputable def tailK80_const : ℝ := 1 / 300

/-- **Smooth uniform LB constant**: `(259/3586)·(5/29) ≈ 0.01246`.-/
noncomputable def smoothLBConst : ℝ := (259 / 3586) * (5 / 29)

/-- ⭐ **PROVED — `tailK32_rat` is anti-monotone in `T`.**-/
lemma tailK32_rat_antitone_T {T₁ T₂ : ℝ}
    (hT₁_pos : 0 < T₁) (h_T_le : T₁ ≤ T₂) :
    tailK32_rat T₂ ≤ tailK32_rat T₁ := by
  unfold tailK32_rat
  have hT₂_pos : 0 < T₂ := by linarith
  have hinv : 1 / T₂ ≤ 1 / T₁ := one_div_le_one_div_of_le hT₁_pos h_T_le
  have h_pos_factor : (0 : ℝ) ≤ (22 / 15) * (8 / 5) * (7 / 44) := by norm_num
  have h_form₁ : (22 / 15 : ℝ) * (8/5) * (7/44) / T₁
                  = (22 / 15) * (8/5) * (7/44) * (1/T₁) := by ring
  have h_form₂ : (22 / 15 : ℝ) * (8/5) * (7/44) / T₂
                  = (22 / 15) * (8/5) * (7/44) * (1/T₂) := by ring
  rw [h_form₁, h_form₂]
  exact mul_le_mul_of_nonneg_left hinv h_pos_factor

/-- ⭐ **PROVED — `tailK32_rat T ≤ tailK_32_36 T` on `[32, 36]`.**-/
lemma tailK32_rat_le_tailK_32_36
    {T : ℝ} (hT32 : 32 ≤ T) (_hT36 : T ≤ 36) :
    tailK32_rat T ≤ tailK_32_36 T := by
  unfold tailK32_rat tailK_32_36
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have hT_pos : 0 < T := by linarith
  have h_pi_inv : (7 / 44 : ℝ) ≤ 1 / (2 * Real.pi) :=
    one_div_two_pi_ge_seven_fortyfour
  have h_factor_nn : (0 : ℝ) ≤ (22 / 15 : ℝ) * (8 / 5) := by norm_num
  have h_step1 :
      (22 / 15 : ℝ) * (8 / 5) * (7 / 44)
        ≤ (22 / 15 : ℝ) * (8 / 5) * (1 / (2 * Real.pi)) :=
    mul_le_mul_of_nonneg_left h_pi_inv h_factor_nn
  have h_form_eq :
      (22 / 15 : ℝ) * ((8 / 5 : ℝ) / (2 * Real.pi)) / T
        = (22 / 15 : ℝ) * (8 / 5) * (1 / (2 * Real.pi)) / T := by ring
  rw [h_form_eq]
  apply div_le_div_of_nonneg_right h_step1 (le_of_lt hT_pos)

/-- ⭐ **PROVED — `tailK_10_12 T ≥ 33/4750`** on `[10, 12]`.
Chain: `tailK = (22/15)·(9/25)·(1/(2π))·(1/T)` with `1/(2π) ≥ 3/19`
and `1/T ≥ 1/12`.-/
lemma tailK_10_12_ge_const
    {T : ℝ} (hT10 : 10 ≤ T) (hT12 : T ≤ 12) :
    tailK10_const ≤ tailK_10_12 T := by
  unfold tailK10_const tailK_10_12
  have hT_pos : 0 < T := by linarith
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_2pi_inv : (3 / 19 : ℝ) ≤ 1 / (2 * Real.pi) :=
    one_div_two_pi_ge_three_nineteenths
  have h_inv_T : (1 / 12 : ℝ) ≤ 1 / T := one_div_le_one_div_of_le hT_pos hT12
  have h_form_eq : (22 / 15 : ℝ) *
      ((9 / 25 : ℝ) / (2 * Real.pi)) / T
      = (22 / 15) * (9 / 25) * (1 / (2 * Real.pi)) * (1/T) := by ring
  rw [h_form_eq]
  have h_22_15_9_25_nn : (0:ℝ) ≤ (22 / 15) * (9 / 25 : ℝ) := by positivity
  have h_22_15_9_25_2pi_nn : (0:ℝ) ≤ (22 / 15) * (9 / 25 : ℝ) * (1 / (2 * Real.pi)) := by
    positivity
  have h2 : (22 / 15 : ℝ) * (9 / 25) * (3/19)
          ≤ (22 / 15) * (9 / 25) * (1/(2*Real.pi)) := by
    apply mul_le_mul_of_nonneg_left h_2pi_inv h_22_15_9_25_nn
  have h3 : (22 / 15 : ℝ) * (9 / 25) * (1/(2*Real.pi)) * (1/12)
          ≤ (22 / 15) * (9 / 25) * (1/(2*Real.pi)) * (1/T) := by
    apply mul_le_mul_of_nonneg_left h_inv_T h_22_15_9_25_2pi_nn
  have h_C_le_A :
      (22 / 15 : ℝ) * (9 / 25) * (3/19) * (1/12)
        ≤ (22 / 15) * (9 / 25) * (1/(2*Real.pi)) * (1/12) := by
    apply mul_le_mul_of_nonneg_right h2 (by norm_num)
  have h_const_eq : (22 / 15 : ℝ) * (9 / 25) * (3/19) * (1/12) = 33/4750 := by norm_num
  linarith [h3, h_C_le_A, h_const_eq]

/-- ⭐ **PROVED — Helper 8b: `tailK_12_13 T ≥ 7/1000` on `[12, 13]`.**
Chain: `tailK = (22/15)·((affine LB)/(2π))/T`. With affine LB ≥ 2/5,
`1/(2π) ≥ 3/19`, and `1/T ≥ 1/13`:
  tailK ≥ (22/15)·(2/5)·(3/19)·(1/13) = 132/18525 > 7/1000.-/
lemma tailK_12_13_ge_const
    {T : ℝ} (hT12 : 12 ≤ T) (hT13 : T ≤ 13) :
    tailK12_const ≤ tailK_12_13 T := by
  unfold tailK12_const tailK_12_13
  have hT_pos : 0 < T := by linarith
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_aff_ge : (2 / 5 : ℝ) ≤ (2 / 5 : ℝ) + (T - 12) / 10 := by linarith
  have h_aff_nn : (0 : ℝ) ≤ (2 / 5 : ℝ) + (T - 12) / 10 := by linarith
  have h_2pi_inv : (3 / 19 : ℝ) ≤ 1 / (2 * Real.pi) :=
    one_div_two_pi_ge_three_nineteenths
  have h_T_le_13 : T ≤ 13 := hT13
  have h_inv_T : (1 / 13 : ℝ) ≤ 1 / T := one_div_le_one_div_of_le hT_pos h_T_le_13
  -- chain:  (22/15) · ((2/5)·(3/19))/13 ≤ (22/15)·(affine LB)·(1/(2π))/T  ≤  tailK_12_13 T
  -- = 132/(18525). Want ≥ 7/1000.
  have h_2pi_inv_nn : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have h_T_inv_nn : (0 : ℝ) ≤ 1 / T := by positivity
  -- Show: (22/15) · (affine LB / (2π)) / T = (22/15) · (affine LB) · (1/(2π)) · (1/T)
  have h_form_eq : (22 / 15 : ℝ) *
      (((2 / 5 : ℝ) + (T - 12) / 10) / (2 * Real.pi)) / T
      = (22 / 15) * ((2/5 : ℝ) + (T - 12)/10) * (1 / (2 * Real.pi)) * (1/T) := by
    ring
  rw [h_form_eq]
  -- Bound by the four nonneg multiplicands
  have h_22_15_nn : (0:ℝ) ≤ 22 / 15 := by norm_num
  have h_aff_part_nn : (0:ℝ) ≤ (22 / 15) * ((2/5 : ℝ) + (T - 12)/10) := by
    apply mul_nonneg h_22_15_nn h_aff_nn
  have h1 : (22 / 15 : ℝ) * (2/5) ≤ (22 / 15) * ((2/5 : ℝ) + (T - 12)/10) := by
    apply mul_le_mul_of_nonneg_left h_aff_ge h_22_15_nn
  have h2 : (22 / 15 : ℝ) * ((2/5 : ℝ) + (T - 12)/10) * (3/19)
          ≤ (22 / 15) * ((2/5 : ℝ) + (T - 12)/10) * (1/(2*Real.pi)) := by
    apply mul_le_mul_of_nonneg_left h_2pi_inv h_aff_part_nn
  -- Combine into nlinarith-style
  nlinarith [h1, h2, h_inv_T, h_2pi_inv, h_22_15_nn, h_aff_ge, h_aff_nn,
             mul_pos hT_pos hT_pos]

/-- ⭐ **PROVED — `tailK_13_14 T ≥ 1/120`.**
Chain: `(22/15)·(1/2)·(7/44)·(1/14) = 1/120`.-/
lemma tailK_13_14_ge_const
    {T : ℝ} (hT13 : 13 ≤ T) (hT14 : T ≤ 14) :
    tailK13_const ≤ tailK_13_14 T := by
  unfold tailK13_const tailK_13_14
  have hT_pos : 0 < T := by linarith
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_2pi_inv : (7 / 44 : ℝ) ≤ 1 / (2 * Real.pi) :=
    one_div_two_pi_ge_seven_fortyfour
  have h_inv_T : (1 / 14 : ℝ) ≤ 1 / T := one_div_le_one_div_of_le hT_pos hT14
  have h_form_eq : (22 / 15 : ℝ) *
      ((1 / 2 : ℝ) / (2 * Real.pi)) / T
      = (22 / 15) * (1 / 2) * (1 / (2 * Real.pi)) * (1/T) := by ring
  rw [h_form_eq]
  have h_22_15_12_nn : (0:ℝ) ≤ (22 / 15) * (1 / 2 : ℝ) := by positivity
  have h_22_15_12_2pi_nn : (0:ℝ) ≤ (22 / 15) * (1 / 2 : ℝ) * (1 / (2 * Real.pi)) := by
    positivity
  have h2 : (22 / 15 : ℝ) * (1 / 2) * (7/44)
          ≤ (22 / 15) * (1 / 2) * (1/(2*Real.pi)) := by
    apply mul_le_mul_of_nonneg_left h_2pi_inv h_22_15_12_nn
  have h3 : (22 / 15 : ℝ) * (1 / 2) * (1/(2*Real.pi)) * (1/14)
          ≤ (22 / 15) * (1 / 2) * (1/(2*Real.pi)) * (1/T) := by
    apply mul_le_mul_of_nonneg_left h_inv_T h_22_15_12_2pi_nn
  have h_C_le_A :
      (22 / 15 : ℝ) * (1 / 2) * (7/44) * (1/14)
        ≤ (22 / 15) * (1 / 2) * (1/(2*Real.pi)) * (1/14) := by
    apply mul_le_mul_of_nonneg_right h2 (by norm_num)
  have h_const_eq : (22 / 15 : ℝ) * (1 / 2) * (7/44) * (1/14) = 1/120 := by norm_num
  linarith [h3, h_C_le_A, h_const_eq]

/-- ⭐ **PROVED — `tailK_14_19 T ≥ 7/760`.**
Chain: `(22/15)·(3/4)·(7/44)·(1/19) = 7/760`.-/
lemma tailK_14_19_ge_const
    {T : ℝ} (hT14 : 14 ≤ T) (hT19 : T ≤ 19) :
    tailK14_const ≤ tailK_14_19 T := by
  unfold tailK14_const tailK_14_19
  have hT_pos : 0 < T := by linarith
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_2pi_inv : (7 / 44 : ℝ) ≤ 1 / (2 * Real.pi) :=
    one_div_two_pi_ge_seven_fortyfour
  have h_inv_T : (1 / 19 : ℝ) ≤ 1 / T := one_div_le_one_div_of_le hT_pos hT19
  have h_form_eq : (22 / 15 : ℝ) *
      ((3 / 4 : ℝ) / (2 * Real.pi)) / T
      = (22 / 15) * (3 / 4) * (1 / (2 * Real.pi)) * (1/T) := by ring
  rw [h_form_eq]
  have h_22_15_34_nn : (0:ℝ) ≤ (22 / 15) * (3 / 4 : ℝ) := by positivity
  have h_22_15_34_2pi_nn : (0:ℝ) ≤ (22 / 15) * (3 / 4 : ℝ) * (1 / (2 * Real.pi)) := by
    positivity
  have h2 : (22 / 15 : ℝ) * (3 / 4) * (7/44)
          ≤ (22 / 15) * (3 / 4) * (1/(2*Real.pi)) := by
    apply mul_le_mul_of_nonneg_left h_2pi_inv h_22_15_34_nn
  have h3 : (22 / 15 : ℝ) * (3 / 4) * (1/(2*Real.pi)) * (1/19)
          ≤ (22 / 15) * (3 / 4) * (1/(2*Real.pi)) * (1/T) := by
    apply mul_le_mul_of_nonneg_left h_inv_T h_22_15_34_2pi_nn
  have h_C_le_A :
      (22 / 15 : ℝ) * (3 / 4) * (7/44) * (1/19)
        ≤ (22 / 15) * (3 / 4) * (1/(2*Real.pi)) * (1/19) := by
    apply mul_le_mul_of_nonneg_right h2 (by norm_num)
  have h_const_eq : (22 / 15 : ℝ) * (3 / 4) * (7/44) * (1/19) = 7/760 := by norm_num
  linarith [h3, h_C_le_A, h_const_eq]

/-- `7/(18·B) ≤ tailK_36_48 T` for `T ≤ B`. Chain: `(22/15)·(5/3)·(7/44) = 7/18`.-/
lemma tailK_36_48_ge_const
    {T B : ℝ} (hTpos : 0 < T) (hTB : T ≤ B) :
    (7 / (18 * B) : ℝ) ≤ tailK_36_48 T := by
  unfold tailK_36_48
  have hBpos : 0 < B := by linarith
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have h_2pi_inv : (7 / 44 : ℝ) ≤ 1 / (2 * Real.pi) :=
    one_div_two_pi_ge_seven_fortyfour
  have h_inv_T : (1 / B : ℝ) ≤ 1 / T :=
    one_div_le_one_div_of_le hTpos hTB
  have h_form :
      (22 / 15 : ℝ) * ((5 / 3 : ℝ) / (2 * Real.pi)) / T
        = (22 / 15 : ℝ) * (5 / 3) * (1 / (2 * Real.pi)) * (1 / T) := by ring
  rw [h_form]
  have hA_nn : (0 : ℝ) ≤ (22 / 15) * (5 / 3) := by positivity
  have hA_2pi_nn :
      (0 : ℝ) ≤ (22 / 15 : ℝ) * (5 / 3) * (1 / (2 * Real.pi)) := by positivity
  have h_inv_B_nn : (0 : ℝ) ≤ 1 / B := by positivity
  have h2 :
      (22 / 15 : ℝ) * (5 / 3) * (7 / 44)
        ≤ (22 / 15 : ℝ) * (5 / 3) * (1 / (2 * Real.pi)) :=
    mul_le_mul_of_nonneg_left h_2pi_inv hA_nn
  have h3 :
      (22 / 15 : ℝ) * (5 / 3) * (1 / (2 * Real.pi)) * (1 / B)
        ≤ (22 / 15 : ℝ) * (5 / 3) * (1 / (2 * Real.pi)) * (1 / T) :=
    mul_le_mul_of_nonneg_left h_inv_T hA_2pi_nn
  have h4 :
      (22 / 15 : ℝ) * (5 / 3) * (7 / 44) * (1 / B)
        ≤ (22 / 15 : ℝ) * (5 / 3) * (1 / (2 * Real.pi)) * (1 / B) :=
    mul_le_mul_of_nonneg_right h2 h_inv_B_nn
  have h_const :
      (22 / 15 : ℝ) * (5 / 3) * (7 / 44) * (1 / B) = 7 / (18 * B) := by
    field_simp
    ring
  linarith

/-- ⭐ **PROVED — `tailK_80_140 T ≥ 1/300`.**
Chain: `(22/15)·2·(7/44)·(1/140) = 1/300`.-/
lemma tailK_80_140_ge_const
    {T : ℝ} (_hT80 : 80 ≤ T) (hT140 : T ≤ 140) :
    tailK80_const ≤ tailK_80_140 T := by
  unfold tailK80_const tailK_80_140
  have hT_pos : 0 < T := by linarith
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_2pi_inv : (7 / 44 : ℝ) ≤ 1 / (2 * Real.pi) :=
    one_div_two_pi_ge_seven_fortyfour
  have h_inv_T : (1 / 140 : ℝ) ≤ 1 / T := one_div_le_one_div_of_le hT_pos hT140
  have h_form_eq : (22 / 15 : ℝ) *
      ((2 : ℝ) / (2 * Real.pi)) / T
      = (22 / 15) * (2 : ℝ) * (1 / (2 * Real.pi)) * (1/T) := by ring
  rw [h_form_eq]
  have h_22_15_2_nn : (0:ℝ) ≤ (22 / 15) * (2 : ℝ) := by positivity
  have h_22_15_2_2pi_nn : (0:ℝ) ≤ (22 / 15) * (2 : ℝ) * (1 / (2 * Real.pi)) := by
    positivity
  have h2 : (22 / 15 : ℝ) * (2 : ℝ) * (7/44)
          ≤ (22 / 15) * (2 : ℝ) * (1/(2*Real.pi)) := by
    apply mul_le_mul_of_nonneg_left h_2pi_inv h_22_15_2_nn
  have h3 : (22 / 15 : ℝ) * (2 : ℝ) * (1/(2*Real.pi)) * (1/140)
          ≤ (22 / 15) * (2 : ℝ) * (1/(2*Real.pi)) * (1/T) := by
    apply mul_le_mul_of_nonneg_left h_inv_T h_22_15_2_2pi_nn
  have h_C_le_A :
      (22 / 15 : ℝ) * (2 : ℝ) * (7/44) * (1/140)
        ≤ (22 / 15) * (2 : ℝ) * (1/(2*Real.pi)) * (1/140) := by
    apply mul_le_mul_of_nonneg_right h2 (by norm_num)
  have h_const_eq : (22 / 15 : ℝ) * (2 : ℝ) * (7/44) * (1/140) = 1/300 := by norm_num
  linarith [h3, h_C_le_A, h_const_eq]

/-- ⭐ **PROVED — Generic tail bound `tailK_80_140 T ≥ 7/(15·B)`** for
`T ≤ B`. Reused for each `[48, 80]` subband by setting `B` to the
subband upper endpoint.-/
lemma tailK_80_140_ge_seven_fifteen_div
    {T B : ℝ} (hT_pos : 0 < T) (hB_pos : 0 < B) (hT_le : T ≤ B) :
    (7 / (15 * B) : ℝ) ≤ tailK_80_140 T := by
  unfold tailK_80_140
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_2pi_inv : (7 / 44 : ℝ) ≤ 1 / (2 * Real.pi) :=
    one_div_two_pi_ge_seven_fortyfour
  have h_inv_T : (1 / B : ℝ) ≤ 1 / T := one_div_le_one_div_of_le hT_pos hT_le
  have h_form_eq : (22 / 15 : ℝ) *
      ((2 : ℝ) / (2 * Real.pi)) / T
      = (22 / 15) * (2 : ℝ) * (1 / (2 * Real.pi)) * (1/T) := by ring
  rw [h_form_eq]
  have h_22_15_2_nn : (0:ℝ) ≤ (22 / 15) * (2 : ℝ) := by positivity
  have h_22_15_2_2pi_nn : (0:ℝ) ≤ (22 / 15) * (2 : ℝ) * (1 / (2 * Real.pi)) := by
    positivity
  have h2 : (22 / 15 : ℝ) * (2 : ℝ) * (7/44)
          ≤ (22 / 15) * (2 : ℝ) * (1/(2*Real.pi)) := by
    apply mul_le_mul_of_nonneg_left h_2pi_inv h_22_15_2_nn
  have h3 : (22 / 15 : ℝ) * (2 : ℝ) * (1/(2*Real.pi)) * (1/B)
          ≤ (22 / 15) * (2 : ℝ) * (1/(2*Real.pi)) * (1/T) := by
    apply mul_le_mul_of_nonneg_left h_inv_T h_22_15_2_2pi_nn
  have h_inv_B_nn : (0 : ℝ) ≤ 1/B := le_of_lt (one_div_pos.mpr hB_pos)
  have h_C_le_A :
      (22 / 15 : ℝ) * (2 : ℝ) * (7/44) * (1/B)
        ≤ (22 / 15) * (2 : ℝ) * (1/(2*Real.pi)) * (1/B) := by
    apply mul_le_mul_of_nonneg_right h2 h_inv_B_nn
  have hB_ne : B ≠ 0 := ne_of_gt hB_pos
  have h_const_eq : (22 / 15 : ℝ) * (2 : ℝ) * (7/44) * (1/B) = 7/(15*B) := by
    field_simp
    ring
  linarith [h3, h_C_le_A, h_const_eq]

end OverflowResidueRH
