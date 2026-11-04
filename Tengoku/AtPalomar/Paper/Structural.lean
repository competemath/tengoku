module

public import Tengoku.AtPalomar.Paper.Gaussian
public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Gaussian structural argument (Proposition 5.3)

The matched Gaussian identity, exact moments, Cauchy–Schwarz step, and monotonicity
in the nonnegative mean are proved for the actual Gaussian measure. Together
they prove Proposition 5.3 from the stated fixed-point equation. Existence and
uniqueness of that fixed point are separate results.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

noncomputable def matchedGaussianExpectation (s : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ y, f y ∂gaussianReal s s.toNNReal

noncomputable def matchedField (s z : ℝ) : ℝ := s + Real.sqrt s * z

/-- Exact mean of the Gaussian whose mean and variance both equal `s`.-/
@[simp] theorem matchedGaussian_mean (s : ℝ) :
    matchedGaussianExpectation s id = s := by
  simp [matchedGaussianExpectation]

/-- Its second moment includes both variance and squared mean.-/
theorem matchedGaussian_secondMoment {s : ℝ} (hs : 0 ≤ s) :
    matchedGaussianExpectation s (fun y => y ^ 2) = s + s ^ 2 := by
  have hv := variance_eq_sub (memLp_id_gaussianReal (μ := s) (v := s.toNNReal) 2)
  simp only [variance_id_gaussianReal, Real.coe_toNNReal s hs] at hv
  change s = (∫ x, x ^ 2 ∂gaussianReal s s.toNNReal) -
    (∫ x, x ∂gaussianReal s s.toNNReal) ^ 2 at hv
  rw [integral_id_gaussianReal] at hv
  change s = matchedGaussianExpectation s (fun y => y ^ 2) - s ^ 2 at hv
  linarith

/-- `Y = s + sqrt(s) Z` has precisely the matched Gaussian distribution.-/
theorem matchedField_law {s : ℝ} (hs : 0 ≤ s) :
    (gaussianReal 0 1).map (matchedField s) = gaussianReal s s.toNNReal := by
  have he : matchedField s = (fun y : ℝ => y + s) ∘ (fun z : ℝ => Real.sqrt s * z) := by
    ext z
    simp [matchedField, add_comm]
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_add_const]
  simp only [mul_zero, zero_add, mul_one]
  congr 1
  apply NNReal.coe_injective
  simp [Real.sq_sqrt hs, Real.coe_toNNReal s hs]

/-- Relates the distribution-based calculation to the paper's standard-normal expectation.-/
theorem matchedGaussian_eq_standard {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (gaussianReal s s.toNNReal)) :
    matchedGaussianExpectation s f = gaussianExpectation (fun z => f (matchedField s z)) := by
  unfold matchedGaussianExpectation gaussianExpectation
  rw [← matchedField_law hs]
  exact integral_map (by unfold matchedField; fun_prop) (by simpa [matchedField_law hs] using hf)

private theorem one_sub_tanh_eq (y : ℝ) :
    1 - Real.tanh y = Real.exp (-y) / Real.cosh y := by
  rw [Real.tanh_eq_sinh_div_cosh, ← Real.cosh_sub_sinh]
  field_simp

/-- The weighted density in the paper's matched-field identity is even.-/
theorem matchedGaussian_weight_even {s : ℝ} (hs : 0 < s) (y : ℝ) :
    (1 - Real.tanh (-y)) * gaussianPDFReal s s.toNNReal (-y) =
      (1 - Real.tanh y) * gaussianPDFReal s s.toNNReal y := by
  have hf : ∀ x : ℝ, (1 - Real.tanh x) * gaussianPDFReal s s.toNNReal x =
      ((Real.sqrt (2 * Real.pi * s))⁻¹ / Real.cosh x) *
        Real.exp (-x ^ 2 / (2 * s) - s / 2) := by
    intro x
    rw [one_sub_tanh_eq, gaussianPDFReal_def, Real.coe_toNNReal s hs.le]
    calc
      (Real.exp (-x) / Real.cosh x) *
          ((Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-(x - s) ^ 2 / (2 * s))) =
        ((Real.sqrt (2 * Real.pi * s))⁻¹ / Real.cosh x) *
          (Real.exp (-x) * Real.exp (-(x - s) ^ 2 / (2 * s))) := by ring
      _ = ((Real.sqrt (2 * Real.pi * s))⁻¹ / Real.cosh x) *
          Real.exp (-x ^ 2 / (2 * s) - s / 2) := by
        rw [← Real.exp_add]
        congr 2
        field_simp
        ring
  rw [hf, hf]
  simp

private theorem memLp_tanh_gaussian (s : ℝ) :
    MemLp Real.tanh 2 (gaussianReal s s.toNNReal) := by
  apply MemLp.of_bound ?_ 1
  · filter_upwards [] with y
    rw [Real.norm_eq_abs]
    exact abs_le_of_sq_le_sq (by simpa using tanh_sq_le_one y) zero_le_one
  · have he : Real.tanh = (fun y : ℝ => Real.sinh y / Real.cosh y) :=
      funext Real.tanh_eq_sinh_div_cosh
    rw [he]
    exact (Real.continuous_sinh.div Real.continuous_cosh
      (fun y => ne_of_gt (Real.cosh_pos y))).aestronglyMeasurable

/-- Cancellation of the odd weighted Gaussian density.-/
theorem matchedGaussian_cancellation {s : ℝ} (hs : 0 < s) :
    matchedGaussianExpectation s (fun y => y * (1 - Real.tanh y)) = 0 := by
  have hv : s.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hs)
  rw [matchedGaussianExpectation, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  let F : ℝ → ℝ := fun y => gaussianPDFReal s s.toNNReal y * (y * (1 - Real.tanh y))
  change (∫ y, F y) = 0
  have hodd : ∀ y, F (-y) = -F y := by
    intro y
    dsimp [F]
    have he := matchedGaussian_weight_even hs y
    calc
      _ = -y * ((1 - Real.tanh (-y)) * gaussianPDFReal s s.toNNReal (-y)) := by ring
      _ = -y * ((1 - Real.tanh y) * gaussianPDFReal s s.toNNReal y) := by rw [he]
      _ = _ := by ring
  have hi := integral_neg_eq_self F volume
  simp only [hodd, integral_neg] at hi
  linarith

/-- The Gaussian matched-field identity `E[Y tanh Y] = s`.-/
theorem matchedGaussian_tanh_moment {s : ℝ} (hs : 0 < s) :
    matchedGaussianExpectation s (fun y => y * Real.tanh y) = s := by
  have hy : Integrable (fun y : ℝ => y) (gaussianReal s s.toNNReal) :=
    (memLp_id_gaussianReal (μ := s) (v := s.toNNReal) 2).integrable (by norm_num)
  have hyt : Integrable (fun y : ℝ => y * Real.tanh y) (gaussianReal s s.toNNReal) :=
    (memLp_id_gaussianReal' (μ := s) (v := s.toNNReal) 2 (by norm_num)).integrable_mul (memLp_tanh_gaussian s)
  have he := matchedGaussian_cancellation hs
  have hfun : (fun y : ℝ => y * (1 - Real.tanh y)) = (fun y => y - y * Real.tanh y) := by
    ext y
    ring
  rw [hfun, matchedGaussianExpectation, integral_sub hy hyt, integral_id_gaussianReal] at he
  unfold matchedGaussianExpectation
  linarith

/-- Integral Cauchy–Schwarz, proved by integrating a nonnegative square.-/
theorem integral_cauchySchwarz_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (ha : 0 < ∫ x, f x ^ 2 ∂μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  let a := ∫ x, f x ^ 2 ∂μ
  let b := ∫ x, f x * g x ∂μ
  let c := ∫ x, g x ^ 2 ∂μ
  have hfg : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have hi : 0 ≤ ∫ x, (a * g x - b * f x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have he : (∫ x, (a * g x - b * f x) ^ 2 ∂μ) = a * (a * c - b ^ 2) := by
    calc
      _ = ∫ x, (a ^ 2 * g x ^ 2 - (2 * a * b) * (f x * g x)) + b ^ 2 * f x ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = (a ^ 2 * c - (2 * a * b) * b) + b ^ 2 * a := by
        have hsub : Integrable (fun x => a ^ 2 * g x ^ 2 - (2 * a * b) * (f x * g x)) μ :=
          (hg.integrable_sq.const_mul _).sub (hfg.const_mul _)
        rw [integral_add hsub (hf.integrable_sq.const_mul _)]
        have hleft : Integrable (fun x => a ^ 2 * g x ^ 2) μ := hg.integrable_sq.const_mul _
        have hright : Integrable (fun x => (2 * a * b) * (f x * g x)) μ := hfg.const_mul _
        rw [integral_sub hleft hright, integral_const_mul, integral_const_mul, integral_const_mul]
      _ = a * (a * c - b ^ 2) := by ring
  rw [he] at hi
  have hh := (mul_nonneg_iff_of_pos_left ha).mp hi
  dsimp [a, b, c] at hh
  linarith

/-- The actual Cauchy–Schwarz bound for the matched Gaussian field.-/
theorem matchedGaussian_cauchySchwarz {s : ℝ} (hs : 0 < s) :
    s ^ 2 ≤ (s + s ^ 2) * matchedGaussianExpectation s (fun y => Real.tanh y ^ 2) := by
  have hm := matchedGaussian_secondMoment hs.le
  have hc := integral_cauchySchwarz_sq
    (memLp_id_gaussianReal (μ := s) (v := s.toNNReal) 2) (memLp_tanh_gaussian s)
    (by change 0 < matchedGaussianExpectation s (fun y => y ^ 2); rw [hm]; positivity)
  change matchedGaussianExpectation s (fun y => y * Real.tanh y) ^ 2 ≤
    matchedGaussianExpectation s (fun y => y ^ 2) *
      matchedGaussianExpectation s (fun y => Real.tanh y ^ 2) at hc
  rwa [matchedGaussian_tanh_moment hs, hm] at hc

/-- Distribution of the fixed-point Gaussian field.-/
theorem gaussianField_law {β h q : ℝ} (hq : 0 ≤ q) :
    (gaussianReal 0 1).map (gaussianField β h q) = gaussianReal h (β ^ 2 * q).toNNReal := by
  have he : gaussianField β h q =
      (fun y : ℝ => y + h) ∘ (fun z : ℝ => (β * Real.sqrt q) * z) := by
    ext z
    rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_add_const]
  simp only [mul_zero, zero_add, mul_one]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mk, Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) hq)]
  rw [mul_pow, Real.sq_sqrt hq]

/-- The final algebraic contradiction, with the comparison of means made explicit.-/
theorem structural_beta_bound {β q : ℝ} (hq : 0 < q) (hβ : β ≠ 0)
    (hcompare : matchedGaussianExpectation (β ^ 2 * q) (fun y => Real.tanh y ^ 2) ≤ q) :
    β ^ 2 * (1 - q) ≤ 1 := by
  have hs : 0 < β ^ 2 * q := mul_pos (sq_pos_of_ne_zero hβ) hq
  have hc := matchedGaussian_cauchySchwarz hs
  have hb : (β ^ 2 * q) ^ 2 ≤ (β ^ 2 * q + (β ^ 2 * q) ^ 2) * q :=
    hc.trans (mul_le_mul_of_nonneg_left hcompare (by positivity))
  have hm : 0 ≤ (β ^ 2 * q) * q * (1 - β ^ 2 * (1 - q)) := by
    nlinarith [hb]
  have hp : 0 < (β ^ 2 * q) * q := mul_pos hs hq
  have he := (mul_nonneg_iff_of_pos_left hp).mp hm
  linarith

/-- Auxiliary implication isolating the comparison of Gaussian means.-/
theorem structural_field_lt_conditional {β h q : ℝ} (hq : 0 < q)
    (hlarge : 1 < β ^ 2 * (1 - q))
    (hcompare : β ^ 2 * q ≤ h →
      matchedGaussianExpectation (β ^ 2 * q) (fun y => Real.tanh y ^ 2) ≤ q) :
    h < β ^ 2 * q := by
  by_contra hn
  have hβ : β ≠ 0 := by
    intro hb
    norm_num [hb] at hlarge
  have hb := structural_beta_bound hq hβ (hcompare (le_of_not_gt hn))
  linarith

/-- The matched field's first moment, expressed with standard-normal expectation.-/
theorem matchedField_mean {s : ℝ} (hs : 0 ≤ s) :
    gaussianExpectation (matchedField s) = s := by
  change gaussianExpectation (fun z => id (matchedField s z)) = s
  rw [← matchedGaussian_eq_standard hs (f := id) (by fun_prop)]
  exact matchedGaussian_mean s

/-- The matched field's second moment, expressed with standard-normal expectation.-/
theorem matchedField_secondMoment {s : ℝ} (hs : 0 ≤ s) :
    gaussianExpectation (fun z => matchedField s z ^ 2) = s + s ^ 2 := by
  rw [← matchedGaussian_eq_standard hs (f := fun y => y ^ 2) (by fun_prop)]
  exact matchedGaussian_secondMoment hs

end Paper
