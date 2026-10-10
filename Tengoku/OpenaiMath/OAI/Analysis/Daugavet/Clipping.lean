import Tengoku.OpenaiMath.OAI.Analysis.Daugavet.Model

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe uX uY u_1

namespace ExactModuli

/-- Scalar clipping, equivalently sign(a) * min(|a|,h) when h >= 0. -/
def scalarClip (h a : ℝ) : ℝ := max (-h) (min h a)

lemma scalarClip_bounds {h a : ℝ} (hh : 0 ≤ h) :
    -h ≤ scalarClip h a ∧ scalarClip h a ≤ h := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma abs_scalarClip_le {h a : ℝ} (hh : 0 ≤ h) : |scalarClip h a| ≤ h :=
  abs_le.mpr (scalarClip_bounds hh)

lemma scalarClip_eq_of_mem {h a : ℝ} (ha : -h ≤ a) (hb : a ≤ h) :
    scalarClip h a = a := by
  simp [scalarClip, min_eq_right hb, max_eq_right ha]

lemma abs_sub_scalarClip {h a : ℝ} (hh : 0 ≤ h) :
    |a - scalarClip h a| = |a| - |scalarClip h a| := by
  by_cases ha : a < -h
  · have ha0 : a ≤ 0 := by linarith
    have hc : scalarClip h a = -h := by
      simp [scalarClip, min_eq_right (show a ≤ h by linarith), max_eq_left ha.le]
    rw [hc, abs_of_nonpos ha0, abs_of_nonpos (neg_nonpos.mpr hh),
      abs_of_nonpos (show a - -h ≤ 0 by linarith)]
    ring
  · by_cases hb : h < a
    · have hc : scalarClip h a = h := by
        simp [scalarClip, min_eq_left hb.le, max_eq_right (show -h ≤ h by linarith)]
      rw [hc, abs_of_nonneg (show 0 ≤ a by linarith), abs_of_nonneg hh,
        abs_of_nonneg (show 0 ≤ a - h by linarith)]
    · rw [scalarClip_eq_of_mem (le_of_not_gt ha) (le_of_not_gt hb)]
      simp

lemma abs_scalarClip_eq_min {h a : ℝ} (hh : 0 ≤ h) :
    |scalarClip h a| = min |a| h := by
  by_cases ha : a < -h
  · have hc : scalarClip h a = -h := by
      simp [scalarClip, min_eq_right (show a ≤ h by linarith), max_eq_left ha.le]
    rw [hc, abs_neg, abs_of_nonneg hh, abs_of_nonpos (show a ≤ 0 by linarith)]
    exact (min_eq_right (by linarith)).symm
  · by_cases hb : h < a
    · have hc : scalarClip h a = h := by
        simp [scalarClip, min_eq_left hb.le, max_eq_right (show -h ≤ h by linarith)]
      rw [hc, abs_of_nonneg hh, abs_of_nonneg (show 0 ≤ a by linarith)]
      exact (min_eq_right hb.le).symm
    · rw [scalarClip_eq_of_mem (le_of_not_gt ha) (le_of_not_gt hb)]
      exact (min_eq_left (abs_le.mpr ⟨le_of_not_gt ha, le_of_not_gt hb⟩)).symm

lemma scalarClip_mono (h : ℝ) : Monotone (scalarClip h) := by
  intro a b hab
  exact max_le_max_left _ (min_le_min_left _ hab)

lemma scalarClip_sub_le {h a b : ℝ} (hab : b ≤ a) :
    scalarClip h a - scalarClip h b ≤ a - b := by
  unfold scalarClip
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma abs_scalarClip_sub_le (h a b : ℝ) :
    |scalarClip h a - scalarClip h b| ≤ |a - b| := by
  rcases le_total b a with hab | hab
  · rw [abs_of_nonneg (sub_nonneg.mpr (scalarClip_mono h hab)),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    exact scalarClip_sub_le hab
  · rw [abs_sub_comm, abs_sub_comm a b]
    rw [abs_of_nonneg (sub_nonneg.mpr (scalarClip_mono h hab)),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    exact scalarClip_sub_le hab

lemma scalar_average_abs (a b : ℝ) :
    (|a + b| + |a - b|) / 2 = max |a| |b| := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (add_nonneg ha hb)]
    by_cases h : b ≤ a
    · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_left h]; ring
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h)), max_eq_right (le_of_not_ge h)]
      ring
  · rw [abs_of_nonneg ha, abs_of_nonpos hb,
        abs_of_nonneg (sub_nonneg.mpr (le_trans hb ha))]
    by_cases h : -b ≤ a
    · rw [abs_of_nonneg (by linarith : 0 ≤ a + b), max_eq_left h]; ring
    · rw [abs_of_nonpos (by linarith : a + b ≤ 0), max_eq_right (le_of_not_ge h)]; ring
  · rw [abs_of_nonpos ha, abs_of_nonneg hb,
        abs_of_nonpos (sub_nonpos.mpr (le_trans ha hb))]
    by_cases h : b ≤ -a
    · rw [abs_of_nonpos (by linarith : a + b ≤ 0), max_eq_left h]; ring
    · rw [abs_of_nonneg (by linarith : 0 ≤ a + b), max_eq_right (le_of_not_ge h)]; ring
  · rw [abs_of_nonpos ha, abs_of_nonpos hb, abs_of_nonpos (add_nonpos ha hb)]
    by_cases h : b ≤ a
    · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_right (by linarith : -a ≤ -b)]; ring
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h)),
        max_eq_left (by linarith : -b ≤ -a)]; ring

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Clip at a nonnegative L1 height. Clips are not required to belong to E. -/
def clip (h y : Lp ℝ 1 μ) : Lp ℝ 1 μ := (-h) ⊔ (h ⊓ y)

lemma coeFn_clip (h y : Lp ℝ 1 μ) :
    ⇑(clip h y) =ᵐ[μ] fun ω => scalarClip (h ω) (y ω) := by
  filter_upwards [Lp.coeFn_sup (-h) (h ⊓ y), Lp.coeFn_inf h y,
    Lp.coeFn_neg h] with ω h₁ h₂ h₃
  simp only [clip, h₁, h₂, h₃, Pi.sup_apply, Pi.inf_apply, Pi.neg_apply, scalarClip]

lemma norm_sub_clip (h y : Lp ℝ 1 μ) (hh : 0 ≤ h) :
    ‖y - clip h y‖ = ‖y‖ - ‖clip h y‖ := by
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm y,
    L1.norm_eq_integral_norm (clip h y),
    ← integral_sub (L1.integrable_coeFn y).norm (L1.integrable_coeFn (clip h y)).norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub y (clip h y), coeFn_clip h y,
    (Lp.coeFn_nonneg h).mpr hh] with ω hs hc hpos
  simpa only [hs, hc, Pi.sub_apply, Real.norm_eq_abs] using abs_sub_scalarClip hpos

end ExactModuli

namespace ExactModuli
variable {X : Type uX} {Y : Type uY} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma cofinite_ker [FiniteDimensional ℝ Y] (P : X →L[ℝ] Y) :
    Cofinite P.toLinearMap.ker := by
  refine ⟨P.isClosed_ker, ?_⟩
  exact FiniteDimensional.of_injective
    (LinearMap.quotKerEquivRange P.toLinearMap).toLinearMap
    (LinearMap.quotKerEquivRange P.toLinearMap).injective

/-- The finite norming-functional step of the clipping argument. In L1 the
    functionals can be taken to be signs; Hahn--Banach gives the same estimate. -/
lemma finite_norming_kernel (j : X →L[ℝ] Y) (s : Finset Y) :
    ∃ F : Submodule ℝ X, Cofinite F ∧
      ∀ y ∈ F, ∀ b ∈ s, ‖b‖ ≤ ‖b - j y‖ := by
  classical
  choose φ hφnorm hφval using fun b : s => exists_dual_vector'' ℝ (b : Y)
  let P : X →L[ℝ] (s → ℝ) := ContinuousLinearMap.pi fun b => (φ b).comp j
  refine ⟨P.toLinearMap.ker, cofinite_ker P, ?_⟩
  intro y hy b hb
  have hy' : P y = 0 := hy
  have hzero : φ ⟨b, hb⟩ (j y) = 0 := congrFun hy' ⟨b, hb⟩
  have heq : φ ⟨b, hb⟩ (b - j y) = ‖b‖ := by
    rw [map_sub, hzero, sub_zero, hφval ⟨b, hb⟩]
    rfl
  calc
    ‖b‖ = |φ ⟨b, hb⟩ (b - j y)| := by rw [heq, abs_of_nonneg (norm_nonneg _)]
    _ ≤ ‖φ ⟨b, hb⟩‖ * ‖b - j y‖ := (φ ⟨b, hb⟩).le_opNorm _
    _ ≤ 1 * ‖b - j y‖ := mul_le_mul_of_nonneg_right (hφnorm _) (norm_nonneg _)
    _ = ‖b - j y‖ := one_mul _

end ExactModuli

namespace ExactModuli

/-- The quantitative half-mass estimate, before the net radius tends to zero. -/
lemma half_mass_of_norming {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {b c u : Y} {ε : ℝ}
    (hunit : ‖u‖ = 1) (hres : ‖u - c‖ = ‖u‖ - ‖c‖)
    (hnet : ‖c - b‖ < ε) (hker : ‖b‖ ≤ ‖b - u‖) :
    ‖c‖ < 1 / 2 + ε := by
  have h₁ := norm_sub_norm_le c b
  have h₂ : ‖b - u‖ ≤ ‖b - c‖ + ‖c - u‖ := by
    calc ‖b - u‖ = ‖(b - c) + (c - u)‖ := by congr 1; abel
         _ ≤ ‖b - c‖ + ‖c - u‖ := norm_add_le _ _
  rw [norm_sub_rev b c, norm_sub_rev c u, hres, hunit] at h₂
  linarith

end ExactModuli

namespace ExactModuli
variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω}

lemma measureDistance_threshold_nonempty [IsProbabilityMeasure μ] (f g : Lp ℝ 1 μ) :
    {a : ℝ | 0 < a ∧ μ.real {ω | a < |f ω - g ω|} < a}.Nonempty := by
  refine ⟨2, by norm_num, ?_⟩
  exact lt_of_le_of_lt measureReal_le_one (by norm_num)

lemma measureDistance_nonneg [IsProbabilityMeasure μ] (f g : Lp ℝ 1 μ) :
    0 ≤ measureDistance μ f g := by
  exact le_csInf (measureDistance_threshold_nonempty f g) (fun _ ha => ha.1.le)

lemma tail_lt_of_measureDistance_lt [IsProbabilityMeasure μ] (f g : Lp ℝ 1 μ)
    {ε : ℝ} (h : measureDistance μ f g < ε) :
    μ.real {ω | ε < |f ω - g ω|} < ε := by
  obtain ⟨a, ⟨ha, htail⟩, haε⟩ :=
    (csInf_lt_iff ⟨0, fun _ ha => ha.1.le⟩ (measureDistance_threshold_nonempty f g)).mp h
  have hsub : {ω | ε < |f ω - g ω|} ⊆ {ω | a < |f ω - g ω|} :=
    fun _ hω => lt_trans haε hω
  exact lt_trans (lt_of_le_of_lt (measureReal_mono hsub) htail) haε

lemma scalarClip_diff_le_two {h a b : ℝ} (hh : 0 ≤ h) :
    |scalarClip h a - scalarClip h b| ≤ 2 * h := by
  have hab : |scalarClip h a - scalarClip h b| ≤
      |scalarClip h a| + |scalarClip h b| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (scalarClip h a) (scalarClip h b)
  linarith [abs_scalarClip_le (a := a) hh, abs_scalarClip_le (a := b) hh]

end ExactModuli

namespace ExactModuli

lemma scalar_overlap (a b t : ℝ) (ht : 0 < t) :
    (|a + t * b| + |a - t * b|) / 2 =
      |a| + t * (|b| - |scalarClip (|a| / t) b|) := by
  rw [scalar_average_abs, abs_mul, abs_of_pos ht,
    abs_scalarClip_eq_min (div_nonneg (abs_nonneg _) ht.le)]
  by_cases hb : |b| ≤ |a| / t
  · have hb' : t * |b| ≤ |a| := by simpa [mul_comm] using (le_div_iff₀ ht).mp hb
    rw [min_eq_left hb, max_eq_left hb']
    ring
  · have hb' : |a| ≤ t * |b| := by
      have := (div_lt_iff₀ ht).mp (lt_of_not_ge hb)
      linarith
    rw [min_eq_right (le_of_not_ge hb), max_eq_right hb']
    field_simp
    ring

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω}

def clipHeight (x : Lp ℝ 1 μ) (t : ℝ) : Lp ℝ 1 μ := t⁻¹ • |x|

lemma coeFn_clipHeight (x : Lp ℝ 1 μ) (t : ℝ) :
    ⇑(clipHeight x t) =ᵐ[μ] fun ω => |x ω| / t := by
  filter_upwards [Lp.coeFn_smul t⁻¹ |x|, Lp.coeFn_abs x] with ω h₁ h₂
  simp only [clipHeight, h₁, h₂, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma clipHeight_nonneg (x : Lp ℝ 1 μ) {t : ℝ} (ht : 0 < t) :
    0 ≤ clipHeight x t := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [coeFn_clipHeight x t] with ω hω
  rw [hω]
  exact div_nonneg (abs_nonneg _) ht.le

lemma overlap_identity (x y : Lp ℝ 1 μ) {t : ℝ} (ht : 0 < t) :
    (‖x + t • y‖ + ‖x - t • y‖) / 2 =
      ‖x‖ + t * (‖y‖ - ‖clip (clipHeight x t) y‖) := by
  let c := clip (clipHeight x t) y
  have hx := (L1.integrable_coeFn x).norm
  have hy := (L1.integrable_coeFn y).norm
  have hc := (L1.integrable_coeFn c).norm
  have hplus := (L1.integrable_coeFn (x + t • y)).norm
  have hminus := (L1.integrable_coeFn (x - t • y)).norm
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm (x - t • y),
    L1.norm_eq_integral_norm x, L1.norm_eq_integral_norm y,
    L1.norm_eq_integral_norm (clip (clipHeight x t) y)]
  calc
    ((∫ ω, ‖(x + t • y) ω‖ ∂μ) + (∫ ω, ‖(x - t • y) ω‖ ∂μ)) / 2 =
        ∫ ω, (‖(x + t • y) ω‖ + ‖(x - t • y) ω‖) / 2 ∂μ := by
          rw [integral_div, integral_add hplus hminus]
    _ = ∫ ω, ‖x ω‖ + t * (‖y ω‖ - ‖c ω‖) ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add x (t • y), Lp.coeFn_sub x (t • y),
        Lp.coeFn_smul t y, coeFn_clip (clipHeight x t) y,
        coeFn_clipHeight x t] with ω hp hm hty hclip hh
      simpa only [hp, hm, hty, hclip, hh, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, c] using scalar_overlap (x ω) (y ω) t ht
    _ = (∫ ω, ‖x ω‖ ∂μ) + t * ((∫ ω, ‖y ω‖ ∂μ) - ∫ ω, ‖c ω‖ ∂μ) := by
      have hdiff : Integrable (fun ω => ‖y ω‖ - ‖c ω‖) μ := hy.sub hc
      rw [integral_add hx (hdiff.const_mul t), integral_const_mul, integral_sub hy hc]

end ExactModuli

end

end OAI
