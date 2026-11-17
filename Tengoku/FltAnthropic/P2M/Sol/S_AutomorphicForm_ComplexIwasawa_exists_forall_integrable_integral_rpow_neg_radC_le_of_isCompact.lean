import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ComplexIwasawa
import Tengoku.Seed.Analysis.Fourier.FourierTransformDeriv
import Tengoku.Seed.Topology.Compactness.Compact
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact

set_option autoImplicit false

open MeasureTheory AutomorphicForm.ComplexIwasawa
open scoped ContDiff

noncomputable section

namespace B2bCL2

open ComplexConjugate
open scoped Nat

variable {g : Matrix (Fin 2) (Fin 2) ℂ}

def botNormSqC (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Complex.normSq (g 1 0) + Complex.normSq (g 1 1)

def centerC (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  -(conj (g 1 0) * g 0 0 + conj (g 1 1) * g 0 1) / (botNormSqC g : ℂ)

/--
@isnad1 id=eq.0h2v.s6.5b12cbe34976 from=translated src=- shape=0f43f2be vocab=b92c20bb
-/
theorem radC_sq (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    radC g z ^ 2 = Complex.normSq (botP g z) + Complex.normSq (botQ g z) := by
  rw [radC, Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]

/--
@isnad1 id=lt.1h1v.s5.f97db99d8b77 from=translated src=- shape=21445356 vocab=4af339e2
-/
theorem botNormSqC_pos (hg : g.det ≠ 0) : 0 < botNormSqC g := by
  rw [botNormSqC]
  rcases (add_nonneg (Complex.normSq_nonneg (g 1 0)) (Complex.normSq_nonneg (g 1 1))).lt_or_eq
    with h | h
  · exact h
  · exfalso
    have hc : Complex.normSq (g 1 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (g 1 0), Complex.normSq_nonneg (g 1 1)]
    have hd : Complex.normSq (g 1 1) = 0 := by
      nlinarith [Complex.normSq_nonneg (g 1 0), Complex.normSq_nonneg (g 1 1)]
    apply hg
    rw [Matrix.det_fin_two, Complex.normSq_eq_zero.1 hc, Complex.normSq_eq_zero.1 hd,
      mul_zero, mul_zero, sub_zero]

/--
@isnad1 id=eq.1h2v.s7.c8073b09b79f from=translated src=- shape=28697d87 vocab=7374e062
-/
theorem radC_sq_eq (hg : g.det ≠ 0) (z : ℂ) :
    radC g z ^ 2 = botNormSqC g * Complex.normSq (z - centerC g)
      + Complex.normSq g.det / botNormSqC g := by
  have hA : botNormSqC g ≠ 0 := (botNormSqC_pos hg).ne'
  have hAc : (botNormSqC g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hA
  have hz : z - centerC g = ((botNormSqC g : ℂ) * z + ((starRingEnd ℂ) (g 1 0) * g 0 0
      + (starRingEnd ℂ) (g 1 1) * g 0 1)) / (botNormSqC g : ℂ) := by
    rw [centerC]
    field_simp
    try ring
  rw [radC_sq, hz, Complex.normSq_div, Complex.normSq_ofReal, Matrix.det_fin_two]
  field_simp
  simp only [botP, botQ, botNormSqC, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/--
@isnad1 id=lt.1h2v.s5.72f1e2163854 from=translated src=- shape=606d29bf vocab=6aaedfbb
-/
theorem radC_pos (hg : g.det ≠ 0) (z : ℂ) : 0 < radC g z := by
  rw [radC]
  apply Real.sqrt_pos.2
  rcases (add_nonneg (Complex.normSq_nonneg (botP g z)) (Complex.normSq_nonneg (botQ g z))).lt_or_eq
    with h | h
  · exact h
  · exfalso
    have hP : Complex.normSq (botP g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (botP g z), Complex.normSq_nonneg (botQ g z)]
    have hQ : Complex.normSq (botQ g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (botP g z), Complex.normSq_nonneg (botQ g z)]
    have hP0 := Complex.normSq_eq_zero.1 hP
    have hQ0 := Complex.normSq_eq_zero.1 hQ
    rw [botP] at hP0
    rw [botQ] at hQ0
    apply hg
    rw [Matrix.det_fin_two]
    have ha : g 0 0 = -(z * g 1 0) := by linear_combination hP0
    have hb : g 0 1 = -(z * g 1 1) := by linear_combination hQ0
    rw [ha, hb]
    ring

/--
@isnad1 id=contdiff.1h1v.s6.cf108a53c155 from=translated src=- shape=ea1704a6 vocab=13fbda81
-/
theorem contDiff_radC (hg : g.det ≠ 0) : ContDiff ℝ ∞ (radC g) := by
  have hnormSq : ContDiff ℝ ∞ Complex.normSq := by
    have h : (Complex.normSq : ℂ → ℝ) = fun z => z.re * z.re + z.im * z.im := by
      funext w
      exact Complex.normSq_apply w
    rw [h]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hP : ContDiff ℝ ∞ (botP g) := by
    unfold botP
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hQ : ContDiff ℝ ∞ (botQ g) := by
    unfold botQ
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hinner : ContDiff ℝ ∞ (fun z => Complex.normSq (botP g z) + Complex.normSq (botQ g z)) :=
    (hnormSq.comp hP).add (hnormSq.comp hQ)
  rw [contDiff_iff_contDiffAt]
  intro z
  have hpos : Complex.normSq (botP g z) + Complex.normSq (botQ g z) ≠ 0 := by
    rw [← radC_sq g z]
    exact (pow_pos (radC_pos hg z) 2).ne'
  have h := (Real.contDiffAt_sqrt hpos).comp z hinner.contDiffAt
  simp [radC, Function.comp_def] at h
  exact h

/--
@isnad1 id=continuo.0h0v.s6.36bc1ea08d59 from=translated src=- shape=9907cdae vocab=64843a49
-/
theorem continuous_botNormSqC : Continuous fun g : Matrix (Fin 2) (Fin 2) ℂ => botNormSqC g := by
  unfold botNormSqC
  exact (Complex.continuous_normSq.comp (continuous_id.matrix_elem 1 0)).add
    (Complex.continuous_normSq.comp (continuous_id.matrix_elem 1 1))

/--
@isnad1 id=continuo.0h0v.s6.b2af40c02acc from=translated src=- shape=62ec8e45 vocab=a134058e
-/
theorem continuous_detC : Continuous fun g : Matrix (Fin 2) (Fin 2) ℂ => g.det := by
  have : (fun g : Matrix (Fin 2) (Fin 2) ℂ => g.det) = fun g => g 0 0 * g 1 1 - g 0 1 * g 1 0 :=
    funext fun g => Matrix.det_fin_two g
  rw [this]; fun_prop

/--
@isnad1 id=ex.3h3v.s8.60145d43e122 from=translated src=- shape=039984ed vocab=590af743
-/
theorem main (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (κ₀ κ₁ : ℝ) (hκ₀ : 2 < κ₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ g ∈ 𝒢, ∀ κ : ℝ, κ₀ ≤ κ → κ ≤ κ₁ →
      Integrable (fun z : ℂ => radC g z ^ (-κ)) ∧ ∫ z : ℂ, radC g z ^ (-κ) ≤ M := by

  obtain ⟨A₀, hA₀⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => botNormSqC g)
    continuous_botNormSqC.continuousOn
  obtain ⟨cA, hcA⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => (botNormSqC g)⁻¹)
    ((continuous_botNormSqC.continuousOn).inv₀ fun g hg => (botNormSqC_pos (hdet g hg)).ne')
  obtain ⟨cD, hcD⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => ‖g.det‖⁻¹)
    (continuous_detC.continuousOn.norm.inv₀ fun g hg => (norm_pos_iff.2 (hdet g hg)).ne')
  set A₁ : ℝ := max 1 A₀ with hA₁def
  set a : ℝ := max 1 cA with hadef
  set d : ℝ := max 1 cD with hddef
  have hA₁1 : 1 ≤ A₁ := le_max_left _ _
  have ha1 : 1 ≤ a := le_max_left _ _
  have hd1 : 1 ≤ d := le_max_left _ _
  set μ₀ : ℝ := min a⁻¹ ((d ^ 2)⁻¹ * A₁⁻¹) with hμ₀def
  have hμ₀ : 0 < μ₀ := by positivity
  have hμ₀1 : μ₀ ≤ 1 := (min_le_left _ _).trans (inv_le_one_of_one_le₀ ha1)

  set h : ℂ → ℝ := fun z => ((1 : ℝ) + ‖z‖ ^ 2) ^ (-κ₀ / 2) with hhdef
  have hfinr : ((Module.finrank ℝ ℂ : ℕ) : ℝ) < κ₀ := by
    rw [Complex.finrank_real_complex]; exact_mod_cast hκ₀
  have hh_int : Integrable h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) hfinr
  have hh_nonneg : ∀ z, 0 ≤ h z := fun z => Real.rpow_nonneg (by positivity) _
  set B : ℝ := μ₀⁻¹ ^ (κ₁ / 2) with hBdef
  have hB : 0 < B := Real.rpow_pos_of_pos (inv_pos.2 hμ₀) _
  have hIh : 0 ≤ ∫ z, h z := integral_nonneg hh_nonneg
  refine ⟨B * (∫ z, h z) + 1, by positivity, fun g hg κ hκ hκ1 => ?_⟩
  have hg' : g.det ≠ 0 := hdet g hg
  have hApos := botNormSqC_pos hg'
  have hdet0 : 0 < ‖g.det‖ := norm_pos_iff.2 hg'
  have h1 : (botNormSqC g)⁻¹ ≤ a := by
    have := hcA g hg; rw [norm_inv, Real.norm_of_nonneg hApos.le] at this
    exact this.trans (le_max_right _ _)
  have h2 : ‖g.det‖⁻¹ ≤ d := by
    have := hcD g hg; rw [norm_inv, norm_norm] at this
    exact this.trans (le_max_right _ _)
  have hAup : botNormSqC g ≤ A₁ := by
    have := hA₀ g hg; rw [Real.norm_of_nonneg hApos.le] at this
    exact this.trans (le_max_right _ _)
  have hb1 : a⁻¹ ≤ botNormSqC g := by
    rw [inv_le_comm₀ (by positivity) hApos]; exact h1
  have hb2 : (d ^ 2)⁻¹ * A₁⁻¹ ≤ Complex.normSq g.det / botNormSqC g := by
    rw [Complex.normSq_eq_norm_sq, div_eq_mul_inv]
    refine mul_le_mul ?_ ((inv_le_inv₀ (by positivity) hApos).mpr hAup) (by positivity) (sq_nonneg _)
    rw [← inv_pow]
    exact pow_le_pow_left₀ (by positivity) ((inv_le_comm₀ (by positivity) hdet0).mpr h2) 2
  have hμA : μ₀ ≤ botNormSqC g := (min_le_left _ _).trans hb1
  have hμM : μ₀ ≤ Complex.normSq g.det / botNormSqC g := (min_le_right _ _).trans hb2

  have hcmp : ∀ z : ℂ, radC g z ^ (-κ) ≤ B * h (z - centerC g) := by
    intro z
    have hrad0 : 0 < radC g z := radC_pos hg' z
    have hκ0 : 0 < κ := by linarith
    have hW : (1:ℝ) ≤ 1 + ‖z - centerC g‖ ^ 2 := by nlinarith [sq_nonneg ‖z - centerC g‖]
    have hlb : μ₀ * (1 + ‖z - centerC g‖ ^ 2) ≤ radC g z ^ 2 := by
      rw [radC_sq_eq hg' z, Complex.normSq_eq_norm_sq]
      nlinarith [mul_le_mul_of_nonneg_right hμA (sq_nonneg ‖z - centerC g‖)]
    have hMn : 0 < μ₀ * (1 + ‖z - centerC g‖ ^ 2) := mul_pos hμ₀ (by positivity)
    calc radC g z ^ (-κ) = (radC g z ^ 2) ^ (-κ / 2) := by
          rw [← Real.rpow_natCast (radC g z) 2, ← Real.rpow_mul hrad0.le]; ring_nf
      _ ≤ (μ₀ * (1 + ‖z - centerC g‖ ^ 2)) ^ (-κ / 2) :=
          Real.rpow_le_rpow_of_nonpos hMn hlb (by linarith)
      _ = μ₀ ^ (-κ / 2) * ((1 : ℝ) + ‖z - centerC g‖ ^ 2) ^ (-κ / 2) := by
          rw [Real.mul_rpow hμ₀.le (by positivity)]
      _ ≤ B * ((1 : ℝ) + ‖z - centerC g‖ ^ 2) ^ (-κ₀ / 2) := by
          refine mul_le_mul ?_ ?_ (Real.rpow_nonneg (by positivity) _) hB.le
          · rw [hBdef, show -κ / 2 = -(κ / 2) from by ring, Real.rpow_neg hμ₀.le, ← Real.inv_rpow hμ₀.le]
            exact Real.rpow_le_rpow_of_exponent_le (one_le_inv_iff₀.2 ⟨hμ₀, hμ₀1⟩) (by linarith)
          · exact Real.rpow_le_rpow_of_exponent_le hW (by linarith)
      _ = B * h (z - centerC g) := by rw [hhdef]
  have hmaj_int : Integrable (fun z : ℂ => B * h (z - centerC g)) :=
    (hh_int.comp_sub_right (centerC g)).const_mul B
  have hmeas : AEStronglyMeasurable (fun z : ℂ => radC g z ^ (-κ)) volume :=
    ((contDiff_radC hg').continuous.rpow_const
      (fun z => Or.inl (radC_pos hg' z).ne')).aestronglyMeasurable
  have hnn : ∀ z : ℂ, 0 ≤ radC g z ^ (-κ) := fun z => Real.rpow_nonneg (radC_pos hg' z).le _
  have hint : Integrable (fun z : ℂ => radC g z ^ (-κ)) :=
    hmaj_int.mono' hmeas (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (hnn z)]; exact hcmp z)
  refine ⟨hint, ?_⟩
  calc ∫ z : ℂ, radC g z ^ (-κ) ≤ ∫ z : ℂ, B * h (z - centerC g) :=
        integral_mono hint hmaj_int hcmp
    _ = B * ∫ z : ℂ, h (z - centerC g) := integral_const_mul _ _
    _ = B * ∫ z : ℂ, h z := by rw [integral_sub_right_eq_self h (centerC g)]
    _ ≤ B * (∫ z, h z) + 1 := by linarith

end B2bCL2

end

open B2bCL2 in

/--
@isnad1 id=ex.3h3v.s8.60145d43e122 from=translated src=- shape=039984ed vocab=590af743
-/
theorem solution
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (_h𝒢 : IsCompact 𝒢) (_hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (κ₀ κ₁ : ℝ) (_hκ₀ : 2 < κ₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ g ∈ 𝒢, ∀ κ : ℝ, κ₀ ≤ κ → κ ≤ κ₁ →
      Integrable (fun z : ℂ => radC g z ^ (-κ)) ∧ ∫ z : ℂ, radC g z ^ (-κ) ≤ M :=
  B2bCL2.main 𝒢 _h𝒢 _hdet κ₀ κ₁ _hκ₀
