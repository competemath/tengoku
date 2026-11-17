import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MeasureTheory_norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod

set_option autoImplicit false

open MeasureTheory

namespace SUPFT9

open scoped FourierTransform RealInnerProductSpace

/--
@isnad1 id=continuo.0h0v.s5.4e31639fb070 from=translated src=- shape=52aed1e4 vocab=8fc9430f
-/
lemma continuous_w : Continuous fun t : ℝ => (1 + |t|)⁻¹ ^ 2 :=
  ((continuous_const.add continuous_abs).inv₀
    (fun t => (by have := abs_nonneg t; linarith : (1 : ℝ) + |t| ≠ 0))).pow 2

/--
@isnad1 id=eq.0h0v.s6.5c09bd69045d from=translated src=- shape=45bd078a vocab=011f3144
-/
lemma integral_Ioi_w : ∫ t in Set.Ioi (0 : ℝ), (1 + t)⁻¹ ^ 2 = 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (g := fun t : ℝ => -(1 + t)⁻¹) (g' := fun t => (1 + t)⁻¹ ^ 2)
    (a := 0) (l := 0) ?_ ?_ ?_ ?_
  · simpa using h
  · exact (((continuous_const.add continuous_id).continuousAt.inv₀ (by norm_num)).neg).continuousWithinAt
  · intro t ht
    have ht' : (1 : ℝ) + t ≠ 0 := by have := Set.mem_Ioi.mp ht; linarith
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id t).const_add 1
    have h2 := (h1.inv ht').neg
    convert h2 using 1
    · rfl
    · rfl
    · rfl
    field_simp
  · intro t _; positivity
  · have : Filter.Tendsto (fun t : ℝ => (1 + t)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_left _ 1 Filter.tendsto_id)
    simpa using this.neg

/--
@isnad1 id=eq.0h0v.s6.54d9f1147850 from=translated src=- shape=cfb6c9b2 vocab=e2fe5d60
-/
lemma integral_w : ∫ t : ℝ, (1 + |t|)⁻¹ ^ 2 = 2 := by
  have := integral_comp_abs (f := fun t => (1 + t)⁻¹ ^ 2)
  rw [this, integral_Ioi_w]; norm_num

/--
@isnad1 id=le.0h1v.s6.d7ac0c4a5d23 from=translated src=- shape=ebe85a4a vocab=f7eec3b5
-/
lemma w_le (η : ℝ) : (1 + |η|)⁻¹ ^ 2 ≤ (1 + η ^ 2)⁻¹ := by
  rw [inv_pow]
  apply inv_anti₀ (by positivity)
  nlinarith [abs_nonneg η, sq_abs η]

/--
@isnad1 id=integrab.0h0v.s6.e7ee010efef3 from=translated src=- shape=1587e3b3 vocab=c2bf1a22
-/
lemma integrable_w : Integrable (fun η : ℝ => (1 + |η|)⁻¹ ^ 2) := by
  refine (integrable_inv_one_add_sq).mono' continuous_w.aestronglyMeasurable (ae_of_all _ fun η => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact w_le η

/--
@isnad1 id=integrab.0h1v.s6.b27481533f47 from=translated src=- shape=e6401055 vocab=62bbff84
-/
lemma integrable_P (r : ℕ) : Integrable (fun x : Fin r → ℝ => ∏ k, (1 + |x k|)⁻¹ ^ 2) := by
  have := Integrable.fintype_prod (ι := Fin r) (f := fun _ (t : ℝ) => (1 + |t|)⁻¹ ^ 2) (μ := fun _ => volume)
    (fun _ => integrable_w)
  simpa [volume_pi] using this

/--
@isnad1 id=eq.0h1v.s7.6027e4ccf3a9 from=translated src=- shape=2b0f5a1a vocab=527adfcf
-/
lemma integral_P (r : ℕ) : ∫ x : Fin r → ℝ, ∏ k, (1 + |x k|)⁻¹ ^ 2 = 2 ^ r := by
  rw [integral_fintype_prod_volume_eq_pow (fun t : ℝ => (1 + |t|)⁻¹ ^ 2), integral_w, Fintype.card_fin]

variable {r : ℕ}

/--
@isnad1 id=measurep.0h1v.s7.5ba7adcf7ac7 from=translated src=- shape=8dfcc495 vocab=998133f3
-/
lemma mp_toLp : MeasurePreserving (WithLp.toLp 2 : (Fin r → ℝ) → EuclideanSpace ℝ (Fin r)) :=
  PiLp.volume_preserving_toLp (Fin r)
/--
@isnad1 id=measurab.0h1v.s6.53dd4d06c1be from=translated src=- shape=3087f43a vocab=3bff8309
-/
lemma me_toLp : MeasurableEmbedding (WithLp.toLp 2 : (Fin r → ℝ) → EuclideanSpace ℝ (Fin r)) :=
  (MeasurableEquiv.toLp 2 (Fin r → ℝ)).measurableEmbedding
/--
@isnad1 id=measurep.0h1v.s7.cf6dbd2104ea from=translated src=- shape=644aedf0 vocab=9e3b7be4
-/
lemma mp_ofLp : MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (Fin r) → (Fin r → ℝ)) :=
  PiLp.volume_preserving_ofLp (Fin r)
/--
@isnad1 id=measurab.0h1v.s6.5a3cd2cdb736 from=translated src=- shape=49609b3d vocab=b99cb82b
-/
lemma me_ofLp : MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin r) → (Fin r → ℝ)) :=
  (MeasurableEquiv.toLp 2 (Fin r → ℝ)).symm.measurableEmbedding

/--
@isnad1 id=integrab.1h2v.s8.57ca2588359d from=translated src=- shape=befe25df vocab=a3b08d1a
-/
lemma integrable_comp_ofLp {g : (Fin r → ℝ) → ℂ} (hg : Integrable g) :
    Integrable (fun v : EuclideanSpace ℝ (Fin r) => g (WithLp.ofLp v)) :=
  (mp_ofLp.integrable_comp_emb me_ofLp).mpr hg

/--
@isnad1 id=integrab.1h2v.s8.661d1897ef50 from=translated src=- shape=09f897e8 vocab=c3fa0312
-/
lemma integrable_comp_ofLp_real {g : (Fin r → ℝ) → ℝ} (hg : Integrable g) :
    Integrable (fun v : EuclideanSpace ℝ (Fin r) => g (WithLp.ofLp v)) :=
  (mp_ofLp.integrable_comp_emb me_ofLp).mpr hg

/--
@isnad1 id=eq.0h2v.s8.3b8bc71c45eb from=translated src=- shape=9a142f11 vocab=26445736
-/
lemma integral_comp_ofLp_real (g : (Fin r → ℝ) → ℝ) :
    ∫ v : EuclideanSpace ℝ (Fin r), g (WithLp.ofLp v) = ∫ y, g y :=
  mp_ofLp.integral_comp me_ofLp g

/--
@isnad1 id=eq.0h3v.s8.33257e64e583 from=translated src=- shape=afb4d06c vocab=bfab3743
-/
lemma fourier_transport (f : (Fin r → ℝ) → ℂ) (w : EuclideanSpace ℝ (Fin r)) :
    𝓕 (fun v : EuclideanSpace ℝ (Fin r) => f (WithLp.ofLp v)) w =
      ∫ y : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, (WithLp.ofLp w) k * y k : ℝ) : ℂ))) * f y := by
  rw [Real.fourier_eq', ← mp_toLp.integral_comp me_toLp]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [WithLp.ofLp_toLp, PiLp.inner_apply, smul_eq_mul]
  congr 1
  congr 1
  push_cast
  simp only [RCLike.inner_apply, conj_trivial, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
  rw [Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

/--
@isnad1 id=continuo.1h2v.s8.718be3021877 from=translated src=- shape=74a5e60e vocab=142ff93a
-/
lemma continuous_fourier {F : EuclideanSpace ℝ (Fin r) → ℂ} (hF : Integrable F) : Continuous (𝓕 F) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hF

/--
@isnad1 id=le.3h4v.s9.eb4ebf5db4e6 from=translated src=- shape=9dbfe53c vocab=5c7ac104
-/
lemma norm_fourierInv_le {G : EuclideanSpace ℝ (Fin r) → ℂ} {B : EuclideanSpace ℝ (Fin r) → ℝ}
    (hG : Integrable G) (hB : Integrable B) (h : ∀ w, ‖G w‖ ≤ B w) (v : EuclideanSpace ℝ (Fin r)) :
    ‖𝓕⁻ G v‖ ≤ ∫ w, B w := by
  rw [Real.fourierInv_eq]
  calc ‖∫ w, 𝐞 ⟪w, v⟫ • G w‖ ≤ ∫ w, ‖𝐞 ⟪w, v⟫ • G w‖ := norm_integral_le_integral_norm _
    _ = ∫ w, ‖G w‖ := by simp_rw [Circle.norm_smul]
    _ ≤ ∫ w, B w := integral_mono hG.norm hB h

end SUPFT9

/--
@isnad1 id=le.3h4v.s8.6e15a41ddb3b from=translated src=- shape=5a8dc65f vocab=0455795a
-/
theorem solution
    {r : ℕ} (f : (Fin r → ℝ) → ℂ) (hf : Continuous f) (hfi : Integrable f) (C : ℝ)
    (hC : ∀ ξ : Fin r → ℝ,
      ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * f x‖ ≤ C * ∏ k, (1 + |ξ k|)⁻¹ ^ 2)
    (x : Fin r → ℝ) :
    ‖f x‖ ≤ 2 ^ r * C := by
  have hFc : Continuous (fun v : EuclideanSpace ℝ (Fin r) => f (WithLp.ofLp v)) := hf.comp (PiLp.continuous_ofLp 2 _)
  have hFi : Integrable (fun v : EuclideanSpace ℝ (Fin r) => f (WithLp.ofLp v)) := SUPFT9.integrable_comp_ofLp hfi
  have hbd : ∀ w : EuclideanSpace ℝ (Fin r),
      ‖FourierTransform.fourier (fun v : EuclideanSpace ℝ (Fin r) => f (WithLp.ofLp v)) w‖ ≤
        C * ∏ k, (1 + |(WithLp.ofLp w) k|)⁻¹ ^ 2 := by
    intro w; rw [SUPFT9.fourier_transport]; exact hC _
  have hPi : Integrable (fun w : EuclideanSpace ℝ (Fin r) => C * ∏ k, (1 + |(WithLp.ofLp w) k|)⁻¹ ^ 2) :=
    SUPFT9.integrable_comp_ofLp_real ((SUPFT9.integrable_P r).const_mul C)
  have hFTi : Integrable (FourierTransform.fourier (fun v : EuclideanSpace ℝ (Fin r) => f (WithLp.ofLp v))) :=
    hPi.mono' (SUPFT9.continuous_fourier hFi).aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  have hinv := hFc.fourierInv_fourier_eq hFi hFTi
  have hx : f x = FourierTransformInv.fourierInv
      (FourierTransform.fourier (fun v : EuclideanSpace ℝ (Fin r) => f (WithLp.ofLp v))) (WithLp.toLp 2 x) := by
    rw [hinv]
  rw [hx]
  calc _ ≤ ∫ w : EuclideanSpace ℝ (Fin r), C * ∏ k, (1 + |(WithLp.ofLp w) k|)⁻¹ ^ 2 :=
        SUPFT9.norm_fourierInv_le hFTi hPi hbd _
    _ = C * ∫ y : Fin r → ℝ, ∏ k, (1 + |y k|)⁻¹ ^ 2 := by
        rw [integral_const_mul, ← SUPFT9.integral_comp_ofLp_real]
    _ = 2 ^ r * C := by rw [SUPFT9.integral_P, mul_comm]
