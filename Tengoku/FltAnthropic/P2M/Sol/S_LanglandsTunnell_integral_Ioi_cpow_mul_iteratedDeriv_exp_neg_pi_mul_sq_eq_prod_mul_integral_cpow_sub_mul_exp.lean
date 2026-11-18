import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp

set_option autoImplicit false

open MeasureTheory Set Filter Topology Polynomial

namespace P2mIbpPower

noncomputable def G : ℝ → ℂ := fun s => (Real.exp (-(Real.pi * s ^ 2)) : ℂ)

noncomputable def P : ℕ → ℂ[X]
  | 0 => 1
  | k + 1 => derivative (P k) - C (2 * (Real.pi : ℂ)) * X * P k

/--
@isnad1 id=eq.0h1v.s5.e4f343c35c4a from=translated src=- shape=cb2bbcc3 vocab=7c470295
-/
lemma G_apply (s : ℝ) : G s = (Real.exp (-(Real.pi * s ^ 2)) : ℂ) := rfl

/--
@isnad1 id=eq.0h1v.s5.2a6c51cb5e38 from=translated src=- shape=13bde707 vocab=0af9ecd7
-/
lemma norm_G (s : ℝ) : ‖G s‖ = Real.exp (-(Real.pi * s ^ 2)) := by
  rw [G_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/--
@isnad1 id=continuo.0h0v.s4.6a3975a7e64d from=translated src=- shape=54c8eceb vocab=290df69d
-/
lemma continuous_G : Continuous G := by
  unfold G; fun_prop

/--
@isnad1 id=hasderiv.0h1v.s6.d2d27dfe105f from=translated src=- shape=0ed30b99 vocab=ab1b8ce0
-/
lemma hasDerivAt_G (s : ℝ) : HasDerivAt G (-(2 * (Real.pi : ℂ) * s) * G s) s := by
  have h1 : HasDerivAt (fun t : ℝ => -(Real.pi * t ^ 2)) (-(Real.pi * (2 * s))) s := by
    have := ((hasDerivAt_pow 2 s).const_mul Real.pi).neg
    simp at this
    exact this
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(Real.pi * t ^ 2)))
      (Real.exp (-(Real.pi * s ^ 2)) * (-(Real.pi * (2 * s)))) s := h1.exp
  have h3 := h2.ofReal_comp
  convert h3 using 1
  · rfl
  simp only [G, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

/--
@isnad1 id=hasderiv.0h2v.s6.5812263549a2 from=translated src=- shape=cd8b7229 vocab=33adac3f
-/
lemma hasDerivAt_Peval_mul_G (k : ℕ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (P k).eval (t : ℂ) * G t) ((P (k + 1)).eval (s : ℂ) * G s) s := by
  have hp : HasDerivAt (fun t : ℝ => (P k).eval (t : ℂ)) ((derivative (P k)).eval (s : ℂ)) s :=
    ((P k).hasDerivAt (s : ℂ)).comp_ofReal
  have := hp.mul (hasDerivAt_G s)
  convert this using 1
  · rfl
  · rfl
  simp only [P, eval_sub, eval_mul, eval_C, eval_X]
  ring

/--
@isnad1 id=eq.0h1v.s5.fa6628d11328 from=translated src=- shape=4a0283ae vocab=0144a50c
-/
lemma iteratedDeriv_G (k : ℕ) : iteratedDeriv k G = fun s : ℝ => (P k).eval (s : ℂ) * G s := by
  induction k with
  | zero => funext s; simp [P, iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    exact (hasDerivAt_Peval_mul_G k s).deriv

/--
@isnad1 id=hasderiv.0h2v.s6.185b0df91349 from=translated src=- shape=e1876c70 vocab=a865251e
-/
lemma hasDerivAt_iteratedDeriv_G (k : ℕ) (s : ℝ) :
    HasDerivAt (iteratedDeriv k G) (iteratedDeriv (k + 1) G s) s := by
  rw [iteratedDeriv_G k, iteratedDeriv_G (k + 1)]
  exact hasDerivAt_Peval_mul_G k s

/--
@isnad1 id=continuo.0h1v.s5.33d75d83bbe7 from=translated src=- shape=9e39cfad vocab=169dfb1e
-/
lemma continuous_iteratedDeriv_G (k : ℕ) : Continuous (iteratedDeriv k G) := by
  rw [iteratedDeriv_G]
  exact ((P k).continuous.comp Complex.continuous_ofReal).mul continuous_G

/--
@isnad1 id=ex.0h1v.s6.ff0709d1e20b from=translated src=- shape=aacabf86 vocab=32ced5d5
-/
lemma norm_eval_le (p : ℂ[X]) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ : ℝ, 1 ≤ σ → ‖p.eval (σ : ℂ)‖ ≤ B * σ ^ p.natDegree := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖,
    Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun σ hσ => ?_⟩
  rw [eval_eq_sum_range, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hσ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) (norm_nonneg _)

/--
@isnad1 id=ex.0h1v.s6.ad4d2cbbc875 from=translated src=- shape=9e23ce2b vocab=6396105c
-/
lemma norm_iteratedDeriv_G_le (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ : ℝ, 1 ≤ σ →
      ‖iteratedDeriv k G σ‖ ≤ B * (σ ^ ((P k).natDegree : ℝ) * Real.exp (-(Real.pi * σ ^ 2))) := by
  obtain ⟨B, hB0, hB⟩ := norm_eval_le (P k)
  refine ⟨B, hB0, fun σ hσ => ?_⟩
  rw [iteratedDeriv_G, norm_mul, norm_G, Real.rpow_natCast, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hB σ hσ) (Real.exp_pos _).le

noncomputable def F (w v : ℝ) (b : ℂ) : ℝ → ℂ := fun σ => ((σ * w - v : ℝ) : ℂ) ^ b

/--
@isnad1 id=lt.2h3v.s5.3aa757aefaf8 from=translated src=- shape=7213ac8d vocab=2d787729
-/
lemma sub_pos_of_lt {w : ℝ} (hw : 0 < w) (v : ℝ) {σ : ℝ} (hσ : v / w < σ) : 0 < σ * w - v := by
  rw [div_lt_iff₀ hw] at hσ; linarith

/--
@isnad1 id=eq.1h3v.s5.0a7a3e91c6a6 from=translated src=- shape=79b37cac vocab=2d787729
-/
lemma sub_eq_mul {w : ℝ} (hw : 0 < w) (v σ : ℝ) : σ * w - v = w * (σ - v / w) := by
  field_simp

/--
@isnad1 id=eq.2h4v.s6.f45ee22dd148 from=translated src=- shape=b48a56e6 vocab=323d1bdd
-/
lemma norm_F {w : ℝ} (hw : 0 < w) (v : ℝ) (b : ℂ) {σ : ℝ} (hσ : v / w < σ) :
    ‖F w v b σ‖ = (σ * w - v) ^ b.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos_of_lt hw v hσ) b

/--
@isnad1 id=hasderiv.2h4v.s6.9b335918dd81 from=translated src=- shape=251bcb23 vocab=586a5b60
-/
lemma hasDerivAt_F {w : ℝ} (hw : 0 < w) (v : ℝ) (b : ℂ) {σ : ℝ} (hσ : v / w < σ) :
    HasDerivAt (F w v b) (b * (w : ℂ) * F w v (b - 1) σ) σ := by
  have hlin : HasDerivAt (fun z : ℂ => z * w - v) (w : ℂ) (σ : ℂ) := by
    simpa using ((hasDerivAt_id (σ : ℂ)).mul_const (w : ℂ)).sub_const (v : ℂ)
  have hslit : (σ : ℂ) * w - v ∈ Complex.slitPlane := by
    have : ((σ * w - v : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.mpr (sub_pos_of_lt hw v hσ)
    simpa using this
  have h := (hlin.cpow_const (c := b) hslit).comp_ofReal
  have hfun : (fun y : ℝ => ((y : ℂ) * w - v) ^ b) = F w v b := by
    funext y; simp [F]
  rw [hfun] at h
  convert h using 1
  simp only [F, Complex.ofReal_sub, Complex.ofReal_mul]
  ring

/--
@isnad1 id=continuo.1h3v.s5.8a01772a8b05 from=translated src=- shape=387f39e4 vocab=cf952d79
-/
lemma continuousOn_F {w : ℝ} (hw : 0 < w) (v : ℝ) (b : ℂ) : ContinuousOn (F w v b) (Ioi (v / w)) :=
  fun _ hσ => (hasDerivAt_F hw v b hσ).continuousAt.continuousWithinAt

/--
@isnad1 id=tendsto.2h3v.s6.f25e99fdf60d from=translated src=- shape=8d2a56d8 vocab=64b97fe9
-/
lemma tendsto_F_zero {w : ℝ} (hw : 0 < w) (v : ℝ) {b : ℂ} (hb : 0 < b.re) :
    Tendsto (F w v b) (𝓝[>] (v / w)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun σ : ℝ => (σ * w - v) ^ b.re) (𝓝 (v / w)) (𝓝 0) := by
    have hc : ContinuousAt (fun σ : ℝ => (σ * w - v) ^ b.re) (v / w) :=
      ((continuousAt_id.mul continuousAt_const).sub continuousAt_const).rpow_const (Or.inr hb.le)
    have hval : ((v / w) * w - v) ^ b.re = 0 := by
      rw [div_mul_cancel₀ v hw.ne', sub_self, Real.zero_rpow hb.ne']
    simpa [hval] using hc.tendsto
  refine (tendsto_nhdsWithin_of_tendsto_nhds h1).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact (norm_F hw v b hσ).symm

/--
@isnad1 id=interval.2h4v.s6.235d71927abc from=translated src=- shape=046323e6 vocab=33c68294
-/
lemma intervalIntegrable_F {w : ℝ} (hw : 0 < w) (v : ℝ) {b : ℂ} (hb : -1 < b.re) (D : ℝ) :
    IntervalIntegrable (F w v b) volume (v / w) D := by

  have h0 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ b) volume (v / w * w - v) (D * w - v) :=
    intervalIntegral.intervalIntegrable_cpow' hb
  have h1 := h0.comp_sub_right v
  have h2 := h1.comp_mul_right (c := w)
  simp only [sub_add_cancel] at h2
  rw [mul_div_cancel_right₀ _ hw.ne', mul_div_cancel_right₀ _ hw.ne'] at h2
  convert h2 using 1
  rfl

/--
@isnad1 id=ex.1h4v.s7.82db1707a877 from=translated src=- shape=df6d391c vocab=20f740a9
-/
lemma norm_F_mul_iteratedDeriv_le {w : ℝ} (hw : 0 < w) (v : ℝ) (b : ℂ) (k : ℕ) :
    ∃ C s : ℝ, 0 ≤ s ∧ ∀ σ : ℝ, 1 ≤ σ → v / w + 1 ≤ σ →
      ‖F w v b σ * iteratedDeriv k G σ‖ ≤ C * (σ ^ s * Real.exp (-Real.pi * σ ^ 2)) := by
  obtain ⟨B, hB0, hB⟩ := norm_iteratedDeriv_G_le k
  set r : ℝ := max b.re 0 with hr
  set A : ℝ := max ((w * (1 + |v / w|)) ^ b.re) (w ^ b.re) with hA
  refine ⟨A * B, r + (P k).natDegree, by positivity, fun σ h1 h2 => ?_⟩
  have hσc : v / w < σ := by linarith
  have hpos : 0 < σ * w - v := sub_pos_of_lt hw v hσc

  have hF : ‖F w v b σ‖ ≤ A * σ ^ r := by
    rw [norm_F hw v b hσc]
    rcases le_or_gt 0 b.re with hb | hb
    ·
      have hle : σ * w - v ≤ w * (1 + |v / w|) * σ := by
        rw [sub_eq_mul hw v σ]
        have : σ - v / w ≤ (1 + |v / w|) * σ := by
          have h3 : -(v / w) ≤ |v / w| := neg_le_abs _
          have h4 : |v / w| ≤ |v / w| * σ := le_mul_of_one_le_right (abs_nonneg _) h1
          nlinarith
        calc w * (σ - v / w) ≤ w * ((1 + |v / w|) * σ) :=
              mul_le_mul_of_nonneg_left this hw.le
          _ = w * (1 + |v / w|) * σ := by ring
      calc (σ * w - v) ^ b.re ≤ (w * (1 + |v / w|) * σ) ^ b.re :=
            Real.rpow_le_rpow hpos.le hle hb
        _ = (w * (1 + |v / w|)) ^ b.re * σ ^ b.re :=
            Real.mul_rpow (by positivity) (by linarith)
        _ ≤ A * σ ^ r := by
            apply mul_le_mul (le_max_left _ _) _ (by positivity) (by positivity)
            rw [hr, max_eq_left hb]
    ·
      have hge : w ≤ σ * w - v := by rw [sub_eq_mul hw v σ]; nlinarith
      calc (σ * w - v) ^ b.re ≤ w ^ b.re :=
            Real.rpow_le_rpow_of_nonpos hw hge hb.le
        _ = w ^ b.re * σ ^ r := by rw [hr, max_eq_right hb.le, Real.rpow_zero, mul_one]
        _ ≤ A * σ ^ r := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  calc ‖F w v b σ * iteratedDeriv k G σ‖ = ‖F w v b σ‖ * ‖iteratedDeriv k G σ‖ := norm_mul _ _
    _ ≤ (A * σ ^ r) * (B * (σ ^ ((P k).natDegree : ℝ) * Real.exp (-(Real.pi * σ ^ 2)))) :=
        mul_le_mul hF (hB σ h1) (norm_nonneg _) (by positivity)
    _ = A * B * (σ ^ (r + (P k).natDegree) * Real.exp (-Real.pi * σ ^ 2)) := by
        rw [Real.rpow_add (by linarith), neg_mul]; ring

/--
@isnad1 id=integrab.2h4v.s6.e93fdc43cecc from=translated src=- shape=681cb24e vocab=6a535306
-/
lemma integrableOn_F_mul_iteratedDeriv {w : ℝ} (hw : 0 < w) (v : ℝ) {b : ℂ} (hb : -1 < b.re) (k : ℕ) :
    IntegrableOn (fun σ => F w v b σ * iteratedDeriv k G σ) (Ioi (v / w)) := by
  set D : ℝ := max 1 (v / w + 1) with hD
  have hcD : v / w ≤ D := by
    have : v / w + 1 ≤ D := le_max_right _ _
    linarith
  rw [← Ioc_union_Ioi_eq_Ioi hcD, integrableOn_union]
  constructor
  ·
    have h := (intervalIntegrable_F hw v hb D).mul_continuousOn
      (g := iteratedDeriv k G) (continuous_iteratedDeriv_G k).continuousOn
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hcD).mp h
  ·
    obtain ⟨C, s, hs, hC⟩ := norm_F_mul_iteratedDeriv_le hw v b k
    have hmeas : AEStronglyMeasurable (fun σ => F w v b σ * iteratedDeriv k G σ)
        (volume.restrict (Ioi D)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ((continuousOn_F hw v b).mono ?_).mul (continuous_iteratedDeriv_G k).continuousOn
      exact Ioi_subset_Ioi hcD
    have hdom : IntegrableOn (fun σ : ℝ => C * (σ ^ s * Real.exp (-Real.pi * σ ^ 2))) (Ioi D) := by
      have h0 := (integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos (by linarith : (-1 : ℝ) < s))
      exact (h0.mono_set (Ioi_subset_Ioi (le_max_left _ _ |>.trans' zero_le_one))).const_mul C
    refine Integrable.mono' hdom hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
    have hσ' : D < σ := hσ
    exact hC σ (by linarith [le_max_left 1 (v / w + 1)]) (by linarith [le_max_right 1 (v / w + 1)])

/--
@isnad1 id=tendsto.1h4v.s6.21040e665aa9 from=translated src=- shape=c16fb9af vocab=2159f203
-/
lemma tendsto_F_mul_iteratedDeriv_atTop {w : ℝ} (hw : 0 < w) (v : ℝ) (b : ℂ) (k : ℕ) :
    Tendsto (fun σ => F w v b σ * iteratedDeriv k G σ) atTop (𝓝 0) := by
  obtain ⟨C, s, hs, hC⟩ := norm_F_mul_iteratedDeriv_le hw v b k

  have hlim : Tendsto (fun σ : ℝ => |C| * (σ ^ s * Real.exp (-Real.pi * σ))) atTop (𝓝 0) := by
    have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s Real.pi Real.pi_pos).const_mul |C|
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (v / w + 1)] with σ h1 h2
  refine (hC σ h1 h2).trans ?_
  have hexp : Real.exp (-Real.pi * σ ^ 2) ≤ Real.exp (-Real.pi * σ) := by
    apply Real.exp_le_exp.mpr
    have : σ ≤ σ ^ 2 := by nlinarith
    nlinarith [Real.pi_pos]
  calc C * (σ ^ s * Real.exp (-Real.pi * σ ^ 2))
      ≤ |C| * (σ ^ s * Real.exp (-Real.pi * σ ^ 2)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (σ ^ s * Real.exp (-Real.pi * σ)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        exact mul_le_mul_of_nonneg_left hexp (by positivity)

/--
@isnad1 id=tendsto.2h4v.s6.1e694786990e from=translated src=- shape=00d8c7d1 vocab=99eab6f5
-/
lemma tendsto_F_mul_iteratedDeriv_nhdsWithin {w : ℝ} (hw : 0 < w) (v : ℝ) {b : ℂ} (hb : 0 < b.re) (k : ℕ) :
    Tendsto (fun σ => F w v b σ * iteratedDeriv k G σ) (𝓝[>] (v / w)) (𝓝 0) := by
  have h1 := tendsto_F_zero hw v hb
  have h2 : Tendsto (iteratedDeriv k G) (𝓝[>] (v / w)) (𝓝 (iteratedDeriv k G (v / w))) :=
    ((continuous_iteratedDeriv_G k).tendsto _).mono_left nhdsWithin_le_nhds
  simpa using h1.mul h2

/--
@isnad1 id=eq.2h4v.s7.77a9e77fb8bf from=translated src=- shape=6c124dd7 vocab=1b0d1812
-/
lemma integral_step {w : ℝ} (hw : 0 < w) (v : ℝ) {a : ℂ} (n : ℕ) (ha : (n : ℝ) < a.re) :
    ∫ σ in Ioi (v / w), F w v a σ * iteratedDeriv (n + 1) G σ =
      -(a * w) * ∫ σ in Ioi (v / w), F w v (a - 1) σ * iteratedDeriv n G σ := by
  have ha0 : 0 < a.re := lt_of_le_of_lt (Nat.cast_nonneg n) ha
  have ha1 : -1 < (a - 1).re := by simp; linarith
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := F w v a) (u' := fun σ => a * (w : ℂ) * F w v (a - 1) σ)
    (v := iteratedDeriv n G) (v' := iteratedDeriv (n + 1) G) (a' := 0) (b' := 0)
    (fun σ hσ => hasDerivAt_F hw v a hσ)
    (fun σ _ => hasDerivAt_iteratedDeriv_G n σ)
    (integrableOn_F_mul_iteratedDeriv hw v (by linarith) (n + 1))
    (by
      have hI : IntegrableOn (fun σ => a * (w : ℂ) * (F w v (a - 1) σ * iteratedDeriv n G σ))
          (Ioi (v / w)) :=
        (integrableOn_F_mul_iteratedDeriv hw v ha1 n).const_mul (a * (w : ℂ))
      refine hI.congr_fun (fun σ _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply]; ring)
    (tendsto_F_mul_iteratedDeriv_nhdsWithin hw v ha0 n)
    (tendsto_F_mul_iteratedDeriv_atTop hw v a n)
  rw [hibp, sub_zero, zero_sub, ← integral_neg, ← integral_const_mul]
  congr 1; funext σ; ring

/--
@isnad1 id=eq.2h4v.s7.f92521d49f09 from=translated src=- shape=76a96aec vocab=be3507d1
-/
theorem integral_eq {w : ℝ} (hw : 0 < w) (v : ℝ) (n : ℕ) :
    ∀ a : ℂ, (n : ℝ) - 1 < a.re →
      ∫ σ in Ioi (v / w), F w v a σ * iteratedDeriv n G σ =
        (-(w : ℂ)) ^ n * (∏ k ∈ Finset.range n, (a - k)) *
          ∫ σ in Ioi (v / w), F w v (a - n) σ * G σ := by
  induction n with
  | zero => intro a _; simp [iteratedDeriv_zero]
  | succ n ih =>
    intro a ha
    have ha' : (n : ℝ) < a.re := by push_cast at ha; linarith
    rw [integral_step hw v n ha', ih (a - 1) (by simp; linarith)]
    have h1 : a - 1 - (n : ℂ) = a - (((n + 1 : ℕ)) : ℂ) := by push_cast; ring
    rw [h1, Finset.prod_range_succ' (fun k => a - k)]
    have h2 : ∀ k ∈ Finset.range n, a - 1 - (k : ℂ) = a - ((k + 1 : ℕ) : ℂ) := by
      intro k _; push_cast; ring
    rw [Finset.prod_congr rfl h2]
    push_cast
    ring

end P2mIbpPower

open P2mIbpPower in

/--
@isnad1 id=eq.2h4v.s8.18ceaa71c66e from=translated src=- shape=85d5bc31 vocab=db33d152
-/
theorem solution
    (n : ℕ) (a : ℂ) (ha : (n : ℝ) - 1 < a.re) (w : ℝ) (hw : 0 < w) (v : ℝ) :
    ∫ σ in Ioi (v / w), (((σ * w - v : ℝ) : ℂ) ^ a) *
        iteratedDeriv n (fun s : ℝ => (Real.exp (-(Real.pi * s ^ 2)) : ℂ)) σ
      = (-(w : ℂ)) ^ n * (∏ k ∈ Finset.range n, (a - (k : ℂ))) *
          ∫ σ in Ioi (v / w), (((σ * w - v : ℝ) : ℂ) ^ (a - (n : ℂ))) *
            (Real.exp (-(Real.pi * σ ^ 2)) : ℂ) :=
  P2mIbpPower.integral_eq hw v n a ha
