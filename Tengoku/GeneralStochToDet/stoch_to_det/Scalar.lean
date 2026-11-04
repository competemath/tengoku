import Tengoku.GeneralStochToDet.stoch_to_det.Mismatch
import Tengoku.Seed.NumberTheory.Harmonic.GammaDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# §8. The scalar channel theorem

`scalar = I(σ_B(Z) T ; Z ∣ B, C₀) ≤ S + κ d`, with `κ = (1 + ln 8 − γ)/ln 2`.

The statement of Theorem 8.1 is the `RaceQuantities.scalar_le` obligation;
this module keeps the scalar analytic ingredients and the `Ksc` assembly bound.

## Proof structure

The calculation is performed in nats and converted at the end; nats-valued statements
here carry the `_nats` suffix. Fix a context `(g,b)` and write `R := p/σ_b(Z)` under the source
posterior `ν`, `C := −E_ν ln R = D(ν ‖ q_g) ≥ 0`. Then:

* **Off-diagonal `b ≠ g`.** The bijection
  `W := ln(U/p) = X + N` with `X := −ln R` a function of `Z` and `N := ln T`
  independent turns the problem into a scalar additive-noise channel:
  `I(U;Z ∣ b,g) = h(X+N) − h(N)`. Then `h(N) = γ + 1` (an explicit integral),
  `E|N| ≤ 1 + e⁻¹ ≤ 2`, `E|X| ≤ C + 2`, and the max-entropy bound (T4) gives
  `≤ C + ln 8 − γ`. This is the only place `(T4)` — and hence differential
  entropy — is used here.
* **Diagonal `b = g`.** The golden formula against the
  reference `Exp(mean p)`, using
  `D(Exp(mean s) ‖ Exp(mean p)) = ln(p/s) + s/p − 1`. Gives `p·I ≤ 1 − p`.
* **Assembly.** The mixture identity
  `∑_b p_{gb} C_{gb} = I(B;Z ∣ C₀=g)` collapses the off-diagonal sum, and
  cluster-level calibration gives `I(B;Z ∣ C₀) = S`, `P(B ≠ C₀) = d`.

## Mathlib support

`ProbabilityTheory.expMeasure` and `InformationTheory.klDiv` cover the diagonal
case. The off-diagonal case additionally needs `h(N) = γ + 1` for `N = ln T`,
`T ~ Exp(1)` — obtained from the derivative of the Gamma integral at one — and
`stoch_to_det.Toolkit.diffEntropy_le_of_abs_le`.
-/

namespace stoch_to_det

open Finset MeasureTheory ProbabilityTheory InformationTheory

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} {D : SeedSetup p} {K : Clustering D}

/-- The elementary positive-log estimate used in the sharpened scalar
channel argument.-/
lemma log_pos_part_le_div_exp_one (r : ℝ) (hr : 0 < r) :
    max (Real.log r) 0 ≤ r / Real.exp 1 := by
  by_cases hlog : Real.log r ≤ 0
  · rw [max_eq_right hlog]
    positivity
  · rw [max_eq_left (le_of_not_ge hlog)]
    apply (le_div_iff₀ (Real.exp_pos 1)).2
    simpa [Real.exp_log hr, mul_comm] using
      (Real.exp_one_mul_le_exp (x := Real.log r))

/-- `E|ln T| ≤ 1 + e⁻¹ ≤ 2` for `T ~ Exp(1)`.-/
theorem abs_log_exp_integral_le :
    ∫ t in Set.Ioi (0 : ℝ), |Real.log t| * Real.exp (-t) ≤ 2 := by
  let f : ℝ → ℝ := fun t => |Real.log t| * Real.exp (-t)
  have hf_meas : StronglyMeasurable f := by
    dsimp [f]
    exact ((continuous_abs.measurable.comp Real.measurable_log).mul
      (Real.measurable_exp.comp measurable_id.neg)).stronglyMeasurable
  have hneglog_int : IntegrableOn (fun t : ℝ => -Real.log t) (Set.Ioc 0 1) := by
    have hlog_int : IntegrableOn Real.log (Set.Ioc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        intervalIntegral.intervalIntegrable_log'
    exact hlog_int.neg
  have hlow_point (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      f t ≤ -Real.log t := by
    have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.1.le ht.2
    have hexp : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
    dsimp [f]
    rw [abs_of_nonpos hlog]
    exact mul_le_of_le_one_right (neg_nonneg.mpr hlog) hexp
  have hf_low : IntegrableOn f (Set.Ioc (0 : ℝ) 1) := by
    refine Integrable.mono_nonneg hneglog_int hf_meas.aestronglyMeasurable.restrict
      (ae_of_all _ fun t => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact ae_of_all _ hlow_point
  have hlow_value :
      ∫ t : ℝ in Set.Ioc 0 1, -Real.log t = 1 := by
    calc
      (∫ t : ℝ in Set.Ioc 0 1, -Real.log t) =
          ∫ t : ℝ in (0 : ℝ)..1, -Real.log t := by
        rw [intervalIntegral.integral_of_le zero_le_one]
      _ = -(∫ t : ℝ in (0 : ℝ)..1, Real.log t) := by
        rw [intervalIntegral.integral_neg]
      _ = 1 := by simp
  have hlow : ∫ t : ℝ in Set.Ioc 0 1, f t ≤ 1 := by
    calc
      (∫ t : ℝ in Set.Ioc 0 1, f t) ≤
          ∫ t : ℝ in Set.Ioc 0 1, -Real.log t :=
        setIntegral_mono_on hf_low hneglog_int measurableSet_Ioc hlow_point
      _ = 1 := hlow_value
  have hderiv (t : ℝ) :
      HasDerivAt (fun x : ℝ => -x * Real.exp (-x))
        ((t - 1) * Real.exp (-t)) t := by
    have hraw := (hasDerivAt_id t).neg.mul (hasDerivAt_id t).neg.exp
    refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with x
      rfl
    · simp
      ring
  have htop : Filter.Tendsto (fun t : ℝ => -t * Real.exp (-t)) Filter.atTop (nhds 0) := by
    simpa [pow_one] using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).neg
  have hmajor_high : IntegrableOn
      (fun t : ℝ => (t - 1) * Real.exp (-t)) (Set.Ioi 1) := by
    exact integrableOn_Ioi_deriv_of_nonneg'
      (a := (1 : ℝ)) (l := (0 : ℝ))
      (g := fun t : ℝ => -t * Real.exp (-t))
      (g' := fun t : ℝ => (t - 1) * Real.exp (-t))
      (fun t _ => hderiv t)
      (fun t ht => mul_nonneg (sub_nonneg.mpr ht.le) (Real.exp_nonneg _)) htop
  have hhigh_point (t : ℝ) (ht : t ∈ Set.Ioi (1 : ℝ)) :
      f t ≤ (t - 1) * Real.exp (-t) := by
    have htpos : 0 < t := zero_lt_one.trans ht
    have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht.le
    have hlog_le : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos htpos
    dsimp [f]
    rw [abs_of_nonneg hlog_nonneg]
    exact mul_le_mul_of_nonneg_right hlog_le (Real.exp_nonneg _)
  have hf_high : IntegrableOn f (Set.Ioi (1 : ℝ)) := by
    refine Integrable.mono_nonneg hmajor_high hf_meas.aestronglyMeasurable.restrict
      (ae_of_all _ fun t => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ hhigh_point
  have hmajor_value :
      ∫ t : ℝ in Set.Ioi 1, (t - 1) * Real.exp (-t) = Real.exp (-1) := by
    calc
      (∫ t : ℝ in Set.Ioi 1, (t - 1) * Real.exp (-t)) =
          0 - ((-(1 : ℝ)) * Real.exp (-(1 : ℝ))) :=
        integral_Ioi_of_hasDerivAt_of_tendsto'
          (fun t _ => hderiv t) hmajor_high htop
      _ = Real.exp (-1) := by ring
  have hhigh :
      ∫ t : ℝ in Set.Ioi 1, f t ≤ Real.exp (-1) := by
    calc
      (∫ t : ℝ in Set.Ioi 1, f t) ≤
          ∫ t : ℝ in Set.Ioi 1, (t - 1) * Real.exp (-t) :=
        setIntegral_mono_on hf_high hmajor_high measurableSet_Ioi hhigh_point
      _ = Real.exp (-1) := hmajor_value
  change (∫ t : ℝ in Set.Ioi 0, f t) ≤ 2
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hf_low hf_high]
  have hexp_one : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  linarith

/-- The off-diagonal single-context bound, in nats:
`I(U;Z ∣ b,g) ≤ C + ln 8 − γ`, where `C = D(ν ‖ q_g)`.
The last step is `ln((C+4)/4) ≤ C`, i.e. `e^C ≥ 1 + C/4` for `C ≥ 0`.-/
theorem offdiag_context_bound_nats {C : ℝ} (hC : 0 ≤ C) :
    Real.log (2 * Real.exp 1 * (C + 4)) - (1 + Real.eulerMascheroniConstant)
      ≤ C + cZero := by
  have hxpos : 0 < (C + 4) / 4 := div_pos (by linarith) (by norm_num)
  have hxexp : (C + 4) / 4 ≤ Real.exp C := by
    calc
      (C + 4) / 4 ≤ C + 1 := by linarith
      _ ≤ Real.exp C := by simpa [add_comm] using Real.add_one_le_exp C
  have hlogx : Real.log ((C + 4) / 4) ≤ C :=
    (Real.log_le_iff_le_exp hxpos).2 hxexp
  have hfactor :
      2 * Real.exp 1 * (C + 4) =
        (Real.exp 1 * 8) * ((C + 4) / 4) := by ring
  rw [hfactor, Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (by norm_num)) hxpos.ne',
    Real.log_mul (Real.exp_ne_zero _) (by norm_num), Real.log_exp]
  unfold cZero
  linarith

/-- The arithmetic core of the diagonal case: with
`C = −E_ν ln R ≥ 0` and `E_ν(1/R) ≤ 1/P`, the golden formula against
`Exp(mean P)` gives `P · I(U;Z ∣ g,g) ≤ P·[−C + E_ν(1/R) − 1] ≤ 1 − P`.
Stated as the scalar inequality; wiring it to a context depends on how the
seed-conditioned informations are modelled (see `stoch_to_det.Quotient`).-/
theorem diag_context_arith {P C invR : ℝ} (hP : 0 < P) (hC : 0 ≤ C)
    (hinv : invR ≤ 1 / P) :
    P * (-C + invR - 1) ≤ 1 - P := by
  have hinv' : P * invR ≤ 1 := by
    calc
      P * invR ≤ P * (1 / P) := mul_le_mul_of_nonneg_left hinv hP.le
      _ = 1 := by field_simp [hP.ne']
  have hPC : 0 ≤ P * C := mul_nonneg hP.le hC
  nlinarith

private lemma exponentialPDF_toReal {r : ℝ} (hr : 0 < r) (x : ℝ) :
    (exponentialPDF r x).toReal =
      if 0 ≤ x then r * Real.exp (-(r * x)) else 0 := by
  rw [exponentialPDF_eq, ENNReal.toReal_ofReal]
  split_ifs with hx
  · exact mul_nonneg hr.le (Real.exp_nonneg _)
  · exact le_rfl

private lemma integrable_id_expMeasure {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (expMeasure r) := by
  have hpdf : Measurable (exponentialPDF r) :=
    (measurable_exponentialPDFReal r).ennreal_ofReal
  have hpdf_top : ∀ᵐ x : ℝ ∂volume, exponentialPDF r x < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  change Integrable (fun x : ℝ => x)
    (volume.withDensity (exponentialPDF r))
  rw [integrable_withDensity_iff hpdf hpdf_top]
  have hgamma : IntegrableOn
      (fun y : ℝ => Real.exp (-y) * y ^ ((2 : ℝ) - 1)) (Set.Ioi 0) := by
    simpa using (Real.GammaIntegral_convergent (s := (2 : ℝ)) (by norm_num))
  have hscaled : IntegrableOn
      (fun x : ℝ => Real.exp (-(r * x)) * (r * x) ^ ((2 : ℝ) - 1))
      (Set.Ioi 0) := by
    have hgamma' : IntegrableOn
        (fun y : ℝ => Real.exp (-y) * y ^ ((2 : ℝ) - 1))
        (Set.Ioi (r * 0)) := by simpa using hgamma
    exact (integrableOn_Ioi_comp_mul_left_iff
      (fun y : ℝ => Real.exp (-y) * y ^ ((2 : ℝ) - 1)) 0 hr).2 hgamma'
  have hmain : IntegrableOn
      (fun x : ℝ => x * (r * Real.exp (-(r * x)))) (Set.Ioi 0) := by
    refine hscaled.congr_fun (fun x hx => ?_) measurableSet_Ioi
    dsimp only
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    ring
  refine Integrable.congr (hmain.integrable_indicator measurableSet_Ioi)
    (ae_of_all _ fun x => ?_)
  by_cases hx : 0 < x
  · simp [exponentialPDF_toReal hr, hx, hx.le]
  · have hxle : x ≤ 0 := le_of_not_gt hx
    rcases hxle.eq_or_lt with hzero | hxneg
    · simp [hzero]
    · simp [exponentialPDF_toReal hr, hx, not_le.mpr hxneg]

private lemma integral_id_expMeasure {r : ℝ} (hr : 0 < r) :
    ∫ x : ℝ, x ∂(expMeasure r) = 1 / r := by
  have hpdf : Measurable (exponentialPDF r) :=
    (measurable_exponentialPDFReal r).ennreal_ofReal
  have hpdf_top : ∀ᵐ x : ℝ ∂volume, exponentialPDF r x < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  change (∫ x : ℝ, x ∂volume.withDensity (exponentialPDF r)) = 1 / r
  rw [integral_withDensity_eq_integral_toReal_smul hpdf hpdf_top]
  simp only [smul_eq_mul]
  calc
    (∫ x : ℝ, (exponentialPDF r x).toReal * x) =
        ∫ x : ℝ, Set.indicator (Set.Ioi (0 : ℝ))
          (fun x => r * (x ^ ((2 : ℝ) - 1) * Real.exp (-(r * x)))) x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : 0 < x
      · simp [Set.indicator, hx, exponentialPDF_toReal hr, hx.le,
          show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
        ring
      · have hxle : x ≤ 0 := le_of_not_gt hx
        rcases hxle.eq_or_lt with hzero | hxneg
        · simp [hzero]
        · simp [Set.indicator, hx, exponentialPDF_toReal hr, not_le.mpr hxneg]
    _ = ∫ x : ℝ in Set.Ioi 0,
        r * (x ^ ((2 : ℝ) - 1) * Real.exp (-(r * x))) := by
      rw [integral_indicator measurableSet_Ioi]
    _ = r * ∫ x : ℝ in Set.Ioi 0,
        x ^ ((2 : ℝ) - 1) * Real.exp (-(r * x)) := by
      rw [integral_const_mul]
    _ = 1 / r := by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hr]
      simp only [Real.rpow_two, Real.Gamma_ofNat_eq_factorial,
        Nat.factorial_one, Nat.cast_one, mul_one]
      field_simp [hr.ne']

private noncomputable def expRateRatio (r u x : ℝ) : ENNReal :=
  ENNReal.ofReal ((r / u) * Real.exp ((u - r) * x))

private lemma measurable_expRateRatio (r u : ℝ) :
    Measurable (expRateRatio r u) := by
  unfold expRateRatio
  fun_prop

private lemma expMeasure_eq_withDensity_expRateRatio {r u : ℝ}
    (hr : 0 < r) (hu : 0 < u) :
    expMeasure r = (expMeasure u).withDensity (expRateRatio r u) := by
  have hpdf : Measurable (exponentialPDF u) :=
    (measurable_exponentialPDFReal u).ennreal_ofReal
  change volume.withDensity (exponentialPDF r) =
    (volume.withDensity (exponentialPDF u)).withDensity (expRateRatio r u)
  rw [← withDensity_mul volume hpdf (measurable_expRateRatio r u)]
  apply withDensity_congr_ae
  filter_upwards with x
  change exponentialPDF r x = exponentialPDF u x * expRateRatio r u x
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx]
    unfold expRateRatio
    rw [← ENNReal.ofReal_mul (mul_nonneg hu.le (Real.exp_nonneg _))]
    congr 1
    rw [show
      (u * Real.exp (-(u * x))) *
          (r / u * Real.exp ((u - r) * x)) =
        (u * (r / u)) *
          (Real.exp (-(u * x)) * Real.exp ((u - r) * x)) by ring,
      ← Real.exp_add]
    have hexp : -(u * x) + (u - r) * x = -(r * x) := by ring
    rw [hexp]
    field_simp [hu.ne']
  · have hxneg : x < 0 := lt_of_not_ge hx
    rw [exponentialPDF_of_neg hxneg, exponentialPDF_of_neg hxneg]
    simp

/-- The KL between exponentials used by the diagonal case:
`D(Exp(mean s) ‖ Exp(mean q)) = ln(q/s) + s/q − 1` nats.-/
theorem klDiv_expMeasure {s q : ℝ} (hs : 0 < s) (hq : 0 < q) :
    (klDiv (expMeasure (1 / s)) (expMeasure (1 / q))).toReal
      = Real.log (q / s) + s / q - 1 := by
  have hrs : 0 < 1 / s := one_div_pos.mpr hs
  have hrq : 0 < 1 / q := one_div_pos.mpr hq
  letI : IsProbabilityMeasure (expMeasure (1 / s)) :=
    isProbabilityMeasure_expMeasure hrs
  letI : IsProbabilityMeasure (expMeasure (1 / q)) :=
    isProbabilityMeasure_expMeasure hrq
  have hmeasure := expMeasure_eq_withDensity_expRateRatio hrs hrq
  have hac : expMeasure (1 / s) ≪ expMeasure (1 / q) := by
    rw [hmeasure]
    exact withDensity_absolutelyContinuous _ _
  have hrn :
      (expMeasure (1 / s)).rnDeriv (expMeasure (1 / q)) =ᵐ[expMeasure (1 / q)]
        expRateRatio (1 / s) (1 / q) := by
    rw [hmeasure]
    exact Measure.rnDeriv_withDensity _
      (measurable_expRateRatio (1 / s) (1 / q))
  have hrateRatio : (1 / s) / (1 / q) = q / s := by
    field_simp [hs.ne', hq.ne']
  have hratioPos : 0 < (1 / s) / (1 / q) := div_pos hrs hrq
  have hllr :
      llr (expMeasure (1 / s)) (expMeasure (1 / q)) =ᵐ[expMeasure (1 / s)]
        fun x => Real.log (q / s) + (1 / q - 1 / s) * x := by
    filter_upwards [hac.ae_le hrn] with x hx
    rw [llr, hx]
    unfold expRateRatio
    rw [ENNReal.toReal_ofReal
      (mul_nonneg hratioPos.le (Real.exp_nonneg _)),
      Real.log_mul hratioPos.ne' (Real.exp_ne_zero _), Real.log_exp,
      hrateRatio]
  have haffine : Integrable
      (fun x : ℝ => Real.log (q / s) + (1 / q - 1 / s) * x)
      (expMeasure (1 / s)) :=
    (integrable_const _).add ((integrable_id_expMeasure hrs).const_mul _)
  have hllr_int : Integrable
      (llr (expMeasure (1 / s)) (expMeasure (1 / q)))
      (expMeasure (1 / s)) := by
    rwa [integrable_congr hllr]
  have _hfinite :
      klDiv (expMeasure (1 / s)) (expMeasure (1 / q)) ≠ ⊤ :=
    klDiv_ne_top hac hllr_int
  have hmass : expMeasure (1 / s) Set.univ = expMeasure (1 / q) Set.univ := by
    rw [(isProbabilityMeasure_expMeasure hrs).measure_univ,
      (isProbabilityMeasure_expMeasure hrq).measure_univ]
  have hreal : (expMeasure (1 / s)).real Set.univ = 1 := by
    rw [measureReal_def, (isProbabilityMeasure_expMeasure hrs).measure_univ]
    norm_num
  calc
    (klDiv (expMeasure (1 / s)) (expMeasure (1 / q))).toReal =
        ∫ x, llr (expMeasure (1 / s)) (expMeasure (1 / q)) x
          ∂(expMeasure (1 / s)) :=
      toReal_klDiv_of_measure_eq hac hmass
    _ = ∫ x, (Real.log (q / s) + (1 / q - 1 / s) * x)
          ∂(expMeasure (1 / s)) := integral_congr_ae hllr
    _ = Real.log (q / s) + (1 / q - 1 / s) * (1 / (1 / s)) := by
      rw [integral_add (integrable_const _) ((integrable_id_expMeasure hrs).const_mul _),
        integral_const_mul, integral_id_expMeasure hrs]
      simp only [integral_const, smul_eq_mul]
      rw [hreal, one_mul]
    _ = Real.log (q / s) + s / q - 1 := by
      field_simp [hs.ne', hq.ne']
      ring

/-- The form §11 consumes: `scalar ≤ K_sc (M + S)`,
where `K_sc = κ/c_* = (1 + ln 8 − γ) N` (the first branch of the `max`
dominates; the second is `≈ 2.75 × 10¹⁰`).-/
theorem scalar_bound_Ksc (R : RaceQuantities D K) :
    R.scalar ≤ Ksc * (D.M + K.Sinfo) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    calc
      Real.log 8 = Real.log ((2 : ℝ) ^ 3) := by norm_num
      _ = 3 * Real.log 2 := Real.log_pow _ _
  have hgamma : Real.eulerMascheroniConstant < 2 / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds
  have hlog2_lower := Real.log_two_gt_d9
  have hcharge_one :
      1 ≤ 1 + Real.log 8 - Real.eulerMascheroniConstant := by
    rw [hlog8]
    norm_num at hlog2_lower hgamma ⊢
    linarith
  have hkappa : 0 ≤ kappa := by
    rw [kappa]
    exact (div_pos (lt_of_lt_of_le (by norm_num) hcharge_one) hlog2).le
  have hS : 0 ≤ K.Sinfo := by
    unfold Clustering.Sinfo
    exact condMI_nonneg (replicaLaw_isPMF D) (fun u => K.cl u.2.1)
      (fun u => u.2.2.2) (fun u => K.cl u.1)
  have hdom : 1 + 2 / deltaStar ^ 2 ≤ (N : ℝ) := by
    norm_num [deltaStar, N]
  have hcoef :
      1 + kappa * (2 * Real.log 2 / deltaStar ^ 2) ≤ Ksc := by
    have hrewrite :
        kappa * (2 * Real.log 2 / deltaStar ^ 2) =
          (1 + Real.log 8 - Real.eulerMascheroniConstant) *
            (2 / deltaStar ^ 2) := by
      calc
        kappa * (2 * Real.log 2 / deltaStar ^ 2) =
            (kappa * Real.log 2) * (2 / deltaStar ^ 2) := by ring
        _ = (1 + Real.log 8 - Real.eulerMascheroniConstant) *
              (2 / deltaStar ^ 2) := by rw [kappa_mul_log_two]
    rw [hrewrite, Ksc]
    calc
      1 + (1 + Real.log 8 - Real.eulerMascheroniConstant) *
            (2 / deltaStar ^ 2) ≤
          (1 + Real.log 8 - Real.eulerMascheroniConstant) *
            (1 + 2 / deltaStar ^ 2) := by nlinarith
      _ ≤ (1 + Real.log 8 - Real.eulerMascheroniConstant) * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hdom (le_trans (by norm_num) hcharge_one)
  calc
    R.scalar ≤ K.Sinfo + kappa * K.dMis := R.scalar_le
    _ ≤ K.Sinfo + kappa *
          (D.M / cStar + 2 * Real.log 2 / deltaStar ^ 2 * K.Sinfo) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left (mismatch_charge K) hkappa)
    _ = (kappa / cStar) * D.M +
          (1 + kappa * (2 * Real.log 2 / deltaStar ^ 2)) * K.Sinfo := by ring
    _ = Ksc * D.M +
          (1 + kappa * (2 * Real.log 2 / deltaStar ^ 2)) * K.Sinfo := by
      rw [kappa_div_cStar]
    _ ≤ Ksc * D.M + Ksc * K.Sinfo :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcoef hS)
    _ = Ksc * (D.M + K.Sinfo) := by ring

end stoch_to_det
