import Tengoku.Twinprime.TwinPrime.Analytic.MellinRampKernel
import Tengoku.Twinprime.TwinPrime.Analytic.SmoothedPartialSum
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionLogDerivative
import Tengoku.Seed.MeasureTheory.Integral.DominatedConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual Mellin inversion of smoothed character sums

Absolute convergence on a positive vertical line allows the Dirichlet
series to pass through the inverse Mellin integral. The majorant has
summable norm integrals. Specializing the coefficients to the character
twist of von Mangoldt gives the actual logarithmic-derivative formula,
including principal characters and modulus one.
-/

noncomputable section

open MeasureTheory Complex Finset Filter
open scoped Topology

namespace TwinPrime.Analytic

private def mellinSeriesTerm (a : ℕ → ℂ) (c u : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (u : ℂ) ^ (-((c : ℂ) + t * I)) *
    LSeries.term a ((c : ℂ) + t * I) n * mellinRampKernel ((c : ℂ) + t * I)

/--
@isnad1 id=eq.0h4v.s5.ff2666420bbf from=translated src=- shape=69f183d3 vocab=9099fc57
-/
theorem norm_LSeries_term_vertical_eq (a : ℕ → ℂ) (c t : ℝ) (n : ℕ) :
    ‖LSeries.term a ((c : ℂ) + t * I) n‖ = ‖LSeries.term a (c : ℂ) n‖ := by
  simp [LSeries.norm_term_eq]

private theorem norm_mellinSeriesTerm (a : ℕ → ℂ) (c u : ℝ) (hu : 0 < u)
    (n : ℕ) (t : ℝ) :
    ‖mellinSeriesTerm a c u n t‖ =
      (u ^ (-c) * ‖LSeries.term a (c : ℂ) n‖) *
        ‖mellinRampKernel ((c : ℂ) + t * I)‖ := by
  simp only [mellinSeriesTerm, norm_mul, norm_LSeries_term_vertical_eq,
    Complex.norm_cpow_eq_rpow_re_of_pos hu]
  simp

private theorem continuous_LSeries_term_vertical (a : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term a ((c : ℂ) + t * I) n) := by
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero]
    exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    have hline : Continuous (fun t : ℝ => (c : ℂ) + t * I) := by fun_prop
    exact continuous_const.div (hline.const_cpow (.inl (by exact_mod_cast hn)))
      (fun t => by simp [Complex.cpow_eq_zero_iff, hn])

private theorem integrable_mellinSeriesTerm (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c)
    (u : ℝ) (hu : 0 < u) (n : ℕ) : Integrable (mellinSeriesTerm a c u n) := by
  have hpow : Continuous (fun t : ℝ => (u : ℂ) ^ (-((c : ℂ) + t * I))) :=
    (show Continuous (fun t : ℝ => -((c : ℂ) + t * I)) by fun_prop).const_cpow
      (.inl (by exact_mod_cast hu.ne'))
  have hmeas : AEStronglyMeasurable (mellinSeriesTerm a c u n) :=
    (hpow.aestronglyMeasurable.mul (continuous_LSeries_term_vertical a c n).aestronglyMeasurable).mul
      (verticalIntegrable_mellinRampKernel c hc).aestronglyMeasurable
  exact ((verticalIntegrable_mellinRampKernel c hc).norm.const_mul
    (u ^ (-c) * ‖LSeries.term a (c : ℂ) n‖)).mono' hmeas
    (.of_forall fun t => (norm_mellinSeriesTerm a c u hu n t).le)

private theorem summable_integral_norm_mellinSeriesTerm (a : ℕ → ℂ) (c : ℝ)
    (ha : LSeriesSummable a (c : ℂ)) (u : ℝ) (hu : 0 < u) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖mellinSeriesTerm a c u n t‖) := by
  have h := (ha.norm.mul_left (u ^ (-c))).mul_right
    (∫ t : ℝ, ‖mellinRampKernel ((c : ℂ) + t * I)‖)
  apply h.congr
  intro n
  simp_rw [norm_mellinSeriesTerm a c u hu n, integral_const_mul]

private theorem hasSum_mellinSeriesTerm (a : ℕ → ℂ) (c : ℝ)
    (ha : LSeriesSummable a (c : ℂ)) (u t : ℝ) :
    HasSum (fun n => mellinSeriesTerm a c u n t)
      ((u : ℂ) ^ (-((c : ℂ) + t * I)) *
        (LSeries a ((c : ℂ) + t * I) * mellinRampKernel ((c : ℂ) + t * I))) := by
  have h := (ha.of_re_le_re (by simp : (c : ℂ).re ≤ ((c : ℂ) + t * I).re)).hasSum
  simpa only [mellinSeriesTerm, LSeries, mul_assoc] using
    (h.mul_left ((u : ℂ) ^ (-((c : ℂ) + t * I)))).mul_right
      (mellinRampKernel ((c : ℂ) + t * I))

private theorem integral_mellinSeriesTerm_sum (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c)
    (ha : LSeriesSummable a (c : ℂ)) (u : ℝ) (hu : 0 < u) :
    (∑' n : ℕ, ∫ t : ℝ, mellinSeriesTerm a c u n t) =
      ∫ t : ℝ, (u : ℂ) ^ (-((c : ℂ) + t * I)) *
        (LSeries a ((c : ℂ) + t * I) * mellinRampKernel ((c : ℂ) + t * I)) := by
  rw [integral_tsum_of_summable_integral_norm
    (integrable_mellinSeriesTerm a c hc u hu) (summable_integral_norm_mellinSeriesTerm a c ha u hu)]
  apply integral_congr_ae
  exact .of_forall fun t => (hasSum_mellinSeriesTerm a c ha u t).tsum_eq

/-- Absolute convergence of the Dirichlet series and the vertical ramp
kernel imply integrability of the full inverse Mellin integrand.
@isnad1 id=integrab.3h3v.s7.696355fc3ca2 from=translated src=- shape=3bd9ca57 vocab=19645820
-/
theorem integrable_LSeries_mellinRamp_integrand (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c)
    (ha : LSeriesSummable a (c : ℂ)) (u : ℝ) (hu : 0 < u) :
    Integrable (fun t : ℝ => (u : ℂ) ^ (-((c : ℂ) + t * I)) *
      (LSeries a ((c : ℂ) + t * I) * mellinRampKernel ((c : ℂ) + t * I))) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (u : ℂ) ^ (-((c : ℂ) + t * I)) *
      (LSeries a ((c : ℂ) + t * I) * mellinRampKernel ((c : ℂ) + t * I))) := by
    apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℕ)
      (f := fun N t => ∑ n ∈ range N, mellinSeriesTerm a c u n t)
    · intro N
      apply (Finset.aestronglyMeasurable_sum (μ := volume) (range N) (fun n _ =>
        (integrable_mellinSeriesTerm a c hc u hu n).aestronglyMeasurable)).congr
      exact .of_forall fun t => by simp only [Finset.sum_apply]
    · exact .of_forall fun t => (hasSum_mellinSeriesTerm a c ha u t).tendsto_sum_nat
  apply ((verticalIntegrable_mellinRampKernel c hc).norm.const_mul
    (u ^ (-c) * ∑' n, ‖LSeries.term a (c : ℂ) n‖)).mono' hmeas
  apply Eventually.of_forall
  intro t
  have hnorm : ‖LSeries a ((c : ℂ) + t * I)‖ ≤ ∑' n, ‖LSeries.term a (c : ℂ) n‖ := by
    apply (norm_tsum_le_tsum_norm
      (ha.of_re_le_re (by simp : (c : ℂ).re ≤ ((c : ℂ) + t * I).re)).norm).trans_eq
    exact tsum_congr fun n => norm_LSeries_term_vertical_eq a c t n
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu]
  simp only [neg_re, add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
    mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ u ^ (-c) * ((∑' n, ‖LSeries.term a (c : ℂ) n‖) *
        ‖mellinRampKernel ((c : ℂ) + t * I)‖) := by gcongr
    _ = _ := by ring

private theorem mellinSeriesTerm_eq_rescaled {a : ℕ → ℂ} (c u : ℝ) (hu : 0 < u)
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    mellinSeriesTerm a c u n t = a n *
      (((n : ℝ) * u : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) *
        mellinRampKernel ((c : ℂ) + t * I) := by
  rw [mellinSeriesTerm, LSeries.term_of_ne_zero hn, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) hu.le]
  simp only [Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]
  ring

private theorem scaled_integral_mellinSeriesTerm (a : ℕ → ℂ)
    (c : ℝ) (hc : 0 < c) (u : ℝ) (hu : 0 < u) (n : ℕ) :
    (1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ, mellinSeriesTerm a c u n t) =
      if n = 0 then 0 else a n * mellinRamp ((n : ℝ) * u) := by
  by_cases hn : n = 0
  · subst n
    simp [mellinSeriesTerm]
  · rw [ite_eq_right hn]
    have hnu : 0 < (n : ℝ) * u := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hu
    calc
      _ = (1 / (2 * Real.pi) : ℝ) •
          (a n * ∫ t : ℝ, (((n : ℝ) * u : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) *
            mellinRampKernel ((c : ℂ) + t * I)) := by
        congr 1
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact .of_forall fun t => by rw [mellinSeriesTerm_eq_rescaled c u hu hn t]; ring
      _ = a n * mellinInv c mellinRampKernel ((n : ℝ) * u) := by
        simp only [mellinInv, smul_eq_mul, Complex.real_smul]
        ring
      _ = _ := by rw [mellinInv_mellinRampKernel c hc _ hnu]

/-- Termwise Mellin inversion with an integrable, absolutely summable
majorant. The zero coefficient is excluded exactly as in `LSeries.term`.
@isnad1 id=eq.3h3v.s7.111572b96673 from=translated src=- shape=3ddcf00a vocab=3220357d
-/
theorem mellinInv_LSeries_mul_mellinRampKernel (a : ℕ → ℂ)
    (c : ℝ) (hc : 0 < c) (ha : LSeriesSummable a (c : ℂ))
    (u : ℝ) (hu : 0 < u) :
    mellinInv c (fun s => LSeries a s * mellinRampKernel s) u =
      ∑' n : ℕ, if n = 0 then 0 else a n * mellinRamp ((n : ℝ) * u) := by
  unfold mellinInv
  simp only [smul_eq_mul]
  rw [← integral_mellinSeriesTerm_sum a c hc ha u hu]
  change (1 / (2 * Real.pi) : ℝ) • (∑' n : ℕ, ∫ t : ℝ, mellinSeriesTerm a c u n t) = _
  rw [← tsum_const_smul'']
  exact tsum_congr (scaled_integral_mellinSeriesTerm a c hc u hu)

/--
@isnad1 id=eq.3h3v.s6.8f33e8b9d213 from=translated src=- shape=2d4b9bdb vocab=b72da184
-/
theorem mellinInv_LSeries_mul_mellinRampKernel_eq_weightedPartialSum
    (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c) (ha : LSeriesSummable a (c : ℂ))
    (x : ℝ) (hx : 0 < x) :
    mellinInv c (fun s => LSeries a s * mellinRampKernel s) (1 / x) = weightedPartialSum a x := by
  rw [mellinInv_LSeries_mul_mellinRampKernel a c hc ha (1 / x) (by positivity)]
  rw [tsum_eq_sum (s := Icc 1 ⌊x⌋₊)]
  · unfold weightedPartialSum
    apply sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp (mem_Icc.mp hn).2
    rw [ite_eq_right hn0, mellinRamp_eq_of_le_one _ (by
      simpa only [one_div, div_eq_mul_inv, one_mul] using (div_le_one hx).mpr hnx)]
    push_cast
    congr 2
    ring
  · intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hlarge : ⌊x⌋₊ < n := by simp only [mem_Icc, not_and] at hn; exact Nat.lt_of_not_ge (hn (by omega))
      have hxn : x < (n : ℝ) := (Nat.floor_lt hx.le).mp hlarge
      rw [ite_eq_right hn0, mellinRamp_eq_zero_of_one_le _ (by
        simpa only [one_div, div_eq_mul_inv, one_mul] using (one_le_div hx).mpr hxn.le), mul_zero]

/--
@isnad1 id=vertical.2h2v.s5.e15d1dcbae1c from=translated src=- shape=c556d28a vocab=0722a6a6
-/
theorem verticalIntegrable_LSeries_mul_mellinRampKernel (a : ℕ → ℂ)
    (c : ℝ) (hc : 0 < c) (ha : LSeriesSummable a (c : ℂ)) :
    VerticalIntegrable (fun s => LSeries a s * mellinRampKernel s) c := by
  simpa [Complex.VerticalIntegrable] using
    integrable_LSeries_mellinRamp_integrand a c hc ha 1 (by norm_num)

private theorem mangoldt_LSeriesSummable_of_mass {q : ℕ}
    (χ : DirichletCharacter ℂ q) (c : ℝ) (hc : 1 < c) :
    LSeriesSummable (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) := by
  exact (summable_mangoldtDirichletMass hc).of_norm_bounded
    (fun n => by simpa using norm_twist_vonMangoldt_term_le χ (c : ℂ) n)

/-- The actual logarithmic-derivative kernel is vertically integrable;
the modulus and character may be principal or imprimitive.
@isnad1 id=vertical.1h3v.s6.28636aee730f from=translated src=- shape=ad9a5322 vocab=9ccd7320
-/
theorem verticalIntegrable_mangoldt_mellinRampKernel {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (c : ℝ) (hc : 1 < c) :
    VerticalIntegrable (fun s =>
      (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
        mellinRampKernel s) c := by
  apply (verticalIntegrable_LSeries_mul_mellinRampKernel
    (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) c (by linarith)
    (mangoldt_LSeriesSummable_of_mass χ c hc)).congr
  filter_upwards [] with t
  rw [neg_LFunction_logDerivative_eq_twist χ (by simpa using hc)]

/--
@isnad1 id=integrab.2h4v.s7.1553bb329be6 from=translated src=- shape=3f4437e8 vocab=40878377
-/
theorem integrable_mangoldt_mellinRamp_integrand {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (c : ℝ) (hc : 1 < c) (u : ℝ) (hu : 0 < u) :
    Integrable (fun t : ℝ => (u : ℂ) ^ (-((c : ℂ) + t * I)) *
      ((-deriv (DirichletCharacter.LFunction χ) ((c : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((c : ℂ) + t * I)) *
          mellinRampKernel ((c : ℂ) + t * I))) := by
  apply (integrable_LSeries_mellinRamp_integrand
    (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) c (by linarith)
    (mangoldt_LSeriesSummable_of_mass χ c hc) u hu).congr
  filter_upwards [] with t
  rw [neg_LFunction_logDerivative_eq_twist χ (by simpa using hc)]

/-- Smoothed von Mangoldt-character sums equal the actual inverse Mellin
integral of `(-L'/L)/(s(s+1))`, without a supplied analytic hypothesis.
@isnad1 id=eq.2h4v.s7.14eb8c386fc1 from=translated src=- shape=62adc492 vocab=6fae6c01
-/
theorem weighted_mangoldt_sum_eq_mellinInv {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (c : ℝ) (hc : 1 < c) (x : ℝ) (hx : 0 < x) :
    weightedPartialSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x =
      mellinInv c (fun s =>
        (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
          mellinRampKernel s) (1 / x) := by
  rw [← mellinInv_LSeries_mul_mellinRampKernel_eq_weightedPartialSum
    (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) c (by linarith)
    (mangoldt_LSeriesSummable_of_mass χ c hc) x hx]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [neg_LFunction_logDerivative_eq_twist χ (by simpa using hc)]

/--
@isnad1 id=eq.2h4v.s8.d5ca783b9afa from=translated src=- shape=df146c2c vocab=5673d3c4
-/
theorem sum_Icc_mangoldt_ramp_eq_mellinInv {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (c : ℝ) (hc : 1 < c) (x : ℝ) (hx : 0 < x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) *
      (1 - (n : ℂ) / (x : ℂ))) =
      mellinInv c (fun s =>
        (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
          mellinRampKernel s) (1 / x) :=
  weighted_mangoldt_sum_eq_mellinInv χ c hc x hx

end TwinPrime.Analytic
