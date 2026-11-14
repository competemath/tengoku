import Tengoku.Piirrationalitymeasure.Formalization.PositivePowerSeries
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientMoments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tilted probability laws for the general generating function in (6.66). -/

namespace PiIrrationality.PositivePower

open PowerSeries MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def probability (u v d : ℕ) (x : ℝ) (n k : ℕ) : ℝ :=
  (coeff k (series u v d ^ n) : ℚ) * x ^ k / realValue u v d x ^ n

variable (u v : ℕ) {d : ℕ} (hd : 0 < d)

include hd in
/--
@isnad1 id=le.3h6v.s5.2a297128e3df from=translated src=- shape=b46c280f vocab=43e1517b
-/
theorem probability_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n k : ℕ) :
    0 ≤ probability u v d x n k :=
  div_nonneg (mul_nonneg (by exact_mod_cast series_pow_coeff_nonneg u v hd n k)
    (pow_nonneg hx0 _)) (pow_nonneg (realValue_pos u v d hx0 hx1).le _)

include hd in
/--
@isnad1 id=lt.4h6v.s6.ea8b08cd7ba9 from=translated src=- shape=03db2f21 vocab=642e5970
-/
theorem probability_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < probability u v d x n k :=
  div_pos (mul_pos (by exact_mod_cast series_pow_coeff_pos u v hd hn k)
    (pow_pos hx0 _)) (pow_pos (realValue_pos u v d hx0.le hx1) _)

include hd in
/--
@isnad1 id=hassum.3h5v.s6.e52c089b203b from=translated src=- shape=0f44fd77 vocab=96b4b21f
-/
theorem probability_hasSum {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    HasSum (probability u v d x n) 1 := by
  convert! (series_pow_hasSum_real u v hd hx0 hx1 n).div_const
    (realValue u v d x ^ n) using 1
  exact (div_self (pow_ne_zero _ (realValue_pos u v d hx0 hx1).ne')).symm

noncomputable def law (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (probability u v d x n k), by
    have h := probability_hasSum u v hd hx0 hx1 n
    have ht := ENNReal.ofReal_tsum_of_nonneg
      (probability_nonneg u v hd hx0 hx1 n) h.summable
    rw [h.tsum_eq, ENNReal.ofReal_one] at ht
    exact ht ▸ ENNReal.summable.hasSum⟩

/--
@isnad1 id=eq.3h6v.s6.61007e33d4b9 from=translated src=- shape=b3ebd3e6 vocab=7c2c6560
-/
theorem law_toReal {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n k : ℕ) :
    (law u v hd x hx0 hx1 n k).toReal = probability u v d x n k :=
  ENNReal.toReal_ofReal (probability_nonneg u v hd hx0 hx1 n k)

/--
@isnad1 id=eq.4h5v.s6.8d26398aa8fd from=translated src=- shape=003ea1a5 vocab=7c037421
-/
theorem law_full_support {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {n : ℕ} (hn : 0 < n) : (law u v hd x hx0.le hx1 n).support = Set.univ := by
  ext k
  simp only [PMF.mem_support_iff, Set.mem_univ, iff_true]
  exact (ENNReal.ofReal_pos.mpr (probability_pos u v hd hx0 hx1 hn k)).ne'

/--
@isnad1 id=eq.2h7v.s6.18484806e691 from=translated src=- shape=28df94ce vocab=54deafa3
-/
theorem probability_convolution {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n m k : ℕ) :
    probability u v d x (n + m) k =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        probability u v d x n p.1 * probability u v d x m p.2 := by
  unfold probability
  rw [pow_add (series u v d), coeff_mul, Rat.cast_sum, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hk := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [Rat.cast_mul, ← hk, pow_add, pow_add]
  field_simp [(realValue_pos u v d hx0 hx1).ne']

/--
@isnad1 id=eq.2h6v.s7.a58a59fda49e from=translated src=- shape=add07f53 vocab=6434a66c
-/
theorem probability_extraction {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (n k : ℕ) :
    (↑(coeff k (series u v d ^ n)) : ℝ) =
      realValue u v d x ^ n / x ^ k * probability u v d x n k := by
  rw [probability]
  field_simp [hx0.ne', (realValue_pos u v d hx0.le hx1).ne']

include hd in
/--
@isnad1 id=hassum.3h6v.s7.360d818fb83c from=translated src=- shape=5f2b7b08 vocab=9595d53a
-/
theorem probability_exponential_sum {x : ℝ} (hx0 : 0 ≤ x)
    (n : ℕ) (t : ℝ) (ht : x * Real.exp t < 1) :
    HasSum (fun k => probability u v d x n k * Real.exp ((k : ℝ) * t))
      (realValue u v d (x * Real.exp t) ^ n / realValue u v d x ^ n) := by
  have h := (series_pow_hasSum_real u v hd
    (mul_nonneg hx0 (Real.exp_pos t).le) ht n).div_const (realValue u v d x ^ n)
  convert! h using 1
  ext k
  rw [Real.exp_nat_mul, mul_pow]
  dsimp [probability]
  ring

/--
@isnad1 id=integrab.4h5v.s6.67af5347056c from=translated src=- shape=665b869e vocab=7317b3f0
-/
theorem law_integrable_exp {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (t : ℝ) (ht : x * Real.exp t < 1) :
    Integrable (fun k : ℕ => Real.exp (t * (k : ℝ)))
      (law u v hd x hx0 hx1 1).toMeasure := by
  apply pmf_nat_integrable_of_summable
  simpa only [law_toReal, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm t]
    using (probability_exponential_sum u v hd hx0 1 t ht).summable

/--
@isnad1 id=eq.4h5v.s6.09cb78c17453 from=translated src=- shape=bffce518 vocab=de256b2c
-/
theorem law_mgf {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (t : ℝ) (ht : x * Real.exp t < 1) :
    mgf (fun k : ℕ => (k : ℝ)) (law u v hd x hx0 hx1 1).toMeasure t =
      realValue u v d (x * Real.exp t) / realValue u v d x := by
  rw [mgf, PMF.integral_eq_tsum _ _ (law_integrable_exp u v hd hx0 hx1 t ht)]
  simpa only [law_toReal, smul_eq_mul, mul_comm t, pow_one] using
    (probability_exponential_sum u v hd hx0 1 t ht).tsum_eq

/--
@isnad1 id=mem.4h5v.s6.a1798393596c from=translated src=- shape=a65f1cbd vocab=dcef99fe
-/
theorem law_interior_integrableExpSet {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    {t : ℝ} (ht : x * Real.exp t < 1) :
    t ∈ interior (integrableExpSet (fun k : ℕ => (k : ℝ))
      (law u v hd x hx0 hx1 1).toMeasure) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hc : Continuous (fun s : ℝ => x * Real.exp s) := by fun_prop
  filter_upwards [hc.continuousAt.eventually (gt_mem_nhds ht)] with s hs
  exact law_integrable_exp u v hd hx0 hx1 s hs

end PiIrrationality.PositivePower
