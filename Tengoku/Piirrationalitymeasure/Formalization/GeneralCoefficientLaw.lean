import Tengoku.Piirrationalitymeasure.Formalization.LatticeLocalLimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tilted coefficient laws for arbitrary nonnegative real power series. -/

namespace PiIrrationality

open PowerSeries MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem scalarSeries_hasSum_mul {K : Type*} [RCLike K] {f g : PowerSeries K} {z u v : K}
    (hf : HasSum (fun k => coeff k f * z ^ k) u)
    (hg : HasSum (fun k => coeff k g * z ^ k) v) :
    HasSum (fun k => coeff k (f * g) * z ^ k) (u * v) := by
  have hfn := summable_norm_iff.mpr hf.summable
  have hgn := summable_norm_iff.mpr hg.summable
  have h := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn,
    hf.tsum_eq, hg.tsum_eq] at h
  convert! h using 1
  ext k
  rw [coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [mul_mul_mul_comm, ← pow_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hp]

theorem scalarSeries_hasSum_pow {K : Type*} [RCLike K] {f : PowerSeries K} {z u : K}
    (hf : HasSum (fun k => coeff k f * z ^ k) u) (n : ℕ) :
    HasSum (fun k => coeff k (f ^ n) * z ^ k) (u ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, coeff_one, ite_mul, one_mul, zero_mul]
    simpa using (hasSum_single (f := fun k : ℕ => if k = 0 then z ^ k else 0) 0
      (by intro k hk; simp [hk]))
  | succ n ih => simpa only [pow_succ] using scalarSeries_hasSum_mul ih hf

namespace GeneralCoefficient

variable (F : PowerSeries ℝ)

theorem pow_coeff_nonneg (hF : ∀ k, 0 ≤ coeff k F) (n k : ℕ) : 0 ≤ coeff k (F ^ n) := by
  induction n generalizing k with
  | zero => simp only [pow_zero, coeff_one]; split_ifs <;> positivity
  | succ n ih =>
    rw [pow_succ, coeff_mul]
    exact Finset.sum_nonneg fun p _ => mul_nonneg (ih p.1) (hF p.2)

noncomputable def probability (x value : ℝ) (n k : ℕ) : ℝ :=
  coeff k (F ^ n) * x ^ k / value ^ n

theorem probability_nonneg (hF : ∀ k, 0 ≤ coeff k F) {x value : ℝ}
    (hx : 0 ≤ x) (hvalue : 0 < value) (n k : ℕ) : 0 ≤ probability F x value n k :=
  div_nonneg (mul_nonneg (pow_coeff_nonneg F hF n k) (pow_nonneg hx _))
    (pow_nonneg hvalue.le _)

theorem probability_hasSum {x value : ℝ} (hvalue : 0 < value)
    (hseries : HasSum (fun k => coeff k F * x ^ k) value) (n : ℕ) :
    HasSum (probability F x value n) 1 := by
  convert! (scalarSeries_hasSum_pow hseries n).div_const (value ^ n) using 1
  exact (div_self (pow_ne_zero _ hvalue.ne')).symm

noncomputable def law (hF : ∀ k, 0 ≤ coeff k F) (x value : ℝ)
    (hx : 0 ≤ x) (hvalue : 0 < value)
    (hseries : HasSum (fun k => coeff k F * x ^ k) value) (n : ℕ) : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (probability F x value n k), by
    have h := probability_hasSum F hvalue hseries n
    have ht := ENNReal.ofReal_tsum_of_nonneg
      (probability_nonneg F hF hx hvalue n) h.summable
    rw [h.tsum_eq, ENNReal.ofReal_one] at ht
    exact ht ▸ ENNReal.summable.hasSum⟩

theorem law_toReal (hF : ∀ k, 0 ≤ coeff k F) {x value : ℝ}
    (hx : 0 ≤ x) (hvalue : 0 < value)
    (hseries : HasSum (fun k => coeff k F * x ^ k) value) (n k : ℕ) :
    (law F hF x value hx hvalue hseries n k).toReal = probability F x value n k :=
  ENNReal.toReal_ofReal (probability_nonneg F hF hx hvalue n k)

theorem law_support (hF : ∀ k, 0 ≤ coeff k F) {x value : ℝ}
    (hx : 0 < x) (hvalue : 0 < value)
    (hseries : HasSum (fun k => coeff k F * x ^ k) value) :
    (law F hF x value hx.le hvalue hseries 1).support =
      {k : ℕ | coeff k F ≠ 0} := by
  ext k
  rw [PMF.mem_support_iff]
  change ENNReal.ofReal (probability F x value 1 k) ≠ 0 ↔ coeff k F ≠ 0
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le,
    probability, pow_one, pow_one, div_pos_iff_of_pos_right hvalue,
    mul_pos_iff_of_pos_right (pow_pos hx _)]
  exact lt_iff_le_and_ne.trans (by simp [hF k, eq_comm])

theorem probability_extraction {x value : ℝ} (hx : 0 < x) (hvalue : 0 < value) (n k : ℕ) :
    coeff k (F ^ n) = value ^ n / x ^ k * probability F x value n k := by
  rw [probability]
  field_simp [hx.ne', hvalue.ne']

theorem complex_series_summable (hF : ∀ k, 0 ≤ coeff k F) {x value : ℝ}
    (hx : 0 ≤ x) (hseries : HasSum (fun k => coeff k F * x ^ k) value) (t : ℝ) :
    Summable (fun k => ((coeff k F : ℝ) : ℂ) *
      ((x : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) ^ k) := by
  apply summable_norm_iff.mp
  simpa only [norm_mul, norm_pow, coefficient_circle_norm hx, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (hF _)] using hseries.summable

theorem law_charFun_pow (hF : ∀ k, 0 ≤ coeff k F) {x value : ℝ}
    (hx : 0 ≤ x) (hvalue : 0 < value)
    (hseries : HasSum (fun k => coeff k F * x ^ k) value) (n : ℕ) (t : ℝ) :
    charFun ((law F hF x value hx hvalue hseries n).toMeasure.map
      (fun k : ℕ => (k : ℝ))) t =
      charFun ((law F hF x value hx hvalue hseries 1).toMeasure.map
        (fun k : ℕ => (k : ℝ))) t ^ n := by
  let z : ℂ := (x : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
  let S : ℂ := ∑' k, ((coeff k F : ℝ) : ℂ) * z ^ k
  have hs : HasSum (fun k => coeff k (F.map Complex.ofRealHom) * z ^ k) S := by
    simpa only [coeff_map, Complex.ofRealHom_eq_coe] using
      (complex_series_summable F hF hx hseries t).hasSum
  have hchar (n : ℕ) : charFun ((law F hF x value hx hvalue hseries n).toMeasure.map
      (fun k : ℕ => (k : ℝ))) t = (S / (value : ℂ)) ^ n := by
    rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
    simp only [Complex.ofReal_natCast]
    rw [PMF.integral_eq_tsum _ _ (pmf_nat_integrable_cexp _ t)]
    have hn := (scalarSeries_hasSum_pow hs n).div_const ((value : ℂ) ^ n)
    rw [div_pow]
    refine (tsum_congr ?_).trans hn.tsum_eq
    intro k
    rw [law_toReal]
    simp only [probability, RCLike.real_smul_eq_coe_mul, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_pow, ← map_pow, coeff_map,
      Complex.ofRealHom_eq_coe]
    have hexp : Complex.exp ((t : ℂ) * (k : ℂ) * Complex.I) =
        Complex.exp ((t : ℂ) * Complex.I) ^ k := by
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    dsimp [z]
    rw [mul_pow]
    push_cast
    ring
  rw [hchar n, hchar 1, pow_one]

theorem law_integrable_exp (hF : ∀ k, 0 ≤ coeff k F) {x value r : ℝ}
    (hx : 0 ≤ x) (hvalue : 0 < value)
    (hseries : HasSum (fun k => coeff k F * x ^ k) value)
    (hr : Summable (fun k => coeff k F * r ^ k)) (t : ℝ) (ht : x * Real.exp t ≤ r) :
    Integrable (fun k : ℕ => Real.exp (t * (k : ℝ)))
      (law F hF x value hx hvalue hseries 1).toMeasure := by
  have hsum : Summable (fun k => coeff k F * (x * Real.exp t) ^ k) := by
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (hF k) (pow_nonneg (mul_nonneg hx (Real.exp_pos _).le) _))
      (fun k => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hx (Real.exp_pos _).le) ht k) (hF k)) hr
  apply pmf_nat_integrable_of_summable
  convert! hsum.div_const value using 1
  ext k
  rw [law_toReal]
  simp only [probability, pow_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mul_pow, ← Real.exp_nat_mul]
  rw [show t * (k : ℝ) = (k : ℝ) * t by ring]
  ring

theorem law_memLp_two (hF : ∀ k, 0 ≤ coeff k F) {x value r : ℝ}
    (hx : 0 ≤ x) (hvalue : 0 < value)
    (hseries : HasSum (fun k => coeff k F * x ^ k) value)
    (hxr : x < r) (hr : Summable (fun k => coeff k F * r ^ k)) :
    MemLp (fun k : ℕ => (k : ℝ)) 2 (law F hF x value hx hvalue hseries 1).toMeasure := by
  apply memLp_of_mem_interior_integrableExpSet _ 2
  apply mem_interior_iff_mem_nhds.mpr
  have hc : Continuous (fun t : ℝ => x * Real.exp t) := by fun_prop
  have he : x * Real.exp 0 < r := by simpa only [Real.exp_zero, mul_one] using hxr
  filter_upwards [hc.continuousAt.eventually (gt_mem_nhds he)] with t ht
  exact law_integrable_exp F hF hx hvalue hseries hr t ht.le

end GeneralCoefficient

end PiIrrationality
