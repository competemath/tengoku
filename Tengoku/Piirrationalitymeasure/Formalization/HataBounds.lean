import Tengoku.Piirrationalitymeasure.Formalization.HataScale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Quantitative bounds at a selected Hata index.  This is the nonzero paired
integer branch of (5.9), separated from the later conversion from the index
scale to a power of `q`.
-/

namespace PiIrrationality

/--
@isnad1 id=lt.3h6v.s6.1de03f4022cd from=translated src=- shape=b9b1a24e vocab=1c309de2
-/
theorem hata_scale_linear_form_small
    (theta : ℝ) (U V : ℤ) (q n : ℕ) (a : ℝ) (ha : 0 < a)
    (hNn : hataScale q a ha ≤ n)
    (hLupper : |linearForm theta U V| ≤ Real.exp (-a * (n : ℝ))) :
    |(q : ℝ) * linearForm theta U V| < (1 : ℝ) / 2 := by
  have htail := hataScale_tail_small q n ha hNn
  have hq : 0 ≤ (q : ℝ) := by positivity
  calc
    |(q : ℝ) * linearForm theta U V| =
        (q : ℝ) * |linearForm theta U V| := by
          rw [abs_mul, abs_of_nonneg hq]
    _ ≤ (q : ℝ) * Real.exp (-a * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hLupper hq
    _ < (1 : ℝ) / 2 := htail

/--
@isnad1 id=lt.5h7v.s7.4f4d7d6faba1 from=translated src=- shape=b3d5b3ce vocab=4a9d426c
-/
theorem hata_nonzero_index_bound
    (theta : ℝ) (U V : ℤ) (p : ℤ) (q : ℕ) (beta n : ℝ)
    (hV : V ≠ 0) (hq : 0 < q)
    (hA : hataInteger U V p q ≠ 0)
    (hsmall : |(q : ℝ) * linearForm theta U V| < (1 : ℝ) / 2)
    (hVupper : |(V : ℝ)| ≤ Real.exp (beta * n)) :
    |hataDelta theta p q| > (1 : ℝ) / 2 * Real.exp (-beta * n) := by
  have hbase := hata_delta_lower_of_integer_ne_zero theta U V p q
    hq hV hA hsmall
  have hVpos : 0 < |(V : ℝ)| := abs_pos.mpr (by exact_mod_cast hV)
  have hexppos : 0 < Real.exp (beta * n) := Real.exp_pos _
  have hleftpos : 0 < 2 * |(V : ℝ)| := mul_pos (by norm_num) hVpos
  have hrightpos : 0 < 2 * Real.exp (beta * n) := mul_pos (by norm_num) hexppos
  have hrecip : (1 : ℝ) / (2 * Real.exp (beta * n)) ≤
      1 / (2 * |(V : ℝ)|) := by
    apply (div_le_div_iff₀ hrightpos hleftpos).2
    nlinarith [hVupper]
  have hexpneg : Real.exp (-beta * n) = (Real.exp (beta * n))⁻¹ := by
    rw [show -beta * n = -(beta * n) by ring, Real.exp_neg]
  have hrewrite : (1 : ℝ) / (2 * Real.exp (beta * n)) =
      (1 : ℝ) / 2 * Real.exp (-beta * n) := by
    rw [hexpneg, div_eq_mul_inv]
    ring
  rw [← hrewrite]
  exact lt_of_le_of_lt hrecip hbase

/--
@isnad1 id=lt.7h7v.s7.a70f0d5aad6f from=translated src=- shape=8617992b vocab=f3c64a61
-/
theorem hata_nonzero_q_power_bound
    (theta : ℝ) (U V : ℤ) (p : ℤ) (q : ℕ) (a beta : ℝ)
    (ha : 0 < a) (hbeta : 0 ≤ beta) (hV : V ≠ 0) (hq : 0 < q)
    (hA : hataInteger U V p q ≠ 0)
    (hsmall : |(q : ℝ) * linearForm theta U V| < (1 : ℝ) / 2)
    (hVupper : |(V : ℝ)| ≤
      Real.exp (beta * (hataScale q a ha : ℝ))) :
    |hataDelta theta p q| >
      (1 : ℝ) / 2 * Real.exp (-beta) * (2 * q : ℝ) ^ (-beta / a) := by
  have hindex := hata_nonzero_index_bound theta U V p q beta
      (hataScale q a ha : ℝ) hV hq hA hsmall hVupper
  have hscale := hataScale_exp_upper q hq ha
  have hqpos : 0 < (2 * q : ℝ) := by positivity
  have hexpNpos : 0 < Real.exp (hataScale q a ha : ℝ) := Real.exp_pos _
  have hpow :
      (Real.exp (hataScale q a ha : ℝ)) ^ (-beta) ≥
        (Real.exp 1 * (2 * q : ℝ) ^ (1 / a)) ^ (-beta) := by
    exact Real.rpow_le_rpow_of_nonpos hexpNpos hscale (neg_nonpos.mpr hbeta)
  have hpow' :
      Real.exp (-beta * (hataScale q a ha : ℝ)) ≥
        Real.exp (-beta) * (2 * q : ℝ) ^ (-beta / a) := by
    calc
      Real.exp (-beta * (hataScale q a ha : ℝ)) =
          (Real.exp (hataScale q a ha : ℝ)) ^ (-beta) := by
            rw [show -beta * (hataScale q a ha : ℝ) =
              (hataScale q a ha : ℝ) * (-beta) by ring, Real.exp_mul]
      _ ≥ (Real.exp 1 * (2 * q : ℝ) ^ (1 / a)) ^ (-beta) := hpow
      _ = Real.exp (-beta) * (2 * q : ℝ) ^ (-beta / a) := by
        rw [Real.mul_rpow (Real.exp_nonneg 1) (Real.rpow_nonneg (le_of_lt hqpos) _)]
        rw [← Real.exp_mul]
        simp only [one_mul]
        rw [← Real.rpow_mul (le_of_lt hqpos)]
        congr 1
        ring_nf
  have hbase :
      (1 : ℝ) / 2 * Real.exp (-beta) * (2 * q : ℝ) ^ (-beta / a) ≤
        (1 : ℝ) / 2 * Real.exp (-beta * (hataScale q a ha : ℝ)) := by
    have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
    calc
      (1 : ℝ) / 2 * Real.exp (-beta) * (2 * q : ℝ) ^ (-beta / a) =
          (1 / 2 : ℝ) * (Real.exp (-beta) * (2 * q : ℝ) ^ (-beta / a)) := by ring
      _ ≤ (1 / 2 : ℝ) * Real.exp (-beta * (hataScale q a ha : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow' hhalf
      _ = (1 : ℝ) / 2 * Real.exp (-beta * (hataScale q a ha : ℝ)) := by ring
  exact lt_of_le_of_lt hbase hindex

/--
@isnad1 id=lt.7h7v.s8.69ee06d6e1c7 from=translated src=- shape=3b936ddd vocab=1443d1b2
-/
theorem hata_nonzero_rational_approx_bound
    (theta : ℝ) (U V : ℤ) (p : ℤ) (q : ℕ) (a beta : ℝ)
    (ha : 0 < a) (hbeta : 0 ≤ beta) (hV : V ≠ 0) (hq : 0 < q)
    (hA : hataInteger U V p q ≠ 0)
    (hsmall : |(q : ℝ) * linearForm theta U V| < (1 : ℝ) / 2)
    (hVupper : |(V : ℝ)| ≤
      Real.exp (beta * (hataScale q a ha : ℝ))) :
    |theta - (p : ℝ) / (q : ℝ)| >
      ((1 : ℝ) / 2 * Real.exp (-beta) * (2 * q : ℝ) ^ (-beta / a)) /
        (q : ℝ) := by
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqbound := hata_nonzero_q_power_bound theta U V p q a beta
    ha hbeta hV hq hA hsmall hVupper
  have hdiv := (div_lt_div_of_pos_right hqbound hqreal)
  have hfac := hata_delta_abs_factorization theta p q hq
  calc
    ((1 : ℝ) / 2 * Real.exp (-beta) * (2 * q : ℝ) ^ (-beta / a)) /
        (q : ℝ) < |hataDelta theta p q| / (q : ℝ) := hdiv
    _ = |theta - (p : ℝ) / (q : ℝ)| := by
      rw [hfac]
      field_simp [hqreal.ne']

/--
@isnad1 id=lt.5h5v.s7.e1ea1e98e885 from=translated src=- shape=d63678d4 vocab=d7706f1e
-/
theorem hata_second_branch_intermediate
    {D q alpha gamma M : ℝ} (hD : 0 < D) (hq : 0 < q)
    (halpha : 0 ≤ alpha) (hupper : Real.exp M ≤
      Real.exp 1 * (q / D) ^ (1 / gamma))
    (hlower : D > (1 : ℝ) / 2 * Real.exp (-alpha * M)) :
    D > (1 : ℝ) / 2 * Real.exp (-alpha) *
      (q / D) ^ (-alpha / gamma) := by
  have hqD : 0 < q / D := div_pos hq hD
  have hpow :
      (Real.exp 1 * (q / D) ^ (1 / gamma)) ^ (-alpha) ≤
        (Real.exp M) ^ (-alpha) := by
    exact Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hupper
      (neg_nonpos.mpr halpha)
  have hpow' :
      Real.exp (-alpha * M) ≥ Real.exp (-alpha) *
        (q / D) ^ (-alpha / gamma) := by
    calc
      Real.exp (-alpha * M) = (Real.exp M) ^ (-alpha) := by
        rw [show -alpha * M = M * (-alpha) by ring, Real.exp_mul]
      _ ≥ (Real.exp 1 * (q / D) ^ (1 / gamma)) ^ (-alpha) := hpow
      _ = Real.exp (-alpha) * (q / D) ^ (-alpha / gamma) := by
        rw [Real.mul_rpow (Real.exp_nonneg 1)
          (Real.rpow_nonneg hqD.le _)]
        rw [← Real.exp_mul]
        simp only [one_mul]
        rw [← Real.rpow_mul hqD.le]
        congr 1
        ring_nf
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hpow' hhalf
  calc
    (1 : ℝ) / 2 * Real.exp (-alpha) * (q / D) ^ (-alpha / gamma) =
        (1 / 2 : ℝ) * (Real.exp (-alpha) * (q / D) ^ (-alpha / gamma)) := by ring
    _ ≤ (1 / 2 : ℝ) * Real.exp (-alpha * M) := hmul
    _ < D := hlower

/--
@isnad1 id=lt.5h4v.s7.0b8463486c86 from=translated src=- shape=f7ec60c0 vocab=7ea5cb2d
-/
theorem rpow_fixed_point_lower
    {D K q r : ℝ} (hD : 0 < D) (hK : 0 < K) (hq : 0 < q)
    (hr1 : r < 1)
    (h : D > K * (q / D) ^ (-r)) :
    D > (K * q ^ (-r)) ^ (1 / (1 - r)) := by
  have hqD : 0 < q / D := div_pos hq hD
  have hright : 0 < K * (q / D) ^ (-r) :=
    mul_pos hK (Real.rpow_pos_of_pos hqD _)
  have hlog := Real.log_lt_log hright h
  rw [Real.log_mul hK.ne'
      (Real.rpow_pos_of_pos hqD _).ne', Real.log_rpow hqD,
      Real.log_div hq.ne' hD.ne'] at hlog
  have hone : 0 < 1 - r := sub_pos.mpr hr1
  have hscaled := mul_lt_mul_of_pos_left hlog hone
  have hTpos : 0 < (K * q ^ (-r)) ^ (1 / (1 - r)) := by positivity
  have hlogT : Real.log ((K * q ^ (-r)) ^ (1 / (1 - r))) =
      (1 / (1 - r)) * (Real.log K + (-r) * Real.log q) := by
    rw [Real.log_rpow (mul_pos hK (Real.rpow_pos_of_pos hq _)),
      Real.log_mul hK.ne' (Real.rpow_pos_of_pos hq _).ne', Real.log_rpow hq]
  have hlogcomp :
      Real.log ((K * q ^ (-r)) ^ (1 / (1 - r))) < Real.log D := by
    rw [hlogT]
    have hquot :
        (Real.log K + (-r) * Real.log q) / (1 - r) < Real.log D := by
      apply (div_lt_iff₀ hone).2
      nlinarith [hscaled]
    calc
      (1 / (1 - r)) * (Real.log K + (-r) * Real.log q) =
          (Real.log K + (-r) * Real.log q) / (1 - r) := by ring
      _ < Real.log D := hquot
  exact (Real.log_lt_log_iff hTpos hD).mp hlogcomp

/--
@isnad1 id=lt.5h4v.s7.038e4862a990 from=translated src=- shape=058b9a69 vocab=048ae7ea
-/
theorem hata_second_branch_power_bound
    {D q alpha gamma : ℝ} (hD : 0 < D) (hq : 0 < q)
    (halpha : 0 ≤ alpha) (hgap : alpha < gamma)
    (h : D > (1 : ℝ) / 2 * Real.exp (-alpha) *
      (q / D) ^ (-alpha / gamma)) :
    D > (2 * Real.exp alpha) ^ (-gamma / (gamma - alpha)) *
      q ^ (-alpha / (gamma - alpha)) := by
  have hgamma : 0 < gamma := lt_of_le_of_lt halpha hgap
  have hr : alpha / gamma < 1 := by
    apply (div_lt_iff₀ hgamma).2
    linarith
  have hK : 0 < (1 : ℝ) / 2 * Real.exp (-alpha) :=
    mul_pos (by norm_num) (Real.exp_pos _)
  have h' : D > (1 : ℝ) / 2 * Real.exp (-alpha) *
      (q / D) ^ (-(alpha / gamma)) := by
    convert h using 1 <;> ring
  have hfixed := rpow_fixed_point_lower hD hK hq hr h'
  have hbase : 0 < 2 * Real.exp alpha := by positivity
  have hK_eq : (1 : ℝ) / 2 * Real.exp (-alpha) =
      (2 * Real.exp alpha) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg (le_of_lt hbase), Real.rpow_one]
    rw [Real.exp_neg]
    field_simp
  have hfixed_eq :
      ((1 : ℝ) / 2 * Real.exp (-alpha) * q ^ (-(alpha / gamma))) ^
          (1 / (1 - alpha / gamma)) =
        (2 * Real.exp alpha) ^ (-gamma / (gamma - alpha)) *
          q ^ (-alpha / (gamma - alpha)) := by
    rw [hK_eq, Real.mul_rpow (Real.rpow_nonneg (le_of_lt hbase) _) 
      (Real.rpow_nonneg hq.le _)]
    rw [← Real.rpow_mul (le_of_lt hbase), ← Real.rpow_mul hq.le]
    congr 1 <;> field_simp <;> ring
  rw [hfixed_eq] at hfixed
  exact hfixed

/--
@isnad1 id=lt.5h6v.s6.1f1b32a52b3a from=translated src=- shape=69c924ec vocab=c4e250b3
-/
theorem hata_uniform_min_power_bound
    {D q c1 c2 k1 kappa : ℝ} (hq : 1 ≤ q)
    (hc1 : 0 ≤ c1) (hk : k1 ≤ kappa)
    (hfirst : D > c1 * q ^ (-k1))
    (hsecond : D > c2 * q ^ (-kappa)) :
    D > min c1 c2 * q ^ (-kappa) := by
  have hpow : q ^ (-kappa) ≤ q ^ (-k1) := by
    exact Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  by_cases h12 : c1 ≤ c2
  · have hmin : min c1 c2 = c1 := min_eq_left h12
    rw [hmin]
    have hmul : c1 * q ^ (-kappa) ≤ c1 * q ^ (-k1) :=
      mul_le_mul_of_nonneg_left hpow hc1
    exact lt_of_le_of_lt hmul hfirst
  · have h21 : c2 ≤ c1 := le_of_not_ge h12
    have hmin : min c1 c2 = c2 := min_eq_right h21
    rw [hmin]
    exact hsecond

/- The final assembly of Hata's two alternatives: once every denominator
  admits either branch, the weaker of the two constants gives one uniform
  power-law lower bound. -/
/--
@isnad1 id=lt.6h8v.s7.ff24e9f94324 from=translated src=- shape=f2b4e196 vocab=0a7b0eb5
-/
theorem hata_two_branch_uniform_power_bound
    {theta kappa c1 c2 k1 : ℝ} {q0 : ℕ}
    (hq0 : 1 ≤ q0) (hc1 : 0 ≤ c1) (hk : k1 ≤ kappa)
    (hbranch : ∀ p : ℤ, ∀ q : ℕ, q0 ≤ q → 0 < q →
      |theta - (p : ℝ) / (q : ℝ)| > c1 * (q : ℝ) ^ (-k1) ∨
      |theta - (p : ℝ) / (q : ℝ)| > c2 * (q : ℝ) ^ (-kappa)) :
    ∀ p : ℤ, ∀ q : ℕ, q0 ≤ q → 0 < q →
      |theta - (p : ℝ) / (q : ℝ)| > min c1 c2 * (q : ℝ) ^ (-kappa) := by
  intro p q hq0' hq
  have hq1 : 1 ≤ q := le_trans hq0 hq0'
  rcases hbranch p q hq0' hq with hfirst | hsecond
  · by_cases h12 : c1 ≤ c2
    · rw [min_eq_left h12]
      have hpow : (q : ℝ) ^ (-kappa) ≤ (q : ℝ) ^ (-k1) := by
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq1)
          (by linarith)
      have hmul : c1 * (q : ℝ) ^ (-kappa) ≤
          c1 * (q : ℝ) ^ (-k1) :=
        mul_le_mul_of_nonneg_left hpow hc1
      exact lt_of_le_of_lt hmul hfirst
    · have h21 : c2 ≤ c1 := le_of_not_ge h12
      rw [min_eq_right h21]
      by_cases hc2 : 0 ≤ c2
      · have hpow : (q : ℝ) ^ (-kappa) ≤ (q : ℝ) ^ (-k1) := by
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq1)
            (by linarith)
        have hmul : c2 * (q : ℝ) ^ (-kappa) ≤
            c1 * (q : ℝ) ^ (-k1) := by
          calc
            c2 * (q : ℝ) ^ (-kappa) ≤ c2 * (q : ℝ) ^ (-k1) :=
              mul_le_mul_of_nonneg_left hpow hc2
            _ ≤ c1 * (q : ℝ) ^ (-k1) := by
              exact mul_le_mul_of_nonneg_right h21
                (Real.rpow_nonneg (by positivity) _)
        exact lt_of_le_of_lt hmul hfirst
      · have hDpos : 0 < |theta - (p : ℝ) / (q : ℝ)| := by
          have hnonneg : 0 ≤ c1 * (q : ℝ) ^ (-k1) :=
            mul_nonneg hc1 (Real.rpow_nonneg (by positivity) _)
          exact lt_of_le_of_lt hnonneg hfirst
        have htarget : c2 * (q : ℝ) ^ (-kappa) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc2)
            (Real.rpow_nonneg (by positivity) _)
        exact lt_of_le_of_lt htarget hDpos
  · by_cases h12 : c1 ≤ c2
    · rw [min_eq_left h12]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right h12
          (Real.rpow_nonneg (by positivity) _)) hsecond
    · have h21 : c2 ≤ c1 := le_of_not_ge h12
      rw [min_eq_right h21]
      exact hsecond

end PiIrrationality
