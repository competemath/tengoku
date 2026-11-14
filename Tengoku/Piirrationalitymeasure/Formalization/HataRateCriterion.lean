import Tengoku.Piirrationalitymeasure.Formalization.HataAssembly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The full rate criterion of Lemma 5.1, allowing a positive normalization scale. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem hata_delta_choice {sigma tau epsilon : ℝ}
    (hs : 0 < sigma) (ht : 0 < tau) (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ delta < sigma / 2 ∧ delta < tau / 6 ∧
      (sigma + delta) / (tau - 3 * delta) < sigma / tau + epsilon / 2 := by
  have hc : ContinuousAt (fun delta : ℝ => (sigma + delta) / (tau - 3 * delta)) 0 := by
    fun_prop (disch := simpa using ht.ne')
  have hk : ∀ᶠ delta : ℝ in 𝓝 0,
      (sigma + delta) / (tau - 3 * delta) < sigma / tau + epsilon / 2 :=
    hc.eventually (gt_mem_nhds (by simp only [add_zero, mul_zero, sub_zero]; linarith))
  have hnear : ∀ᶠ delta : ℝ in 𝓝 0,
      delta < sigma / 2 ∧ delta < tau / 6 ∧
        (sigma + delta) / (tau - 3 * delta) < sigma / tau + epsilon / 2 :=
    (gt_mem_nhds (by positivity : (0 : ℝ) < sigma / 2)).and
      ((gt_mem_nhds (by positivity : (0 : ℝ) < tau / 6)).and hk)
  have hpos : ∀ᶠ delta : ℝ in 𝓝[>] 0, 0 < delta := self_mem_nhdsWithin
  exact (hpos.and (hnear.filter_mono nhdsWithin_le_nhds)).exists

theorem hata_exp_bounds_of_rates {theta sigma tau scale delta : ℝ} {U V : ℕ → ℤ}
    (hθ : Irrational theta) (hscale : 0 < scale) (hd : 0 < delta) (hds : delta < sigma)
    (hV : Tendsto (fun n : ℕ => Real.log |(V n : ℝ)| / (scale * (n : ℝ)))
      atTop (𝓝 sigma))
    (hL : limsup (fun n : ℕ => ((Real.log |linearForm theta (U n) (V n)| /
      (scale * (n : ℝ)) : ℝ) : EReal)) atTop ≤ ((-tau : ℝ) : EReal)) :
    (∀ᶠ n : ℕ in atTop, Real.exp (scale * (sigma - delta) * (n : ℝ)) ≤ |(V n : ℝ)|) ∧
    (∀ᶠ n : ℕ in atTop, |(V n : ℝ)| ≤ Real.exp (scale * (sigma + delta) * (n : ℝ))) ∧
    (∀ᶠ n : ℕ in atTop, |linearForm theta (U n) (V n)| ≤
      Real.exp (-(scale * (tau - delta)) * (n : ℝ))) := by
  have hvL := hV.eventually (lt_mem_nhds (show sigma - delta < sigma by linarith))
  have hvU := hV.eventually (gt_mem_nhds (show sigma < sigma + delta by linarith))
  have hc : ((-tau : ℝ) : EReal) < ((-tau + delta : ℝ) : EReal) := by
    exact_mod_cast (show -tau < -tau + delta by linarith)
  have hlU := eventually_lt_of_limsup_lt (hL.trans_lt hc)
    ⟨⊤, Eventually.of_forall (fun _ => le_top)⟩
  have hall : ∀ᶠ n : ℕ in atTop,
      Real.exp (scale * (sigma - delta) * (n : ℝ)) ≤ |(V n : ℝ)| ∧
      |(V n : ℝ)| ≤ Real.exp (scale * (sigma + delta) * (n : ℝ)) ∧
      |linearForm theta (U n) (V n)| ≤ Real.exp (-(scale * (tau - delta)) * (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hvL, hvU, hlU] with n hn hvL hvU hlU
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hden : 0 < scale * (n : ℝ) := mul_pos hscale hnR
    have hvl := (lt_div_iff₀ hden).mp hvL
    have hvu := (div_lt_iff₀ hden).mp hvU
    have hVne : V n ≠ 0 := by
      intro hz
      simp only [hz, Int.cast_zero, abs_zero, Real.log_zero] at hvl
      exact (not_lt_of_ge (mul_nonneg (by linarith) hden.le)) hvl
    have hvpos : 0 < |(V n : ℝ)| := abs_pos.mpr (by exact_mod_cast hVne)
    have hlpos : 0 < |linearForm theta (U n) (V n)| :=
      abs_pos.mpr (linearForm_ne_zero_of_irrational hθ hVne)
    have hlu : Real.log |linearForm theta (U n) (V n)| / (scale * (n : ℝ)) <
        -tau + delta := by exact_mod_cast hlU
    have hlu' := (div_lt_iff₀ hden).mp hlu
    refine ⟨(Real.le_log_iff_exp_le hvpos).mp ?_,
      (Real.log_le_iff_le_exp hvpos).mp ?_, (Real.log_le_iff_le_exp hlpos).mp ?_⟩ <;>
      nlinarith
  exact ⟨hall.mono (fun _ h => h.1), hall.mono (fun _ h => h.2.1),
    hall.mono (fun _ h => h.2.2)⟩

theorem hata_irrationality_bound {theta sigma tau scale : ℝ} {U V : ℕ → ℤ}
    (hθ : Irrational theta) (hs : 0 < sigma) (ht : 0 < tau) (hscale : 0 < scale)
    (hV : Tendsto (fun n : ℕ => Real.log |(V n : ℝ)| / (scale * (n : ℝ)))
      atTop (𝓝 sigma))
    (hL : limsup (fun n : ℕ => ((Real.log |linearForm theta (U n) (V n)| /
      (scale * (n : ℝ)) : ℝ) : EReal)) atTop ≤ ((-tau : ℝ) : EReal)) :
    IrrationalityMeasureAtMost theta (1 + sigma / tau) := by
  intro epsilon he
  obtain ⟨delta, hd, hds, hdt, hk⟩ := hata_delta_choice hs ht he
  obtain ⟨hvL, hvU, hlU⟩ := hata_exp_bounds_of_rates hθ hscale hd
    (show delta < sigma by linarith) hV hL
  have ha : 0 < scale * (tau - delta) := mul_pos hscale (by linarith)
  have hb : 0 < scale * (sigma - delta) := mul_pos hscale (by linarith)
  have hbd : scale * (sigma - delta) ≤ scale * (sigma + delta) := by nlinarith
  have hgap : scale * (sigma + delta) <
      scale * (sigma - delta) + scale * (tau - delta) := by nlinarith
  obtain ⟨c, hc, q0, hq0⟩ := hata_uniform_bound_of_exp_bounds hθ ha hb hbd hgap hvL hvU hlU
  have heq : scale * (sigma + delta) /
      (scale * (sigma - delta) + scale * (tau - delta) - scale * (sigma + delta)) =
        (sigma + delta) / (tau - 3 * delta) := by
    rw [show scale * (sigma - delta) + scale * (tau - delta) - scale * (sigma + delta) =
      scale * (tau - 3 * delta) by ring, mul_div_mul_left _ _ hscale.ne']
  rw [heq] at hq0
  have hmeasure := irrationalityMeasureAtMost_of_uniform_power_bound_of_pos_constant hc ⟨q0, hq0⟩
  obtain ⟨q1, hq1⟩ := hmeasure (epsilon / 2) (by linarith)
  refine ⟨q1, ?_⟩
  intro p q hqge hq
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hp := Real.rpow_le_rpow_of_exponent_le hq1R
    (show -(1 + sigma / tau) - epsilon ≤
      -(1 + (sigma + delta) / (tau - 3 * delta)) - epsilon / 2 by linarith)
  exact hp.trans_lt (hq1 p q hqge hq)

end PiIrrationality
