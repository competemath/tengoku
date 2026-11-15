import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter Topology Complex
open scoped Real ComplexConjugate

noncomputable section

/--
@isnad1 id=eq.2h1v.s5.eb9a44723d70 from=translated src=- shape=03693c10 vocab=d81b2980
-/
theorem completedRiemannZeta_eq_mul_Gammaℝ {s : ℂ} (hs0 : s ≠ 0)
    (hΓ : Complex.Gammaℝ s ≠ 0) :
    completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s := by
  rw [riemannZeta_def_of_ne_zero hs0, div_mul_cancel₀ _ hΓ]

/--
@isnad1 id=ne.1h1v.s4.44398e394d95 from=translated src=- shape=555d9df8 vocab=54aa39c7
-/
theorem completedRiemannZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Complex.zero_re] at hs
    linarith
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [completedRiemannZeta_eq_mul_Gammaℝ hs0 hΓ]
  exact mul_ne_zero (riemannZeta_ne_zero_of_one_le_re hs) hΓ

/--
@isnad1 id=ne.1h1v.s4.3c0e7c203767 from=translated src=- shape=7cc8a206 vocab=54aa39c7
-/
theorem completedRiemannZeta_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    completedRiemannZeta s ≠ 0 := by
  rw [← completedRiemannZeta_one_sub s]
  refine completedRiemannZeta_ne_zero_of_one_le_re ?_
  rw [Complex.sub_re, Complex.one_re]
  linarith

/--
@isnad1 id=eq.0h0v.s4.431db292b650 from=translated src=- shape=27dc4851 vocab=d6f7a2b1
-/
theorem completedRiemannZeta_two : completedRiemannZeta 2 = (Real.pi : ℂ) / 6 := by
  have hΓne : Complex.Gammaℝ 2 ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hΓ : Complex.Gammaℝ 2 = ((Real.pi : ℂ))⁻¹ := by
    rw [Complex.Gammaℝ_def, show (-(2 : ℂ) / 2) = -1 by norm_num,
      show ((2 : ℂ) / 2) = 1 by norm_num, Complex.cpow_neg_one, Complex.Gamma_one, mul_one]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [completedRiemannZeta_eq_mul_Gammaℝ two_ne_zero hΓne, riemannZeta_two, hΓ]
  field_simp

def eisensteinScattering (s : ℂ) : ℂ :=
  completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s)

/--
@isnad1 id=eq.0h1v.s5.1f62dcc2cebc from=translated src=- shape=f0cd4f74 vocab=335b26ac
-/
theorem eisensteinScattering_def (s : ℂ) :
    eisensteinScattering s =
      completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s) := rfl

/--
@isnad1 id=differen.5h1v.s7.02e9d328f260 from=translated src=- shape=7d8d6194 vocab=cf175023
-/
theorem differentiableAt_eisensteinScattering {s : ℂ}
    (h1 : 2 * s - 1 ≠ 0) (h2 : 2 * s - 1 ≠ 1) (h3 : 2 * s ≠ 0) (h4 : 2 * s ≠ 1)
    (h5 : completedRiemannZeta (2 * s) ≠ 0) :
    DifferentiableAt ℂ eisensteinScattering s := by
  have hnum : DifferentiableAt ℂ (fun z : ℂ => completedRiemannZeta (2 * z - 1)) s := by
    have := (differentiableAt_completedZeta h1 h2).comp s
      (((differentiableAt_const (2 : ℂ)).mul differentiableAt_id).sub
        (differentiableAt_const 1))
    simpa [Function.comp_def] using this
  have hden : DifferentiableAt ℂ (fun z : ℂ => completedRiemannZeta (2 * z)) s := by
    have := (differentiableAt_completedZeta h3 h4).comp s
      ((differentiableAt_const (2 : ℂ)).mul differentiableAt_id)
    simpa [Function.comp_def] using this
  exact hnum.div hden h5

/--
@isnad1 id=differen.2h1v.s6.6e78b8c54fa4 from=translated src=- shape=eb927e34 vocab=4a12a40c
-/
theorem differentiableAt_eisensteinScattering_of_half_lt_re {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ eisensteinScattering s := by
  have hre2 : (2 * s).re = 2 * s.re := by
    simp [Complex.mul_re]
  have hre21 : (2 * s - 1).re = 2 * s.re - 1 := by
    simp [Complex.sub_re, Complex.mul_re]
  refine differentiableAt_eisensteinScattering ?_ ?_ ?_ ?_ ?_
  · intro h
    have : (2 * s - 1).re = 0 := by rw [h, Complex.zero_re]
    rw [hre21] at this
    linarith
  · intro h
    apply hs1
    have : 2 * s = 2 * 1 := by rw [mul_one]; linear_combination h
    exact mul_left_cancel₀ two_ne_zero this
  · intro h
    have : (2 * s).re = 0 := by rw [h, Complex.zero_re]
    rw [hre2] at this
    linarith
  · intro h
    have : (2 * s).re = 1 := by rw [h, Complex.one_re]
    rw [hre2] at this
    linarith
  · exact completedRiemannZeta_ne_zero_of_one_le_re (by rw [hre2]; linarith)

/--
@isnad1 id=ne.1h1v.s4.497d6d49712c from=translated src=- shape=555d9df8 vocab=f0238943
-/
theorem eisensteinScattering_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    eisensteinScattering s ≠ 0 := by
  have hre2 : (2 * s).re = 2 * s.re := by simp [Complex.mul_re]
  have hre21 : (2 * s - 1).re = 2 * s.re - 1 := by simp [Complex.sub_re, Complex.mul_re]
  exact div_ne_zero
    (completedRiemannZeta_ne_zero_of_one_le_re (by rw [hre21]; linarith))
    (completedRiemannZeta_ne_zero_of_one_le_re (by rw [hre2]; linarith))

/--
@isnad1 id=eq.2h1v.s6.323780b05f25 from=translated src=- shape=435f9718 vocab=27e86fa1
-/
theorem eisensteinScattering_mul_one_sub (s : ℂ)
    (h1 : completedRiemannZeta (2 * s - 1) ≠ 0)
    (h2 : completedRiemannZeta (2 * s) ≠ 0) :
    eisensteinScattering s * eisensteinScattering (1 - s) = 1 := by
  have e1 : 2 * (1 - s) - 1 = 1 - 2 * s := by ring
  have e2 : 2 * (1 - s) = 1 - (2 * s - 1) := by ring
  rw [eisensteinScattering_def, eisensteinScattering_def, e1, e2,
    completedRiemannZeta_one_sub (2 * s), completedRiemannZeta_one_sub (2 * s - 1),
    div_mul_div_comm, mul_comm (completedRiemannZeta (2 * s - 1)) (completedRiemannZeta (2 * s)),
    div_self (mul_ne_zero h2 h1)]

/--
@isnad1 id=eq.1h1v.s5.a842016e40f6 from=translated src=- shape=b2623e89 vocab=9555bb5a
-/
theorem eisensteinScattering_mul_one_sub_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    eisensteinScattering s * eisensteinScattering (1 - s) = 1 := by
  have hre2 : (2 * s).re = 2 * s.re := by simp [Complex.mul_re]
  have hre21 : (2 * s - 1).re = 2 * s.re - 1 := by simp [Complex.sub_re, Complex.mul_re]
  exact eisensteinScattering_mul_one_sub s
    (completedRiemannZeta_ne_zero_of_re_nonpos (by rw [hre21, hs]; norm_num))
    (completedRiemannZeta_ne_zero_of_one_le_re (by rw [hre2, hs]; norm_num))

/--
@isnad1 id=tendsto.0h0v.s6.486a925bccaf from=translated src=- shape=e6c650a5 vocab=e51d6192
-/
theorem eisensteinScattering_residue_one :
    Tendsto (fun s : ℂ => (s - 1) * eisensteinScattering s) (𝓝[≠] 1)
      (𝓝 (3 / (Real.pi : ℂ))) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

  have hsub : Tendsto (fun s : ℂ => 2 * s - 1) (𝓝[≠] (1 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Continuous fun s : ℂ => 2 * s - 1 := by fun_prop
      have h1 : Tendsto (fun s : ℂ => 2 * s - 1) (𝓝 (1 : ℂ)) (𝓝 (2 * 1 - 1)) :=
        hcont.tendsto 1
      norm_num at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro h
      apply hs
      have : 2 * s = 2 * 1 := by rw [mul_one]; linear_combination h
      exact mul_left_cancel₀ two_ne_zero this

  have hnum : Tendsto (fun s : ℂ => ((2 * s - 1) - 1) * completedRiemannZeta (2 * s - 1))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := completedRiemannZeta_residue_one.comp hsub

  have hden : Tendsto (fun s : ℂ => completedRiemannZeta (2 * s)) (𝓝[≠] (1 : ℂ))
      (𝓝 ((Real.pi : ℂ) / 6)) := by
    rw [← completedRiemannZeta_two]
    have hcont : ContinuousAt completedRiemannZeta 2 :=
      (differentiableAt_completedZeta two_ne_zero (by norm_num)).continuousAt
    have : Tendsto (fun s : ℂ => completedRiemannZeta (2 * s)) (𝓝 (1 : ℂ))
        (𝓝 (completedRiemannZeta 2)) := by
      have h2 : Tendsto (fun s : ℂ => 2 * s) (𝓝 (1 : ℂ)) (𝓝 (2 : ℂ)) := by
        have hc : Continuous fun s : ℂ => 2 * s := by fun_prop
        have := hc.tendsto 1
        norm_num at this
        exact this
      exact hcont.tendsto.comp h2
    exact this.mono_left nhdsWithin_le_nhds

  have hπ6 : ((Real.pi : ℂ) / 6) ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff, hπ, false_or]
    norm_num
  have key : Tendsto
      (fun s : ℂ => (1 / 2 : ℂ) * (((2 * s - 1) - 1) * completedRiemannZeta (2 * s - 1)) /
        completedRiemannZeta (2 * s))
      (𝓝[≠] (1 : ℂ)) (𝓝 ((1 / 2 : ℂ) * 1 / ((Real.pi : ℂ) / 6))) :=
    ((hnum.const_mul (1 / 2 : ℂ)).div hden hπ6)
  have hval : (1 / 2 : ℂ) * 1 / ((Real.pi : ℂ) / 6) = 3 / (Real.pi : ℂ) := by
    field_simp
    ring
  rw [hval] at key
  refine key.congr fun s => ?_
  rw [eisensteinScattering_def, ← mul_div_assoc]
  congr 1
  ring

/--
@isnad1 id=eq.1h1v.s6.96dbc69f9438 from=translated src=- shape=f8ce9af1 vocab=7c300c24
-/
theorem completedRiemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hπarg : Complex.arg (Real.pi : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Ne.symm Real.pi_ne_zero
  have hs' : 1 < (conj s).re := by rwa [Complex.conj_re]
  rw [completedZeta_eq_tsum_of_one_lt_re hs, completedZeta_eq_tsum_of_one_lt_re hs',
    map_mul, map_mul]
  congr 1
  · congr 1
    ·
      have harg : -(conj s) / 2 = conj (-s / 2) := by
        rw [map_div₀, map_neg, map_ofNat]
      rw [harg, Complex.cpow_conj _ _ hπarg, Complex.conj_ofReal]
    ·
      have harg : (conj s) / 2 = conj (s / 2) := by
        rw [map_div₀, map_ofNat]
      rw [harg, Complex.Gamma_conj]
  ·
    have hterm : ∀ n : ℕ,
        (1 : ℂ) / (n : ℂ) ^ (conj s) = conj ((1 : ℂ) / (n : ℂ) ^ s) := by
      intro n
      rw [map_div₀, map_one]
      congr 1
      have hnarg : Complex.arg (n : ℂ) ≠ Real.pi := by
        rw [Complex.natCast_arg]
        exact Ne.symm Real.pi_ne_zero
      rw [Complex.cpow_conj _ _ hnarg, Complex.conj_natCast]
    calc ∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ (conj s)
        = ∑' n : ℕ, conj ((1 : ℂ) / (n : ℂ) ^ s) := tsum_congr hterm
      _ = conj (∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ s) := by
          simp only [starRingEnd_apply]
          exact tsum_star.symm

def CompletedZetaConjSymm : Prop :=
  ∀ s : ℂ, completedRiemannZeta (conj s) = conj (completedRiemannZeta s)

/--
@isnad1 id=eq.1h1v.s6.1848e12e36ee from=translated src=- shape=dddf01e7 vocab=f09dc214
-/
theorem eisensteinScattering_conj (h : CompletedZetaConjSymm) (s : ℂ) :
    eisensteinScattering (conj s) = conj (eisensteinScattering s) := by
  rw [eisensteinScattering_def, eisensteinScattering_def, map_div₀]
  congr 1
  · rw [← h (2 * s - 1)]
    congr 1
    rw [map_sub, map_mul, map_one, map_ofNat]
  · rw [← h (2 * s)]
    congr 1
    rw [map_mul, map_ofNat]

/--
@isnad1 id=eq.2h1v.s5.80ce0130ffac from=translated src=- shape=1e503eaf vocab=e9296b67
-/
theorem norm_eisensteinScattering_critical_line (h : CompletedZetaConjSymm)
    {s : ℂ} (hs : s.re = 1 / 2) :
    ‖eisensteinScattering s‖ = 1 := by

  have hconj : (1 : ℂ) - s = conj s := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, hs]
      norm_num
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
      ring

  have key := eisensteinScattering_mul_one_sub_of_re_eq_half hs
  rw [hconj, eisensteinScattering_conj h] at key

  have hnormsq : Complex.normSq (eisensteinScattering s) = 1 := by
    have h1 : ((Complex.normSq (eisensteinScattering s) : ℝ) : ℂ) = 1 := by
      rw [← Complex.mul_conj]
      exact key
    exact_mod_cast h1
  have hnorm' : ‖eisensteinScattering s‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hnormsq
  nlinarith [norm_nonneg (eisensteinScattering s)]

/--
@isnad1 id=not.2h2v.s7.fca5d748d6f3 from=translated src=- shape=6e30429b vocab=7e17e5ed
-/
theorem not_integrableOn_norm_cpow_sq_div_sq {s : ℂ} (hs : s.re = 1 / 2) {T : ℝ}
    (hT : 0 < T) :
    ¬ MeasureTheory.IntegrableOn (fun y : ℝ => ‖(y : ℂ) ^ s‖ ^ 2 / y ^ 2) (Set.Ioi T) := by
  intro hint

  have heq : ∀ y ∈ Set.Ioi T, ‖(y : ℂ) ^ s‖ ^ 2 / y ^ 2 = y ^ (-1 : ℝ) := by
    intro y hy
    have hy0 : 0 < y := lt_trans hT hy
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0, hs]
    rw [← Real.rpow_natCast (y ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hy0.le,
      ← Real.rpow_natCast y 2, ← Real.rpow_sub hy0]
    norm_num
  have : MeasureTheory.IntegrableOn (fun y : ℝ => y ^ (-1 : ℝ)) (Set.Ioi T) :=
    (MeasureTheory.integrableOn_congr_fun heq measurableSet_Ioi).mp hint
  rw [integrableOn_Ioi_rpow_iff hT] at this
  linarith

/--
@isnad1 id=eq.0h0v.s5.86a008005bd8 from=translated src=- shape=7ed1bc26 vocab=b20874c3
-/
theorem eisensteinScattering_one_half : eisensteinScattering (1 / 2) = 1 := by
  have h0 : (2 : ℂ) * (1 / 2) - 1 = 1 - 1 := by ring
  have h1 : (2 : ℂ) * (1 / 2) = 1 := by ring
  have hΛ1 : completedRiemannZeta 1 ≠ 0 :=
    completedRiemannZeta_ne_zero_of_one_le_re (by rw [Complex.one_re])
  rw [eisensteinScattering_def, h0, h1, completedRiemannZeta_one_sub 1, div_self hΛ1]

/--
@isnad1 id=ne.0h0v.s4.bb077ea5978c from=translated src=- shape=3a8c3826 vocab=1669148a
-/
theorem eisensteinScattering_residue_ne_zero : (3 : ℂ) / (Real.pi : ℂ) ≠ 0 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp [div_eq_zero_iff, hπ]

/--
@isnad1 id=eq.0h0v.s5.be21c4ff0665 from=translated src=- shape=4ce6cf17 vocab=8ea2e141
-/
theorem eisensteinScattering_residue_mul_volume :
    (3 / (Real.pi : ℂ)) * ((Real.pi : ℂ) / 3) = 1 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/--
@isnad1 id=eq.0h0v.s6.4528a3daefa8 from=translated src=- shape=3cd2eac4 vocab=51bf70b2
-/
theorem eisensteinScattering_mul_one_sub_one_half :
    eisensteinScattering (1 / 2) * eisensteinScattering (1 - 1 / 2) = 1 := by
  norm_num [eisensteinScattering_one_half]

end
