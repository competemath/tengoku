import Tengoku.OpenaiMath.OAI.Analysis.LpDimension.Discretization

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal
universe u uE uI

namespace SubpolynomialLp

open Metric Module Set
open scoped ENNReal
lemma packing_card_bound {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Finset E) (R : ℝ) (hR : 0 ≤ R)
    (hs : ∀ c ∈ s, ‖c‖ ≤ R) (h : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 ≤ ‖c-d‖) :
    (s.card : ℝ) ≤ (1+2*R)^finrank ℝ E := by
  classical
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := 1/2
  let ρ : ℝ := R+1/2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  let A := ⋃ c ∈ s, ball c δ
  have hd : Set.Pairwise (s : Set E) (fun c d => Disjoint (ball c δ) (ball d δ)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert h c hc d hd hcd using 1; norm_num [δ]
  have hA : A ⊆ ball (0:E) ρ := by
    refine iUnion₂_subset fun c hc => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    dsimp [δ,ρ]
    linarith [hs c hc]
  have hi : (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^finrank ℝ E)*μ (ball 0 1) ≤
      ENNReal.ofReal (ρ^finrank ℝ E)*μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [show A = ⋃ c ∈ s, ball c δ from rfl, measure_biUnion_finset hd (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ (show 0 < δ by norm_num [δ]), Finset.sum_const,
          nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0:E) ρ) := measure_mono hA
      _ = _ := μ.addHaar_ball_of_pos 0 hρ
  have hj : (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^finrank ℝ E) ≤ ENNReal.ofReal (ρ^finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne' measure_ball_lt_top.ne).mp hi
  have hr : (s.card : ℝ)*δ^finrank ℝ E ≤ ρ^finrank ℝ E := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal
      (pow_nonneg (by norm_num [δ] : 0 ≤ δ) (finrank ℝ E))] using ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hj
  have hr := (le_div_iff₀ (pow_pos (by norm_num [δ] : 0 < δ) (finrank ℝ E))).mpr hr
  rw [← div_pow] at hr
  have he : ρ/δ = 1+2*R := by dsimp [ρ,δ]; ring
  rwa [he] at hr

lemma packing_family_bound {E : Type uE} {I : Type uI} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype I] (f : I → E) (R : ℝ) (hR : 0 ≤ R)
    (hf : ∀ i, ‖f i‖ ≤ R) (hsep : ∀ i j, i ≠ j → 1 ≤ ‖f i-f j‖) :
    (Fintype.card I : ℝ) ≤ (1+2*R)^finrank ℝ E := by
  classical
  have hinj : Function.Injective f := by
    intro i j he
    by_contra h
    have := hsep i j h
    simp only [he, sub_self, norm_zero] at this
    linarith
  have hh := packing_card_bound (Finset.univ.image f) R hR
    (by simpa using hf) (by
      intro c hc d hd hcd
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hd
      exact hsep i j (fun he => hcd (congrArg f he)))
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ] using hh

lemma coordinateDistance_norm (p : ℝ) (hp : 0 < p) {d : ℕ} (x y : Fin d → ℝ) :
    coordinateDistance p x y =
      ‖WithLp.toLp (ENNReal.ofReal p) x - WithLp.toLp (ENNReal.ofReal p) y‖ := by
  rw [← WithLp.toLp_sub, PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp only [Pi.sub_apply, Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le]
  rfl

lemma GoodDimension.mono_distortion {p D D' : ℝ} {n d : ℕ}
    (h : GoodDimension.{u} p n D d) (hDD : D ≤ D') : GoodDimension.{u} p n D' d := by
  intro Ω mΩ μ x hx
  obtain ⟨y,s,hs,hy⟩ := h Ω mΩ μ x hx
  refine ⟨y,s,hs,fun i j => ⟨(hy i j).1, (hy i j).2.trans ?_⟩⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDD hs.le) (by rw [Lp.norm_def]; exact ENNReal.toReal_nonneg)

lemma quadratic_growth_log_limit (f : ℕ → ℕ)
    (hlo : ∀ᶠ n in atTop, ((n-1)/4)^2 ≤ f n)
    (hhi : ∀ᶠ n in atTop, f n ≤ n^2) :
    Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log (n:ℝ)) atTop (𝓝 2) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => 2 - (2*Real.log 8)/Real.log (n:ℝ)) atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.sub (hlog.const_div_atTop (2*Real.log 8))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [hlo, Filter.eventually_ge_atTop 9] with n hlo hn
    have hquad : (n:ℝ)^2 / 64 ≤ f n := by
      have hdiv : n ≤ 8*((n-1)/4) := by omega
      have hdivR : (n:ℝ) ≤ 8*((n-1)/4:ℕ) := by exact_mod_cast hdiv
      have hloR : (((n-1)/4:ℕ):ℝ)^2 ≤ f n := by exact_mod_cast hlo
      have hn0 : (0:ℝ) ≤ n := by positivity
      have hk0 : (0:ℝ) ≤ ((n-1)/4:ℕ) := by positivity
      nlinarith
    have hnpos : (0:ℝ) < n := by positivity
    have hn1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hqpos : 0 < (n:ℝ)^2/64 := by positivity
    have hb := Real.log_le_log hqpos hquad
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at hb
    have h64 : Real.log 64 = 2*Real.log 8 := by
      have := Real.log_pow (8:ℝ) 2
      norm_num at this
      exact this
    rw [h64] at hb
    apply (le_div_iff₀ (Real.log_pos hn1)).mpr
    rw [sub_mul, div_mul_cancel₀ _ (Real.log_pos hn1).ne']
    exact_mod_cast hb
  · filter_upwards [hlo, hhi, Filter.eventually_ge_atTop 9] with n hlo hhi hn
    have hfn : 0 < f n := by
      have hk : 0 < (n-1)/4 := by omega
      have := pow_pos hk 2
      omega
    have hfnR : (0:ℝ) < f n := by exact_mod_cast hfn
    have hb := Real.log_le_log hfnR (show (f n:ℝ) ≤ (n:ℝ)^2 by exact_mod_cast hhi)
    rw [Real.log_pow] at hb
    apply (div_le_iff₀ (Real.log_pos (show (1:ℝ) < n by exact_mod_cast (show 1 < n by omega)))).mpr
    exact hb

end SubpolynomialLp

end

end OAI
