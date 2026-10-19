/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Analysis.Calculus.SmoothSeries
import Tengoku.Seed.Analysis.Complex.Liouville
import Tengoku.LanaOka.Oka.Analytic.Laurent.L1
import Tengoku.LanaOka.Oka.Analytic.RiemannExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Holomorphic families of Laurent series

Let `h (z, w)` be holomorphic for `z` in an open subset `U` of a finite-dimensional complex space
and `w` near the two circles `‖w‖ = τ` and `‖w‖ = τ⁻¹`, with values in a finite-dimensional space
`V`. For `1 ≤ σ < τ` the Laurent coefficients of `w ↦ h (z, w)`, computed on these circles, define
an element of `Laurent.L1 V` (`Laurent.L1.toL1 σ τ`), and this element depends holomorphically on
`z` (`Laurent.L1.differentiableOn_toL1`). If `h (z, ·)` is holomorphic on an annulus containing
both circles, the Laurent series sums to `h (z, w)` on `σ⁻¹ ≤ ‖w‖ ≤ σ`
(`Laurent.L1.eval_toL1`).

## Main definitions

- `Laurent.circleCoeff f τ j`: the `j`-th Laurent coefficient of a vector-valued function `f`,
  computed on the circle of radius `τ`.
- `Laurent.L1.toL1 σ τ f`: the Laurent series of `f`, with the coefficients of nonnegative degree
  computed on `‖w‖ = τ` and those of negative degree on `‖w‖ = τ⁻¹`.

## Main results

- `Laurent.circleCoeff_eq_of_isRadius`: independence of the radius.
- `Laurent.differentiableOn_circleCoeff`: the coefficients depend holomorphically on parameters.
- `Laurent.norm_fderiv_le_of_forall_norm_le`: the Cauchy estimate for the derivative of a bounded
  holomorphic function on a ball in a normed space.
- `Laurent.L1.differentiableOn_toL1`: holomorphic dependence of `toL1` on parameters.
- `Laurent.L1.eval_toL1`: the Laurent expansion.
- `Laurent.L1.coeff_toL1_eq_zero_of_neg`, `Laurent.L1.coeff_toL1_eq_circleCoeff`,
  `Laurent.L1.eq_zero_of_toL1_eq_zero`: Laurent series of functions holomorphic on a disc.
- `Laurent.L1.circleCoeff_evalNat`: the Taylor coefficients of the part of nonnegative degree.
-/

open Set Filter Metric Complex
open scoped Real Topology ENNReal

namespace Laurent

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### Laurent coefficients of vector-valued functions -/

section CircleCoeff

/-- The `j`-th Laurent coefficient `(2πi)⁻¹ ∮_{‖ζ‖ = τ} ζ^{-j-1} f(ζ) dζ` of `f`, computed on the
circle of radius `τ`. -/
noncomputable def circleCoeff (f : ℂ → V) (τ : ℝ) (j : ℤ) : V :=
  (2 * π * I)⁻¹ • ∮ ζ in C(0, τ), ζ ^ (-j - 1) • f ζ

variable {f g : ℂ → V} {τ : ℝ}

lemma circleCoeff_congr (hτ : 0 ≤ τ) (h : EqOn f g (sphere 0 τ)) (j : ℤ) :
    circleCoeff f τ j = circleCoeff g τ j := by
  unfold circleCoeff
  congr 1
  exact circleIntegral.integral_congr hτ fun z hz ↦ by simp [h hz]

/-- The Cauchy estimate for Laurent coefficients. -/
theorem norm_circleCoeff_le (hτ : 0 < τ) {M : ℝ} (hM : ∀ z ∈ sphere (0 : ℂ) τ, ‖f z‖ ≤ M)
    (j : ℤ) : ‖circleCoeff f τ j‖ ≤ M * τ ^ (-j) := by
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun z ↦ z ^ (-j - 1) • f z) (c := 0) hτ.le (C := τ ^ (-j - 1) * M) fun z hz ↦ by
      rw [mem_sphere_zero_iff_norm] at hz
      rw [norm_smul, norm_zpow, hz]
      exact mul_le_mul_of_nonneg_left (hM z (by simpa using hz)) (zpow_nonneg hτ.le _)
  refine h.trans (le_of_eq ?_)
  rw [zpow_sub_one₀ hτ.ne']
  field_simp

lemma continuousOn_zpow_smul (hτ : 0 < τ) (hf : ContinuousOn f (sphere 0 τ)) (j : ℤ) :
    ContinuousOn (fun ζ ↦ ζ ^ (-j - 1) • f ζ) (sphere 0 τ) :=
  (continuousOn_id.zpow₀ _ fun _ hz ↦ Or.inl (ne_zero_of_mem_sphere_zero hτ hz)).smul hf

variable [CompleteSpace V]

/-- Continuous linear functionals commute with Laurent coefficients. -/
lemma map_circleCoeff (ℓ : V →L[ℂ] ℂ) (hτ : 0 < τ) (hf : ContinuousOn f (sphere 0 τ)) (j : ℤ) :
    ℓ (circleCoeff f τ j) = coeff (fun ζ ↦ ℓ (f ζ)) τ j := by
  have hint : CircleIntegrable (fun ζ ↦ ζ ^ (-j - 1) • f ζ) 0 τ :=
    (continuousOn_zpow_smul hτ hf j).circleIntegrable hτ.le
  rw [circleCoeff, coeff, map_smul, smul_eq_mul, circleIntegral, circleIntegral,
    ← ℓ.intervalIntegral_comp_comm hint.out]
  simp [map_smul, smul_eq_mul]

/-- The Laurent coefficients do not depend on the radius of the circle. -/
theorem circleCoeff_eq_of_isRadius {r : ℝ} {R : ℝ≥0∞} (hf : DifferentiableOn ℂ f (annulus r R))
    {ρ₁ ρ₂ : ℝ} (h₁ : IsRadius r R ρ₁) (h₂ : IsRadius r R ρ₂) (j : ℤ) :
    circleCoeff f ρ₁ j = circleCoeff f ρ₂ j := by
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ ↦ ?_
  rw [map_circleCoeff ℓ h₁.pos (hf.continuousOn.mono (sphere_subset_annulus h₁)),
    map_circleCoeff ℓ h₂.pos (hf.continuousOn.mono (sphere_subset_annulus h₂))]
  exact coeff_eq_of_isRadius (ℓ.differentiable.comp_differentiableOn hf) h₁ h₂ j

/-- On a disc the Laurent coefficients of negative degree vanish. -/
theorem circleCoeff_eq_zero_of_neg {r : ℝ} {R : ℝ≥0∞} (hf : DifferentiableOn ℂ f (annulus r R))
    (hr : r < 0) (hρ : IsRadius r R τ) {j : ℤ} (hj : j < 0) : circleCoeff f τ j = 0 := by
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ ↦ ?_
  rw [map_circleCoeff ℓ hρ.pos (hf.continuousOn.mono (sphere_subset_annulus hρ)), map_zero]
  exact coeff_eq_zero_of_neg (ℓ.differentiable.comp_differentiableOn hf) hr hρ hj

end CircleCoeff

/-! ### Holomorphic dependence on parameters -/

section Parametric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Cauchy's estimate** for the derivative of a bounded holomorphic function on a ball. -/
theorem norm_fderiv_le_of_forall_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {c : E → F} {z₀ : E} {δ M : ℝ} (hδ : 0 < δ) (hc : DifferentiableOn ℂ c (ball z₀ (2 * δ)))
    (hM : ∀ z ∈ ball z₀ (2 * δ), ‖c z‖ ≤ M) {z : E} (hz : z ∈ ball z₀ δ) :
    ‖fderiv ℂ c z‖ ≤ M / δ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z₀ (mem_ball_self (by linarith)))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hδ.le) fun v ↦ ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  set r := δ / ‖v‖ with hr_def
  have hr : 0 < r := div_pos hδ hv'
  have hmem : ∀ t : ℂ, ‖t‖ ≤ r → z + t • v ∈ ball z₀ (2 * δ) := by
    intro t ht
    rw [mem_ball] at hz ⊢
    have htv : ‖t • v‖ ≤ δ := by
      rw [norm_smul]
      calc ‖t‖ * ‖v‖ ≤ r * ‖v‖ := by gcongr
        _ = δ := div_mul_cancel₀ δ hv'.ne'
    calc dist (z + t • v) z₀ ≤ dist z z₀ + ‖t • v‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]
          exact norm_add_le _ _
      _ < 2 * δ := by linarith
  have hline : ∀ t : ℂ, HasDerivAt (fun t : ℂ ↦ z + t • v) v t := fun t ↦ by
    simpa using ((hasDerivAt_id t).smul_const v).const_add z
  have hdiff : ∀ t : ℂ, ‖t‖ ≤ r → DifferentiableAt ℂ (fun t : ℂ ↦ c (z + t • v)) t := fun t ht ↦
    (hc.differentiableAt (isOpen_ball.mem_nhds (hmem t ht))).comp t (hline t).differentiableAt
  have hd : DiffContOnCl ℂ (fun t : ℂ ↦ c (z + t • v)) (ball 0 r) := by
    refine DifferentiableOn.diffContOnCl fun t ht ↦ (hdiff t ?_).differentiableWithinAt
    rw [closure_ball _ hr.ne'] at ht
    simpa using ht
  have hderiv : deriv (fun t : ℂ ↦ c (z + t • v)) 0 = fderiv ℂ c z v := by
    have hc' : HasFDerivAt c (fderiv ℂ c z) (z + (0 : ℂ) • v) := by
      rw [zero_smul, add_zero]
      exact (hc.differentiableAt (isOpen_ball.mem_nhds (by simpa using hmem 0 (by simp [hr.le])))
        ).hasFDerivAt
    exact (hc'.comp_hasDerivAt (0 : ℂ) (hline 0)).deriv
  have h := norm_deriv_le_of_forall_mem_sphere_norm_le hr hd fun t ht ↦
    hM _ (hmem t (le_of_eq (mem_sphere_zero_iff_norm.1 ht)))
  rw [hderiv] at h
  refine h.trans (le_of_eq ?_)
  rw [hr_def]
  field_simp

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ V]

/-- The Laurent coefficients of a holomorphic family of functions depend holomorphically on the
parameter. -/
theorem differentiableOn_circleCoeff {U : Set E} (hU : IsOpen U) {O : Set ℂ} {τ : ℝ} (hτ : 0 < τ)
    (hO : sphere (0 : ℂ) τ ⊆ O) {h : E × ℂ → V} (hh : DifferentiableOn ℂ h (U ×ˢ O)) (j : ℤ) :
    DifferentiableOn ℂ (fun z ↦ circleCoeff (fun ζ ↦ h (z, ζ)) τ j) U := by
  set e := (Module.finBasis ℂ V).equivFunL
  have hmaps : ∀ ζ ∈ sphere (0 : ℂ) τ, MapsTo (fun z : E ↦ (z, ζ)) U (U ×ˢ O) :=
    fun ζ hζ z hz ↦ ⟨hz, hO hζ⟩
  have hcont : ∀ z ∈ U, ContinuousOn (fun ζ ↦ h (z, ζ)) (sphere 0 τ) := fun z hz ↦
    hh.continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun ζ hζ ↦ ⟨hz, hO hζ⟩
  have key : ∀ i, DifferentiableOn ℂ (fun z ↦ e (circleCoeff (fun ζ ↦ h (z, ζ)) τ j) i) U := by
    intro i
    set ℓ : V →L[ℂ] ℂ := (ContinuousLinearMap.proj i).comp (e : V →L[ℂ] (_ → ℂ))
    have heq : EqOn (fun z ↦ e (circleCoeff (fun ζ ↦ h (z, ζ)) τ j) i)
        (fun z ↦ coeff (fun ζ ↦ ℓ (h (z, ζ))) τ j) U := fun z hz ↦
      map_circleCoeff ℓ hτ (hcont z hz) j
    refine DifferentiableOn.congr ?_ heq
    unfold coeff
    refine (differentiableOn_circleIntegral hU hτ (fun ζ hζ ↦ ?_) ?_).const_mul _
    · exact (ℓ.differentiable.comp_differentiableOn (hh.comp
        ((differentiable_id.prodMk (differentiable_const ζ)).differentiableOn)
        (hmaps ζ hζ))).const_mul _
    · refine ContinuousOn.mul ?_ ?_
      · exact (continuousOn_snd.zpow₀ _ fun p hp ↦
          Or.inl (ne_zero_of_mem_sphere_zero hτ hp.2))
      · exact ℓ.continuous.comp_continuousOn (hh.continuousOn.mono
          (prod_mono subset_rfl hO))
  have hd : DifferentiableOn ℂ (fun z ↦ e (circleCoeff (fun ζ ↦ h (z, ζ)) τ j)) U :=
    differentiableOn_pi.2 key
  have := (e.symm : (_ → ℂ) →L[ℂ] V).differentiable.comp_differentiableOn hd
  simpa [Function.comp_def] using this

end Parametric
lemma annulus_neg_one_ofReal (R : ℝ) : annulus (-1) (ENNReal.ofReal R) = ball 0 R := by
  ext z
  rw [mem_annulus, enorm_lt_iff_ofReal_lt, mem_ball_zero_iff, ENNReal.ofReal_lt_ofReal_iff']
  constructor
  · exact fun h ↦ h.2.1
  · exact fun h ↦ ⟨by linarith [norm_nonneg z], h, (norm_nonneg z).trans_lt h⟩

/-! ### Laurent series of holomorphic families in `ℓ¹` -/

namespace L1

variable {σ τ : ℝ} [hσ : Fact (1 ≤ σ)]

/-- The Laurent coefficients of `f`: those of nonnegative degree computed on the circle
`‖ζ‖ = τ`, those of negative degree on `‖ζ‖ = τ⁻¹`. -/
noncomputable def radCoeff (τ : ℝ) (f : ℂ → V) (j : ℤ) : V :=
  circleCoeff f (if 0 ≤ j then τ else τ⁻¹) j

lemma wt_mul_norm_radCoeff_le (hστ : σ < τ) {f : ℂ → V} {M : ℝ}
    (hM : ∀ ζ ∈ sphere (0 : ℂ) τ ∪ sphere 0 τ⁻¹, ‖f ζ‖ ≤ M) (j : ℤ) :
    wt σ j * ‖radCoeff τ f j‖ ≤ M * (σ / τ) ^ j.natAbs := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  have hτ : 0 < τ := h0.trans hστ
  rcases le_or_gt 0 j with hj | hj
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    have h := norm_circleCoeff_le hτ (fun z hz ↦ hM z (Or.inl hz)) (n : ℤ)
    rw [radCoeff, ite_eq_left hj, wt_natCast, Int.natAbs_natCast, div_pow]
    calc σ ^ n * ‖circleCoeff f τ n‖ ≤ σ ^ n * (M * τ ^ (-(n : ℤ))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = M * (σ ^ n / τ ^ n) := by rw [zpow_neg, zpow_natCast]; field_simp
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -n := ⟨j.natAbs, by omega⟩
    have h := norm_circleCoeff_le (inv_pos.2 hτ) (fun z hz ↦ hM z (Or.inr hz)) (-(n : ℤ))
    rw [radCoeff, ite_eq_right (by omega), wt_neg, wt_natCast, Int.natAbs_neg, Int.natAbs_natCast,
      div_pow]
    calc σ ^ n * ‖circleCoeff f τ⁻¹ (-n)‖ ≤ σ ^ n * (M * τ⁻¹ ^ (-(-(n : ℤ)))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = M * (σ ^ n / τ ^ n) := by rw [neg_neg, zpow_natCast, inv_pow]; field_simp

lemma summable_wt_mul_norm_radCoeff (hστ : σ < τ) {f : ℂ → V} {M : ℝ}
    (hM : ∀ ζ ∈ sphere (0 : ℂ) τ ∪ sphere 0 τ⁻¹, ‖f ζ‖ ≤ M) :
    Summable fun j ↦ wt σ j * ‖radCoeff τ f j‖ := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  have hτ : 0 < τ := h0.trans hστ
  exact Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (wt_pos h0 j).le (norm_nonneg _))
    (wt_mul_norm_radCoeff_le hστ hM)
    ((summable_pow_natAbs (div_nonneg h0.le hτ.le) ((div_lt_one hτ).2 hστ)).mul_left M)

open Classical in
variable (σ) in
/-- The Laurent series of `f` as an element of `ℓ¹`: its coefficients of nonnegative degree are
computed on the circle `‖ζ‖ = τ` and those of negative degree on `‖ζ‖ = τ⁻¹` (and it is `0` if the
weighted coefficients are not summable). -/
noncomputable def toL1 (τ : ℝ) (f : ℂ → V) : L1 V :=
  if h : Summable fun j ↦ wt σ j * ‖radCoeff τ f j‖ then
    ofCoeff (zero_lt_one.trans_le hσ.out) (radCoeff τ f) h
  else 0

variable {f : ℂ → V}

lemma coeff_toL1 (hστ : σ < τ) {M : ℝ} (hM : ∀ ζ ∈ sphere (0 : ℂ) τ ∪ sphere 0 τ⁻¹, ‖f ζ‖ ≤ M)
    (j : ℤ) : coeff σ (toL1 σ τ f) j = radCoeff τ f j := by
  rw [toL1, dite_eq_left (summable_wt_mul_norm_radCoeff hστ hM), coeff_ofCoeff]

lemma toL1_apply (hστ : σ < τ) {M : ℝ} (hM : ∀ ζ ∈ sphere (0 : ℂ) τ ∪ sphere 0 τ⁻¹, ‖f ζ‖ ≤ M)
    (j : ℤ) : toL1 σ τ f j = (wt σ j : ℂ) • radCoeff τ f j := by
  rw [toL1, dite_eq_left (summable_wt_mul_norm_radCoeff hστ hM)]
  rfl

lemma norm_toL1_apply_le (hστ : σ < τ) {M : ℝ}
    (hM : ∀ ζ ∈ sphere (0 : ℂ) τ ∪ sphere 0 τ⁻¹, ‖f ζ‖ ≤ M) (j : ℤ) :
    ‖toL1 σ τ f j‖ ≤ M * (σ / τ) ^ j.natAbs := by
  rw [toL1_apply hστ hM, norm_smul, norm_real,
    Real.norm_of_nonneg (wt_pos (zero_lt_one.trans_le hσ.out) j).le]
  exact wt_mul_norm_radCoeff_le hστ hM j

omit [NormedSpace ℂ V] in
lemma exists_bound_of_continuousOn (hf : ContinuousOn f (sphere (0 : ℂ) τ ∪ sphere 0 τ⁻¹)) :
    ∃ M, ∀ ζ ∈ sphere (0 : ℂ) τ ∪ sphere 0 τ⁻¹, ‖f ζ‖ ≤ M :=
  ((isCompact_sphere _ _).union (isCompact_sphere _ _)).exists_bound_of_continuousOn hf

/-- The Laurent series of a holomorphic family of functions depends holomorphically on the
parameter. -/
theorem differentiableOn_toL1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ V] (hστ : σ < τ) {U : Set E} (hU : IsOpen U)
    {O : Set ℂ} (hO : sphere (0 : ℂ) τ ∪ sphere 0 τ⁻¹ ⊆ O) {h : E × ℂ → V}
    (hh : DifferentiableOn ℂ h (U ×ˢ O)) :
    DifferentiableOn ℂ (fun z ↦ toL1 σ τ fun w ↦ h (z, w)) U := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  have hτ : 0 < τ := h0.trans hστ
  intro z₀ hz₀
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  set δ := ε / 4 with hδ_def
  have hδ : 0 < δ := by positivity
  have hsub : closedBall z₀ (2 * δ) ⊆ U :=
    (closedBall_subset_ball (by simp only [hδ_def]; linarith)).trans hεU
  set C := sphere (0 : ℂ) τ ∪ sphere 0 τ⁻¹
  have hK : IsCompact (closedBall z₀ (2 * δ) ×ˢ C) :=
    (isCompact_closedBall _ _).prod ((isCompact_sphere _ _).union (isCompact_sphere _ _))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hh.continuousOn.mono (prod_mono hsub hO))
  have hMz : ∀ z ∈ closedBall z₀ (2 * δ), ∀ ζ ∈ C, ‖h (z, ζ)‖ ≤ M :=
    fun z hz ζ hζ ↦ hM (z, ζ) ⟨hz, hζ⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMz z₀ (mem_closedBall_self (by positivity)) τ
    (Or.inl (by simp [abs_of_pos hτ])))
  set q := σ / τ
  have hq : Summable fun j : ℤ ↦ M * q ^ j.natAbs / δ :=
    ((summable_pow_natAbs (div_nonneg h0.le hτ.le) ((div_lt_one hτ).2 hστ)).mul_left M).div_const δ
  set c : ℤ → E → V := fun j z ↦ (wt σ j : ℂ) • radCoeff τ (fun w ↦ h (z, w)) j
  have hc : ∀ j, DifferentiableOn ℂ (c j) U := by
    intro j
    refine DifferentiableOn.const_smul ?_ _
    unfold radCoeff
    split_ifs
    · exact differentiableOn_circleCoeff hU hτ (subset_union_left.trans hO) hh j
    · exact differentiableOn_circleCoeff hU (inv_pos.2 hτ) (subset_union_right.trans hO) hh j
  have hcb : ∀ j, ∀ z ∈ closedBall z₀ (2 * δ), ‖c j z‖ ≤ M * q ^ j.natAbs := by
    intro j z hz
    rw [norm_smul, norm_real, Real.norm_of_nonneg (wt_pos h0 j).le]
    exact wt_mul_norm_radCoeff_le hστ (fun ζ hζ ↦ hMz z hz ζ hζ) j
  set S := lp.singleContinuousLinearMap ℂ (fun _ : ℤ ↦ V) 1
  have hS : ∀ j, ‖S j‖ ≤ 1 := fun j ↦
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
      simp [S, lp.norm_single (zero_lt_one' ℝ≥0∞)]
  have hball : ball z₀ δ ⊆ closedBall z₀ (2 * δ) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hderiv : ∀ j, ∀ z ∈ ball z₀ δ,
      HasFDerivAt (fun y ↦ S j (c j y)) ((S j).comp (fderiv ℂ (c j) z)) z := fun j z hz ↦
    (S j).hasFDerivAt.comp z
      ((hc j).differentiableAt (hU.mem_nhds (hsub (hball hz)))).hasFDerivAt
  have hbound : ∀ j, ∀ z ∈ ball z₀ δ, ‖(S j).comp (fderiv ℂ (c j) z)‖ ≤ M * q ^ j.natAbs / δ := by
    intro j z hz
    have h' := norm_fderiv_le_of_forall_norm_le hδ
      ((hc j).mono (ball_subset_closedBall.trans hsub))
      (fun y hy ↦ hcb j y (ball_subset_closedBall hy)) hz
    calc ‖(S j).comp (fderiv ℂ (c j) z)‖ ≤ ‖S j‖ * ‖fderiv ℂ (c j) z‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (M * q ^ j.natAbs / δ) := mul_le_mul (hS j) h' (norm_nonneg _) zero_le_one
      _ = M * q ^ j.natAbs / δ := one_mul _
  have hsum : ∀ z ∈ closedBall z₀ (2 * δ),
      HasSum (fun j ↦ S j (c j z)) (toL1 σ τ fun w ↦ h (z, w)) := fun z hz ↦ by
    have := lp.hasSum_single (E := fun _ : ℤ ↦ V) (p := 1) ENNReal.one_ne_top
      (toL1 σ τ fun w ↦ h (z, w))
    convert this using 2 with j
    rw [toL1_apply hστ (fun ζ hζ ↦ hMz z hz ζ hζ)]
    rfl
  have key := hasFDerivAt_tsum_of_isPreconnected hq isOpen_ball (convex_ball z₀ δ).isPreconnected
    hderiv hbound (mem_ball_self hδ) (hsum z₀ (mem_closedBall_self (by positivity))).summable
    (mem_ball_self hδ)
  refine (key.differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with y hy
  exact (hsum y (hball hy)).tsum_eq.symm

variable [CompleteSpace V]

/-- **Laurent expansion**: if `f` is holomorphic on an annulus containing the circles
`‖ζ‖ = τ` and `‖ζ‖ = τ⁻¹`, then its Laurent series sums to `f` on `σ⁻¹ ≤ ‖w‖ ≤ σ`. -/
theorem eval_toL1 (hστ : σ < τ) {r : ℝ} {R : ℝ≥0∞} (hf : DifferentiableOn ℂ f (annulus r R))
    (h₁ : IsRadius r R τ) (h₂ : IsRadius r R τ⁻¹) {w : ℂ} (hw₁ : σ⁻¹ ≤ ‖w‖) (hw₂ : ‖w‖ ≤ σ) :
    eval σ w (toL1 σ τ f) = f w := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  have hτ : 0 < τ := h0.trans hστ
  obtain ⟨M, hM⟩ := exists_bound_of_continuousOn (τ := τ) (f := f)
    (hf.continuousOn.mono (union_subset (sphere_subset_annulus h₁) (sphere_subset_annulus h₂)))
  have hwA : w ∈ annulus r R :=
    mem_annulus_of_le h₂ h₁ ((inv_anti₀ h0 hστ.le).trans hw₁) (hw₂.trans hστ.le)
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ ↦ ?_
  have e : (fun j ↦ ℓ (w ^ j • coeff σ (toL1 σ τ f) j)) =
      fun j ↦ Laurent.coeff (⇑ℓ ∘ f) τ j * w ^ j := by
    funext j
    rw [coeff_toL1 hστ hM, map_smul, smul_eq_mul, radCoeff, mul_comm]
    congr 1
    split_ifs
    · exact map_circleCoeff ℓ hτ (hf.continuousOn.mono (sphere_subset_annulus h₁)) j
    · rw [map_circleCoeff ℓ (inv_pos.2 hτ) (hf.continuousOn.mono (sphere_subset_annulus h₂)) j]
      exact coeff_eq_of_isRadius (ℓ.differentiable.comp_differentiableOn hf) h₂ h₁ j
  have hA := (hasSum_eval hw₁ hw₂ (toL1 σ τ f)).mapL ℓ
  rw [e] at hA
  exact hA.unique (hasSum_coeff (ℓ.differentiable.comp_differentiableOn hf) h₁ hwA)

/-- The Laurent series of a function holomorphic on a disc has no terms of negative degree. -/
lemma coeff_toL1_eq_zero_of_neg (hστ : σ < τ) {R : ℝ} (hτR : τ < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) {j : ℤ} (hj : j < 0) : coeff σ (toL1 σ τ f) j = 0 := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  have hτ : 1 < τ := hσ.out.trans_lt hστ
  have hf' : DifferentiableOn ℂ f (annulus (-1) (ENNReal.ofReal R)) := by
    rwa [annulus_neg_one_ofReal]
  have hR : IsRadius (-1) (ENNReal.ofReal R) τ⁻¹ :=
    ⟨inv_pos.2 (zero_lt_one.trans hτ), by linarith [inv_pos.2 (zero_lt_one.trans hτ)],
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 ((inv_lt_one_of_one_lt₀ hτ).trans
        (hτ.trans hτR))⟩
  have hR' : IsRadius (-1) (ENNReal.ofReal R) τ :=
    ⟨by linarith, by linarith, (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hτR⟩
  obtain ⟨M, hM⟩ := exists_bound_of_continuousOn (τ := τ) (f := f)
    (hf'.continuousOn.mono (union_subset (sphere_subset_annulus hR') (sphere_subset_annulus hR)))
  rw [coeff_toL1 hστ hM, radCoeff, ite_eq_right (by omega)]
  exact circleCoeff_eq_zero_of_neg hf' (by norm_num) hR hj

/-- The coefficients of nonnegative degree of the Laurent series of a function holomorphic on a
disc are its Taylor coefficients, computed on any circle in the disc. -/
lemma coeff_toL1_eq_circleCoeff (hστ : σ < τ) {R : ℝ} (hτR : τ < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) {r : ℝ} (hr : 0 < r) (hrR : r < R) {j : ℤ}
    (hj : 0 ≤ j) : coeff σ (toL1 σ τ f) j = circleCoeff f r j := by
  have hτ : 1 < τ := hσ.out.trans_lt hστ
  have hf' : DifferentiableOn ℂ f (annulus (-1) (ENNReal.ofReal R)) := by
    rwa [annulus_neg_one_ofReal]
  have hR : IsRadius (-1) (ENNReal.ofReal R) τ⁻¹ :=
    ⟨inv_pos.2 (zero_lt_one.trans hτ), by linarith [inv_pos.2 (zero_lt_one.trans hτ)],
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 ((inv_lt_one_of_one_lt₀ hτ).trans
        (hτ.trans hτR))⟩
  have hR' : IsRadius (-1) (ENNReal.ofReal R) τ :=
    ⟨by linarith, by linarith, (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hτR⟩
  have hr' : IsRadius (-1) (ENNReal.ofReal R) r :=
    ⟨hr, by linarith, (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hrR⟩
  obtain ⟨M, hM⟩ := exists_bound_of_continuousOn (τ := τ) (f := f)
    (hf'.continuousOn.mono (union_subset (sphere_subset_annulus hR') (sphere_subset_annulus hR)))
  rw [coeff_toL1 hστ hM, radCoeff, ite_eq_left hj]
  exact circleCoeff_eq_of_isRadius hf' hR' hr' j

/-- The Taylor coefficients of the part of nonnegative degree. -/
lemma circleCoeff_evalNat {r : ℝ} (hr : 0 < r) (hrσ : r < σ) (a : L1 V) {j : ℤ} (hj : 0 ≤ j) :
    circleCoeff (fun w ↦ evalNat V σ w a) r j = coeff σ a j := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  have hcont : ContinuousOn (fun w ↦ evalNat V σ w a) (sphere 0 r) :=
    ((differentiableOn_evalNat.clm_apply (differentiableOn_const a)).continuousOn).mono
      fun z hz ↦ by rw [mem_ball_zero_iff, (mem_sphere_zero_iff_norm.1 hz)]; exact hrσ
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ ↦ ?_
  rw [map_circleCoeff ℓ hr hcont]
  set b : ℤ → ℂ := fun k ↦ if 0 ≤ k then ℓ (coeff σ a k) else 0
  have hb : Summable fun k ↦ ‖b k‖ * r ^ k := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ ?_)
      ((summable_norm a).mul_left ‖ℓ‖)
    simp only [b]
    split_ifs with hk
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      rw [zpow_natCast]
      calc ‖ℓ (coeff σ a n)‖ * r ^ n ≤ ‖ℓ‖ * ‖coeff σ a n‖ * σ ^ n :=
            mul_le_mul (ℓ.le_opNorm _) (pow_le_pow_left₀ hr.le hrσ.le n) (by positivity)
              (by positivity)
        _ = ‖ℓ‖ * ‖a n‖ := by rw [norm_apply_eq h0 a n, wt_natCast]; ring
    · simp only [norm_zero, zero_mul]
      positivity
  have hsum : ∀ z ∈ sphere (0 : ℂ) r,
      HasSum (fun k ↦ b k * z ^ k) ((fun w ↦ ℓ (evalNat V σ w a)) z) := by
    intro z hz
    have hz' : ‖z‖ < σ := by rw [mem_sphere_zero_iff_norm.1 hz]; exact hrσ
    rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff fun k hk ↦ ?_]
    · have e : ((fun k ↦ b k * z ^ k) ∘ (Nat.cast : ℕ → ℤ)) =
          fun n : ℕ ↦ ℓ (z ^ n • coeff σ a n) := by
        funext n
        simp [b, mul_comm]
      rw [e]
      exact (hasSum_evalNat_apply hz' a).mapL ℓ
    · simp only [b]
      rw [ite_eq_right (fun h ↦ hk ⟨k.toNat, Int.toNat_of_nonneg h⟩), zero_mul]
  rw [coeff_eq_of_hasSum hr hb hsum j]
  simp [b, hj]
/-- A function holomorphic on a disc whose Laurent series vanishes is zero. -/
lemma eq_zero_of_toL1_eq_zero (hστ : σ < τ) {R : ℝ} (hτR : τ < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (h0 : toL1 σ τ f = 0) {w : ℂ} (hw : w ∈ ball 0 R) :
    f w = 0 := by
  have hτ : 1 < τ := hσ.out.trans_lt hστ
  have hf' : DifferentiableOn ℂ f (annulus (-1) (ENNReal.ofReal R)) := by
    rwa [annulus_neg_one_ofReal]
  have hR' : IsRadius (-1) (ENNReal.ofReal R) τ :=
    ⟨by linarith, by linarith, (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hτR⟩
  have hR : IsRadius (-1) (ENNReal.ofReal R) τ⁻¹ :=
    ⟨inv_pos.2 (zero_lt_one.trans hτ), by linarith [inv_pos.2 (zero_lt_one.trans hτ)],
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 ((inv_lt_one_of_one_lt₀ hτ).trans
        (hτ.trans hτR))⟩
  obtain ⟨M, hM⟩ := exists_bound_of_continuousOn (τ := τ) (f := f)
    (hf'.continuousOn.mono (union_subset (sphere_subset_annulus hR') (sphere_subset_annulus hR)))
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ ↦ ?_
  have hwA : w ∈ annulus (-1) (ENNReal.ofReal R) := by rwa [annulus_neg_one_ofReal]
  have hs := hasSum_coeff (ℓ.differentiable.comp_differentiableOn hf') hR' hwA
  have hzero : ∀ k : ℤ, Laurent.coeff (⇑ℓ ∘ f) τ k * w ^ k = 0 := by
    intro k
    rcases lt_or_ge k 0 with hk | hk
    · rw [coeff_eq_zero_of_neg (ℓ.differentiable.comp_differentiableOn hf') (by norm_num) hR' hk,
        zero_mul]
    · have hc := coeff_toL1 (σ := σ) hστ hM k
      rw [h0, coeff_zero, radCoeff, ite_eq_left hk] at hc
      have := map_circleCoeff ℓ (zero_lt_one.trans hτ)
        (hf'.continuousOn.mono (sphere_subset_annulus hR')) k
      rw [← hc, map_zero] at this
      rw [show (⇑ℓ ∘ f) = fun ζ ↦ ℓ (f ζ) from rfl, ← this, zero_mul]
  simp only [hzero] at hs
  have := hs.unique hasSum_zero
  simpa using this

end L1

end Laurent
