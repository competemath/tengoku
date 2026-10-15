import Tengoku

/-!
# Bounded real multipliers on `Lp ℂ 2 μ` (`BoundedMultiplier`)

This file is a generic-measure-space extraction of the bounded-multiplier machinery
originally proved inside `LerayHopf.R3.WeightedFourierCommute` for the fixed space
`L2C_R3 = Lp ℂ 2 (volume : Measure Domain3)`.  None of the content below mentions `Fin 3`,
`Domain3`, or any dimension-specific fact — it is pure `L²` operator theory: multiplying
by a bounded real (a.e.-strongly-measurable) function `m` is a self-adjoint, `C`-Lipschitz
operator on `Lp ℂ 2 μ` that commutes with Bochner interval integration of continuous
`Lp ℂ 2 μ`-valued curves.

`WeightedFourierCommute.lean` keeps thin `Domain3`-instantiated wrappers under the
original names (`mulBdd`, `memLp_mulBdd`, …) so its many existing call sites in
`SobolevEmbedding.lean` and `AubinLionsLimitPassage.lean` are unaffected.
-/

open MeasureTheory

namespace LerayHopf.BoundedMultiplier

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- L²-norm-squared of a complex-scalar `L²` element as an integral of the pointwise squared
norm. (Generic Parseval-free core fact: no Fourier transform involved.) -/
private theorem normSq_eq_integral_normSq (g : Lp ℂ 2 μ) :
    ‖g‖ ^ 2 = ∫ x : X, ‖(g : X → ℂ) x‖ ^ 2 ∂μ := by
  have hre : ‖g‖ ^ 2 = RCLike.re (inner ℂ g g) := norm_sq_eq_re_inner (𝕜 := ℂ) g
  rw [hre, MeasureTheory.L2.inner_def, ← integral_re (MeasureTheory.L2.integrable_inner g g)]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- `mulBdd m hmem g` is the `L²`-class of `x ↦ (m x : ℂ) • g x`, for a bounded
a.e.-strongly-measurable real multiplier `m` (bound `C`).  Well-defined because the bounded
multiplier keeps `g ∈ L²` inside `L²` (Hölder `∞ · 2 ⊆ 2`).
@isnad1 id=memlp.1h4v.s9.96af50c23aa6 from=translated src=- shape=a4a8d5f5 vocab=a8912060
-/
theorem memLp_mulBdd (m : X → ℝ)
    (hmem : MemLp (fun x : X => (m x : ℂ)) ⊤ μ) (g : Lp ℂ 2 μ) :
    MemLp (fun x => (m x : ℂ) • (g : X → ℂ) x) 2 μ := by
  have h := (Lp.memLp g).smul hmem (p := ⊤) (q := 2) (r := 2)
  exact h

/-- The `L²` class of `x ↦ (m x : ℂ) • g x` for a bounded a.e.-strongly-measurable real
multiplier `m`, packaged as an `Lp ℂ 2 μ` element via `memLp_mulBdd`. -/
noncomputable def mulBdd (m : X → ℝ)
    (hmem : MemLp (fun x : X => (m x : ℂ)) ⊤ μ) (g : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (memLp_mulBdd μ m hmem g).toLp _

/-- The `Lp`-coercion of `mulBdd m g` agrees a.e. with the pointwise multiplier action
`x ↦ (m x : ℂ) • g x`.
@isnad1 id=eventual.1h4v.s9.418c7d03000d from=translated src=- shape=d0c3a59b vocab=fe1ae015
-/
theorem mulBdd_coeFn (m : X → ℝ)
    (hmem : MemLp (fun x : X => (m x : ℂ)) ⊤ μ) (g : Lp ℂ 2 μ) :
    (mulBdd μ m hmem g : X → ℂ) =ᵐ[μ] fun x => (m x : ℂ) • (g : X → ℂ) x :=
  MemLp.coeFn_toLp _

/-- **ℝ-homogeneity of the bounded multiplier.**
@isnad1 id=eq.1h5v.s12.06d9091b0018 from=translated src=- shape=202d291a vocab=743b7243
-/
theorem mulBdd_smul (m : X → ℝ)
    (hmem : MemLp (fun x : X => (m x : ℂ)) ⊤ μ) (r : ℝ) (g : Lp ℂ 2 μ) :
    mulBdd μ m hmem (r • g) = r • mulBdd μ m hmem g := by
  apply Lp.ext
  filter_upwards [mulBdd_coeFn μ m hmem (r • g), Lp.coeFn_smul r (mulBdd μ m hmem g),
    mulBdd_coeFn μ m hmem g, Lp.coeFn_smul r g] with x h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h4, h3, Pi.smul_apply]
  simp only [smul_eq_mul, Complex.real_smul]
  ring

/-- **Additivity of the bounded multiplier.**
@isnad1 id=eq.1h5v.s11.f95a3f16406b from=translated src=- shape=aa7eb4d9 vocab=2ddded6f
-/
theorem mulBdd_add (m : X → ℝ)
    (hmem : MemLp (fun x : X => (m x : ℂ)) ⊤ μ) (g h : Lp ℂ 2 μ) :
    mulBdd μ m hmem (g + h) = mulBdd μ m hmem g + mulBdd μ m hmem h := by
  apply Lp.ext
  filter_upwards [mulBdd_coeFn μ m hmem (g + h),
    Lp.coeFn_add (mulBdd μ m hmem g) (mulBdd μ m hmem h),
    mulBdd_coeFn μ m hmem g, mulBdd_coeFn μ m hmem h, Lp.coeFn_add g h] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, smul_add]

/-- **Squared `L²`-norm of `mulBdd m g` as the weighted integral** `∫ (m x)² ‖g x‖²`.
@isnad1 id=eq.1h4v.s9.34247aaf5083 from=translated src=- shape=e2ea7287 vocab=724d1d86
-/
theorem norm_mulBdd_sq (m : X → ℝ)
    (hmem : MemLp (fun x : X => (m x : ℂ)) ⊤ μ) (g : Lp ℂ 2 μ) :
    ‖mulBdd μ m hmem g‖ ^ 2 = ∫ x : X, (m x) ^ 2 * ‖(g : X → ℂ) x‖ ^ 2 ∂μ := by
  rw [normSq_eq_integral_normSq μ (mulBdd μ m hmem g)]
  refine integral_congr_ae ?_
  filter_upwards [mulBdd_coeFn μ m hmem g] with x hx
  rw [hx]
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Operator bound for the bounded multiplier:** `‖mulBdd m g‖ ≤ C ‖g‖` whenever `|m| ≤ C`
everywhere (the sup bound on `m` dominates the operator).
@isnad1 id=le.3h5v.s9.d5421e3eb174 from=translated src=- shape=d39d865e vocab=f81f32dc
-/
theorem norm_mulBdd_le (m : X → ℝ)
    (hmem : MemLp (fun x : X => (m x : ℂ)) ⊤ μ) {C : ℝ}
    (hC : 0 ≤ C) (hmle : ∀ x, |m x| ≤ C) (g : Lp ℂ 2 μ) :
    ‖mulBdd μ m hmem g‖ ≤ C * ‖g‖ := by
  have hsq : ‖mulBdd μ m hmem g‖ ^ 2 ≤ (C * ‖g‖) ^ 2 := by
    rw [norm_mulBdd_sq μ m hmem g, mul_pow, normSq_eq_integral_normSq μ g, ← integral_const_mul]
    have hgint : Integrable (fun x : X => ‖(g : X → ℂ) x‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
    refine integral_mono_of_nonneg ?_ (hgint.const_mul (C ^ 2)) ?_
    · filter_upwards with x; positivity
    · filter_upwards with x
      have hmsq : (m x) ^ 2 ≤ C ^ 2 := by
        rw [← sq_abs (m x)]; exact pow_le_pow_left₀ (abs_nonneg _) (hmle x) 2
      have hgnn : (0:ℝ) ≤ ‖(g : X → ℂ) x‖ ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_right hmsq hgnn
  have hrhs : 0 ≤ C * ‖g‖ := mul_nonneg hC (norm_nonneg _)
  nlinarith [norm_nonneg (mulBdd μ m hmem g), hsq, hrhs]

/-- **Subtractivity of the bounded multiplier.**
@isnad1 id=eq.1h5v.s11.4680e44fddda from=translated src=- shape=aa7eb4d9 vocab=064a41cc
-/
theorem mulBdd_sub (m : X → ℝ)
    (hmem : MemLp (fun x : X => (m x : ℂ)) ⊤ μ) (g h : Lp ℂ 2 μ) :
    mulBdd μ m hmem (g - h) = mulBdd μ m hmem g - mulBdd μ m hmem h := by
  apply Lp.ext
  filter_upwards [mulBdd_coeFn μ m hmem (g - h),
    Lp.coeFn_sub (mulBdd μ m hmem g) (mulBdd μ m hmem h),
    mulBdd_coeFn μ m hmem g, mulBdd_coeFn μ m hmem h, Lp.coeFn_sub g h] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, h3, h4, h5, Pi.sub_apply, smul_sub]

/-- **Continuity of the bounded multiplier operator** (it is `C`-Lipschitz).
@isnad1 id=continuo.3h4v.s11.e46182767576 from=translated src=- shape=7fd10359 vocab=591f2425
-/
theorem continuous_mulBdd (m : X → ℝ)
    (hmem : MemLp (fun x : X => (m x : ℂ)) ⊤ μ) {C : ℝ}
    (hC : 0 ≤ C) (hmle : ∀ x, |m x| ≤ C) :
    Continuous (fun g => mulBdd μ m hmem g) := by
  refine (LipschitzWith.of_dist_le_mul (K := C.toNNReal) ?_).continuous
  intro g h
  rw [dist_eq_norm, dist_eq_norm, ← mulBdd_sub μ m hmem g h, Real.coe_toNNReal C hC]
  exact norm_mulBdd_le μ m hmem hC hmle (g - h)

/-- **Self-adjointness of the bounded real multiplier.**  `⟪c, mulBdd m g⟫ = ⟪mulBdd m c, g⟫`.
@isnad1 id=eq.1h5v.s9.d576c1d2b1de from=translated src=- shape=34544ee0 vocab=635de4bc
-/
theorem inner_mulBdd_left (m : X → ℝ)
    (hmem : MemLp (fun x : X => (m x : ℂ)) ⊤ μ) (c g : Lp ℂ 2 μ) :
    (inner ℂ c (mulBdd μ m hmem g) : ℂ) = inner ℂ (mulBdd μ m hmem c) g := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulBdd_coeFn μ m hmem g, mulBdd_coeFn μ m hmem c] with x hg hc
  rw [hg, hc]
  simp only [RCLike.inner_apply, smul_eq_mul]
  rw [map_mul, Complex.conj_ofReal]
  ring

/-- **Bounded-multiplier Bochner commute (interval integral).**  For a curve `G` that is
interval-integrable on `[a,b]`, the bounded multiplier commutes with the Bochner integral:
`mulBdd m (∫_a^b G s ds) = ∫_a^b mulBdd m (G s) ds`.
@isnad1 id=eq.3h6v.s11.3cf7a0581744 from=translated src=- shape=6c95c09e vocab=1870ffa4
-/
theorem mulBdd_intervalIntegral_comm (m : X → ℝ)
    (hmem : MemLp (fun x : X => (m x : ℂ)) ⊤ μ)
    {G : ℝ → Lp ℂ 2 μ} {a b : ℝ}
    (hGint : IntervalIntegrable G volume a b)
    (hMGint : IntervalIntegrable (fun s => mulBdd μ m hmem (G s)) volume a b) :
    mulBdd μ m hmem (∫ s in a..b, G s) = ∫ s in a..b, mulBdd μ m hmem (G s) := by
  refine ext_inner_left ℂ (fun c => ?_)
  -- `inner ℂ c` as an ℝ-CLM, to pull through the ℝ-Bochner interval integral.
  have hpullR : ∀ {H : ℝ → Lp ℂ 2 μ} (hH : IntervalIntegrable H volume a b) (d : Lp ℂ 2 μ),
      (inner ℂ d (∫ s in a..b, H s) : ℂ) = ∫ s in a..b, (inner ℂ d (H s) : ℂ) := by
    intro H hH d
    exact (((innerSL ℂ d).restrictScalars ℝ).intervalIntegral_comp_comm hH).symm
  -- RHS pairing.
  rw [hpullR hMGint c]
  -- LHS pairing: self-adjointness, then pull through the other integral.
  rw [inner_mulBdd_left μ m hmem c, hpullR hGint (mulBdd μ m hmem c)]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  exact (inner_mulBdd_left μ m hmem c (G s)).symm

end LerayHopf.BoundedMultiplier
